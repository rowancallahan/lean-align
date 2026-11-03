import SeedMapper                 -- `LookupComplete`
import MapperBytes                -- pool: byte genome and word codes

/-!
# Codec `CsrIndex`: compact k-mer index with a certified completeness checker

The genome is one `ByteArray` per chromosome (`ByteGenome`).  The index is
CSR over the 2-bit codes of `l0`-letter words (`codeOfWord`: A0 C1 G2 T3,
anything else 0; collisions are allowed):

* `offs` — `4^l0 + 1` little-endian `UInt32`s; bucket `h` is the entry range
  `offs[h] ..< offs[h+1]`;
* `pos` — one little-endian `UInt32` per entry: a global coordinate
  `starts[c] + p`, turned back into `(c, p)` by `locate`.

Nothing about how the index is built or stored is trusted.  `checkIndex idx gb`
looks at every place `(c, p)` of the genome and checks that bucket
`code(word at (c, p))` holds an entry equal to `(c, p)`; the theorem
`checkIndex_complete` turns `checkIndex idx gb = true` into
`LookupComplete (decodeGenome gb) idx.l0 idx.lookup`, which is all the mapper
needs (`mapWith_eq_mapSpec`).  So the index may come from the fast builder
below, from disk, or from anywhere.
-/

namespace MapSpec

/-! ## The algorithm -/

/-- Little-endian `UInt32` number `i` of a byte array. -/
@[inline] def getU32 (B : ByteArray) (i : Nat) : Nat :=
  let j := 4 * i
  ((B.get! j).toUInt32 ||| ((B.get! (j + 1)).toUInt32 <<< 8) |||
    ((B.get! (j + 2)).toUInt32 <<< 16) ||| ((B.get! (j + 3)).toUInt32 <<< 24)).toNat

/-! ### `getU32` on machine words (compiled code only): `getU32_eqF` -/

theorem uget_get32 (w : ByteArray) (i : USize) (h : i.toNat < w.size) : w.uget i h = w.get! i.toNat := by
  cases w with
  | mk bs =>
    simp only [ByteArray.uget, ByteArray.get!]
    simp only [ByteArray.size] at h
    rw [getElem!_pos bs i.toNat h]
    rfl

theorem u32_idx (i : Nat) (k : Nat) (hi : i < 2 ^ 29) (hk : k < 4) :
    ((4 * i).toUSize + k.toUSize).toNat = 4 * i + k := by
  have hs : 2 ^ 32 ≤ USize.size := USize.le_size
  have hN : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, Nat.toUSize_eq, Nat.toUSize_eq, USize.toNat_ofNat', USize.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : 4 * i < USize.size), Nat.mod_eq_of_lt (by omega : k < USize.size),
    Nat.mod_eq_of_lt (by omega)]

/-- `getU32` with one bounds test and machine-word indices (`getU32_eqF`). -/
@[inline] def getU32F (B : ByteArray) (i : Nat) : Nat :=
  if h : i < 536870912 ∧ 4 * i + 4 ≤ B.size then
    let j := (4 * i).toUSize
    ((B.uget (j + (0 : Nat).toUSize) (by rw [u32_idx i 0 h.1 (by decide)]; omega)).toUInt32 |||
      ((B.uget (j + (1 : Nat).toUSize) (by rw [u32_idx i 1 h.1 (by decide)]; omega)).toUInt32 <<< 8) |||
      ((B.uget (j + (2 : Nat).toUSize) (by rw [u32_idx i 2 h.1 (by decide)]; omega)).toUInt32 <<< 16) |||
      ((B.uget (j + (3 : Nat).toUSize) (by rw [u32_idx i 3 h.1 (by decide)]; omega)).toUInt32 <<< 24)).toNat
  else getU32S B i
where
  /-- The same as `getU32` (its slow path; not rewritten by `csimp`). -/
  getU32S (B : ByteArray) (i : Nat) : Nat :=
    let j := 4 * i
    ((B.get! j).toUInt32 ||| ((B.get! (j + 1)).toUInt32 <<< 8) |||
      ((B.get! (j + 2)).toUInt32 <<< 16) ||| ((B.get! (j + 3)).toUInt32 <<< 24)).toNat

/-- Compiled code runs `getU32F`. -/
@[csimp] theorem getU32_eqF : @getU32 = @getU32F := by
  funext B i
  unfold getU32F getU32F.getU32S getU32
  split
  · rename_i h
    simp only [uget_get32, u32_idx i 0 h.1 (by decide), u32_idx i 1 h.1 (by decide), u32_idx i 2 h.1 (by decide),
      u32_idx i 3 h.1 (by decide), Nat.add_zero]
  · rfl

@[inline] def setU32 (B : ByteArray) (i v : Nat) : ByteArray :=
  let j := 4 * i
  let v := v.toUInt32
  ((((B.set! j v.toUInt8).set! (j + 1) (v >>> 8).toUInt8).set! (j + 2) (v >>> 16).toUInt8).set!
    (j + 3) (v >>> 24).toUInt8)

structure CsrIndex where
  /-- `4^l0 + 1` LE `UInt32` bucket offsets -/
  offs : ByteArray
deriving Inhabited

namespace CsrIndex

@[inline] def lo (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs h
@[inline] def hi (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs (h + 1)

end CsrIndex

/-! ### Builder (fast; not trusted — `checkIndex` certifies its output) -/

/-! ### Checker -/

/-! ## The theorems

    checkIndex idx gb = true →
      LookupComplete (decodeGenome gb) idx.l0 idx.lookup                     (checkIndex_complete)
    checkIndex idx gb = true → c < gb.size → p + idx.l0 ≤ gb[c].bytes.size →
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),
      h = byteWordCode gb[c].bytes p idx.l0                                  (checkIndex_bucket)
    (c, p) ∈ idx.lookup word ↔
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),  h = codeOfWord word   (mem_lookup)

    checkIndex idx gb = true →
      mapWithCsr sc T gb idx read = mapSpec sc T (decodeGenome gb) read      (mapWithCsr_eq_mapSpec)

for every index `idx` (however built or loaded), byte genome `gb`, read,
threshold `T` and scoring with `ValidScoring sc`.  The
genome they are about is `decodeGenome gb`; for an ASCII genome `g`,
`decodeGenome (encodeGenome g) = g` (`decodeGenome_encodeGenome`). -/

/-! ## Proof -/

namespace CsrIndex

end CsrIndex

end MapSpec

#print axioms MapSpec.decodeGenome_encodeGenome
#print axioms MapSpec.windowSeq_decodeGenome
#print axioms MapSpec.byteWordCode_eq
