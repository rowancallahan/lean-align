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

@[inline] def setU32 (B : ByteArray) (i v : Nat) : ByteArray :=
  let j := 4 * i
  let v := v.toUInt32
  ((((B.set! j v.toUInt8).set! (j + 1) (v >>> 8).toUInt8).set! (j + 2) (v >>> 16).toUInt8).set!
    (j + 3) (v >>> 24).toUInt8)

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut B := ByteArray.emptyWithCapacity n
  for _ in [0:n] do B := B.push 0
  return B

structure CsrIndex where
  l0 : Nat
  /-- global coordinate of each chromosome's first letter -/
  starts : Array Nat
  /-- `4^l0 + 1` LE `UInt32` bucket offsets -/
  offs : ByteArray
  /-- LE `UInt32` global coordinates -/
  pos : ByteArray

/-- Largest `c` in `lo ..< hi` with `starts[c] ≤ x` (binary search, fuel-bounded). -/
def locateAux (starts : Array Nat) (x : Nat) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if starts[mid]! ≤ x then locateAux starts x fuel mid hi else locateAux starts x fuel lo mid

/-- Global coordinate ↦ (chromosome, start). -/
def locate (starts : Array Nat) (x : Nat) : Nat × Nat :=
  let c := locateAux starts x 64 0 starts.size
  (c, x - starts[c]!)

namespace CsrIndex

@[inline] def lo (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs h
@[inline] def hi (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs (h + 1)

/-- The place stored at entry `t`. -/
@[inline] def entry (idx : CsrIndex) (t : Nat) : Nat × Nat := locate idx.starts (getU32 idx.pos t)

/-- Every place in the word's bucket.  (A mapper can instead walk the entries
`idx.lo h ..< idx.hi h` with `h = byteWordCode read q l0`; see `mem_lookup`.) -/
def lookup (idx : CsrIndex) (word : List Char) : List (Nat × Nat) :=
  let h := codeOfWord word
  (List.range' (idx.lo h) (idx.hi h - idx.lo h)).map idx.entry

end CsrIndex

/-! ### Builder (fast; not trusted — `checkIndex` certifies its output) -/

def chromStarts (gb : ByteGenome) : Array Nat := Id.run do
  let mut s : Array Nat := Array.emptyWithCapacity gb.size
  let mut x := 0
  for bc in gb do
    s := s.push x
    x := x + bc.bytes.size
  return s

def buildCsr (l0 : Nat) (gb : ByteGenome) : CsrIndex := Id.run do
  let M := 4 ^ l0
  let starts := chromStarts gb
  -- counts in slot h+1
  let mut offs := zeroBytes (4 * (M + 1))
  let mut total := 0
  for bc in gb do
    let B := bc.bytes
    if l0 ≤ B.size then
      let mut h := initCode B l0
      for p in [0:B.size + 1 - l0] do
        if p > 0 then h := (h * 4 + byteCode (B.get! (p - 1 + l0))) % M
        offs := setU32 offs (h + 1) (getU32 offs (h + 1) + 1)
        total := total + 1
  for h in [0:M] do
    offs := setU32 offs (h + 1) (getU32 offs (h + 1) + getU32 offs h)
  let mut fill := offs
  let mut pos := zeroBytes (4 * total)
  for c in [0:gb.size] do
    let B := gb[c]!.bytes
    if l0 ≤ B.size then
      let mut h := initCode B l0
      for p in [0:B.size + 1 - l0] do
        if p > 0 then h := (h * 4 + byteCode (B.get! (p - 1 + l0))) % M
        let t := getU32 fill h
        pos := setU32 pos t (starts[c]! + p)
        fill := setU32 fill h (t + 1)
  return { l0, starts, offs, pos }

/-! ### Checker -/

/-- Place `(c, p)`, whose word has code `h`, is the entry `inv[p]` of bucket `h`. -/
@[inline] def checkAt (idx : CsrIndex) (c : Nat) (inv : ByteArray) (p h : Nat) : Bool :=
  let t := getU32 inv p
  decide (idx.lo h ≤ t) && decide (t < idx.hi h) && decide (idx.entry t = (c, p))

/-- `checkAt` at places `p .. p+k` of one chromosome, rolling the code `h`. -/
def verifyRun (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (M : Nat) : (k p h : Nat) → Bool
  | 0, p, h => checkAt idx c inv p h
  | k + 1, p, h =>
    checkAt idx c inv p h &&
      verifyRun idx c B inv M k (p + 1) ((h * 4 + byteCode (B.get! (p + idx.l0))) % M)

def verifyChrom (idx : CsrIndex) (c : Nat) (B inv : ByteArray) : Bool :=
  if idx.l0 ≤ B.size then verifyRun idx c B inv (4 ^ idx.l0) (B.size - idx.l0) 0 (initCode B idx.l0)
  else true

/-- Checks every place of the genome against inverse positions `invs`
(`invs[c]` holds, as LE `UInt32`s, the entry of each place of chromosome `c`). -/
def verifyIndex (idx : CsrIndex) (gb : ByteGenome) (invs : Array ByteArray) : Bool :=
  decide (0 < idx.l0) && (List.range gb.size).all fun c => verifyChrom idx c gb[c]!.bytes invs[c]!

/-- Inverse positions from the index itself (not trusted). -/
def inversePositions (idx : CsrIndex) (gb : ByteGenome) : Array ByteArray := Id.run do
  let mut invs : Array ByteArray := gb.map fun bc => zeroBytes (4 * bc.bytes.size)
  for t in [0:idx.pos.size / 4] do
    let (c, p) := idx.entry t
    invs := invs.modify c fun inv => setU32 inv p t
  return invs

def checkIndex (idx : CsrIndex) (gb : ByteGenome) : Bool :=
  verifyIndex idx gb (inversePositions idx gb)

/-! ## The theorems

    checkIndex idx gb = true →
      LookupComplete (decodeGenome gb) idx.l0 idx.lookup                     (checkIndex_complete)
    checkIndex idx gb = true → c < gb.size → p + idx.l0 ≤ gb[c].bytes.size →
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),
      h = byteWordCode gb[c].bytes p idx.l0                                  (checkIndex_bucket)
    (c, p) ∈ idx.lookup word ↔
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),  h = codeOfWord word   (mem_lookup)

for every index `idx` (however built or loaded) and byte genome `gb`.  The
genome they are about is `decodeGenome gb`; for an ASCII genome `g`,
`decodeGenome (encodeGenome g) = g` (`decodeGenome_encodeGenome`). -/

/-! ## Proof -/

namespace CsrIndex

/-- Place `(c, p)` is an entry of bucket `h`. -/
def InBucket (idx : CsrIndex) (h c p : Nat) : Prop :=
  ∃ t, idx.lo h ≤ t ∧ t < idx.hi h ∧ idx.entry t = (c, p)

theorem mem_lookup (idx : CsrIndex) (word : List Char) (c p : Nat) :
    (c, p) ∈ idx.lookup word ↔ idx.InBucket (codeOfWord word) c p := by
  simp only [lookup, InBucket, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩; exact ⟨t, h1, by omega, h3⟩
  · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, ⟨h1, by omega⟩, h3⟩

end CsrIndex

theorem checkAt_spec (idx : CsrIndex) (c : Nat) (inv : ByteArray) (p h : Nat)
    (hc : checkAt idx c inv p h = true) : idx.InBucket h c p := by
  simp only [checkAt, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨_, hc.1.1, hc.1.2, hc.2⟩

theorem verifyRun_spec (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (M : Nat)
    (hM : M = 4 ^ idx.l0) (hl : 0 < idx.l0) :
    ∀ k p h, verifyRun idx c B inv M k p h = true → p + k + idx.l0 ≤ B.size →
      h = codeOfWord (wordAt (decodeBytes B) idx.l0 p) →
      ∀ q, p ≤ q → q ≤ p + k → idx.InBucket (codeOfWord (wordAt (decodeBytes B) idx.l0 q)) c q := by
  intro k
  induction k with
  | zero =>
    intro p h hv _ hh q h1 h2
    rw [show q = p by omega, ← hh]; exact checkAt_spec idx c inv p h hv
  | succ k ih =>
    intro p h hv hsz hh q h1 h2
    simp only [verifyRun, Bool.and_eq_true] at hv
    by_cases hq : q = p
    · subst hq; rw [← hh]; exact checkAt_spec idx c inv q h hv.1
    · apply ih (p + 1) _ hv.2 (by omega) _ q (by omega) (by omega)
      have hlen : p + idx.l0 < (decodeBytes B).length := by rw [length_decodeBytes]; omega
      rw [codeOfWord_wordAt_succ _ _ _ hl hlen, hh, hM, getElem_decodeBytes, charCode_toChar]

theorem verifyChrom_spec (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (hl : 0 < idx.l0)
    (hv : verifyChrom idx c B inv = true) (p : Nat) (hp : p + idx.l0 ≤ B.size) :
    idx.InBucket (codeOfWord (wordAt (decodeBytes B) idx.l0 p)) c p := by
  unfold verifyChrom at hv
  rw [if_pos (by omega)] at hv
  exact verifyRun_spec idx c B inv _ rfl hl _ 0 _ hv (by omega) (initCode_eq B idx.l0 (by omega)) p
    (by omega) (by omega)

/-- **Bucket form.**  Every place of the genome is an entry of the bucket of
its word's code, the code computed from the bytes. -/
theorem verifyIndex_bucket (idx : CsrIndex) (gb : ByteGenome) (invs : Array ByteArray)
    (hv : verifyIndex idx gb invs = true) (c : Nat) (hc : c < gb.size) (p : Nat)
    (hp : p + idx.l0 ≤ gb[c].bytes.size) :
    idx.InBucket (byteWordCode gb[c].bytes p idx.l0) c p := by
  simp only [verifyIndex, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hv
  have h := verifyChrom_spec idx c _ _ hv.1 (hv.2 c hc) p (by rw [getElem!_pos gb c hc]; exact hp)
  rw [getElem!_pos gb c hc] at h
  rw [byteWordCode_eq _ _ _ hp]
  exact h

theorem verifyIndex_complete (idx : CsrIndex) (gb : ByteGenome) (invs : Array ByteArray)
    (hv : verifyIndex idx gb invs = true) :
    LookupComplete (decodeGenome gb) idx.l0 idx.lookup := by
  intro c chromosome p hch hp
  rw [getElem?_decodeGenome] at hch
  split at hch
  · next hc =>
    cases hch
    rw [CsrIndex.mem_lookup]
    have hp' : p + idx.l0 ≤ gb[c].bytes.size := by rw [← length_decodeBytes]; exact hp
    have := verifyIndex_bucket idx gb invs hv c hc p hp'
    rwa [byteWordCode_eq _ _ _ hp'] at this
  · cases hch

/-- **Completeness.**  An index that passes the checker reports every place
every word of the genome occurs. -/
theorem checkIndex_complete (idx : CsrIndex) (gb : ByteGenome) (hc : checkIndex idx gb = true) :
    LookupComplete (decodeGenome gb) idx.l0 idx.lookup :=
  verifyIndex_complete idx gb _ hc

theorem checkIndex_bucket (idx : CsrIndex) (gb : ByteGenome) (hchk : checkIndex idx gb = true)
    (c : Nat) (hc : c < gb.size) (p : Nat) (hp : p + idx.l0 ≤ gb[c].bytes.size) :
    idx.InBucket (byteWordCode gb[c].bytes p idx.l0) c p :=
  verifyIndex_bucket idx gb _ hchk c hc p hp

end MapSpec

#print axioms MapSpec.checkIndex_complete
#print axioms MapSpec.checkIndex_bucket
#print axioms MapSpec.CsrIndex.mem_lookup
#print axioms MapSpec.decodeGenome_encodeGenome
#print axioms MapSpec.windowSeq_decodeGenome
#print axioms MapSpec.byteWordCode_eq
