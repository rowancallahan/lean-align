import MapperPGen
import MapperPacked
import MapperGenScore

/-!
# Word kernels for short reads (≤ 256 letters) over the packed genome

The read is packed once (`packRP`: 32 letters per `UInt64`, A0 C1 G2 T3, letter
`i` in bits `2·(i % 32)` of word `i / 32`).  The genome is a `PGen` (64-letter
blocks: a flag byte, then 16 code bytes); the aligned word `u` (absolute letters
`[32u, 32u + 32)`) is 8 consecutive code bytes (`gword`).  A window whose blocks are
all flagged (pure ACGT) is compared 32 letters at a time: XOR, fold each 2-bit
field to its low bit (`fold`), SWAR count (`cnt64`), lowest/highest set field by
`cnt64 (m ^^^ (m - 1))` / `cnt64 (smear m)`.  Anything else (non-ACGT read or
blocks, read longer than 256, a window off the chromosome) takes the byte loops.

Kernels, each equal to the byte version under `Rep P G` (`P` spells `G`):
`hamK` (= `hamming`), `fwdK` (= `fwdMis`), `bwdK` (= `bwdMis`),
`gappedK` (= `gappedPen2`), `kerGK` (= `kerG`).
-/

namespace MapSpec.Fast

open MapSpec

/-! ## Algorithm -/

/-- Packed read: words, and whether the word path applies (`≤ 256` letters, all ACGT). -/
structure RP where
  w : Array UInt64
  ok : Bool
deriving Inhabited

/-- Pack `R[i ..]`: `w` is the word being filled (next field at bit `sh`), `acc` the
full words, `ok` all ACGT so far. -/
def packLoop (R : ByteArray) (i : Nat) (sh : UInt64) (w : UInt64) (acc : Array UInt64) (ok : Bool) : RP :=
  if i < R.size then
    let t := codeTab.get! (R.get! i).toNat
    let w := w ||| (t &&& 3).toUInt64 <<< sh
    if sh == 62 then packLoop R (i + 1) 0 0 (acc.push w) (ok && decide (t < 4))
    else packLoop R (i + 1) (sh + 2) w acc (ok && decide (t < 4))
  else ⟨acc.push w, ok⟩
termination_by R.size - i

def packRP (R : ByteArray) : RP :=
  if R.size ≤ 256 then packLoop R 0 0 0 (Array.emptyWithCapacity 9) true else ⟨#[], false⟩

/-- Aligned genome word `u` of the blocks `w`. -/
@[inline] def gword (w : ByteArray) (u : Nat) : UInt64 :=
  let b := 17 * (u / 2) + 1 + 8 * (u % 2)
  (w.get! b).toUInt64 ||| (w.get! (b + 1)).toUInt64 <<< 8 ||| (w.get! (b + 2)).toUInt64 <<< 16 |||
  (w.get! (b + 3)).toUInt64 <<< 24 ||| (w.get! (b + 4)).toUInt64 <<< 32 ||| (w.get! (b + 5)).toUInt64 <<< 40 |||
  (w.get! (b + 6)).toUInt64 <<< 48 ||| (w.get! (b + 7)).toUInt64 <<< 56

theorem usz_toNat (b k : Nat) (h : b + k < USize.size) : (b.toUSize + k.toUSize).toNat = b + k := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [hs] at h
  rw [USize.toNat_add, Nat.toUSize_eq, Nat.toUSize_eq, USize.toNat_ofNat', USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show b < 2 ^ System.Platform.numBits by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ System.Platform.numBits by omega), Nat.mod_eq_of_lt h]

/-- A round trip through `USize` that keeps `b + 8` bounds it below `USize.size` (a
small-number test, unlike comparing with the big constant `USize.size`). -/
theorem usz_lt (b : Nat) (h : (b.toUSize + (8 : Nat).toUSize).toNat = b + 8) : b + 8 < USize.size :=
  h ▸ USize.toNat_lt_size _

/-- `gword` with machine-word indices and one bounds check (`gword_eq_gwordF`, used by
the compiler in place of `gword`). -/
@[inline] def gwordF (w : ByteArray) (u : Nat) : UInt64 :=
  let b := 17 * (u / 2) + 1 + 8 * (u % 2)
  if h : b + 8 ≤ w.size ∧ (b.toUSize + (8 : Nat).toUSize).toNat = b + 8 then
    let i := b.toUSize
    (w.uget (i + (0 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 |||
    (w.uget (i + (1 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 8 |||
    (w.uget (i + (2 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 16 |||
    (w.uget (i + (3 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 24 |||
    (w.uget (i + (4 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 32 |||
    (w.uget (i + (5 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 40 |||
    (w.uget (i + (6 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 48 |||
    (w.uget (i + (7 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 56
  else gwordS w u
where
  /-- The same as `gword` (its slow path; not rewritten by `csimp`). -/
  gwordS (w : ByteArray) (u : Nat) : UInt64 :=
    let b := 17 * (u / 2) + 1 + 8 * (u % 2)
    (w.get! b).toUInt64 ||| (w.get! (b + 1)).toUInt64 <<< 8 ||| (w.get! (b + 2)).toUInt64 <<< 16 |||
    (w.get! (b + 3)).toUInt64 <<< 24 ||| (w.get! (b + 4)).toUInt64 <<< 32 ||| (w.get! (b + 5)).toUInt64 <<< 40 |||
    (w.get! (b + 6)).toUInt64 <<< 48 ||| (w.get! (b + 7)).toUInt64 <<< 56

theorem uget_get! (w : ByteArray) (i : USize) (h : i.toNat < w.size) : w.uget i h = w.get! i.toNat := by
  cases w with
  | mk bs =>
    simp only [ByteArray.uget, ByteArray.get!]
    simp only [ByteArray.size] at h
    rw [getElem!_pos bs i.toNat h]
    rfl

theorem usz_succ (i n : USize) (h : i.toNat < n.toNat) : (i + 1).toNat = i.toNat + 1 := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  have := USize.toNat_lt_size n
  rw [USize.toNat_add, USize.toNat_one, ← hs, Nat.mod_eq_of_lt (by omega)]

theorem usz_small (m : Nat) (h : m ≤ 256) : m.toUSize.toNat = m := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  have : 2 ^ 32 ≤ USize.size := by
    rw [hs]; exact Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> omega)
  rw [Nat.toUSize_eq, USize.toNat_ofNat', ← hs, Nat.mod_eq_of_lt (by omega)]

/-- `packLoop` on a machine-word index `i` below `n` (`n` the read length; `packLoopU_eq`). -/
def packLoopU (R : ByteArray) (n : USize) (hn : n.toNat = R.size) (i : USize) (sh w : UInt64)
    (acc : Array UInt64) (ok : Bool) : RP :=
  if h : i < n then
    let t := codeTab.get! (R.uget i (by rw [← hn]; exact h)).toNat
    let w := w ||| (t &&& 3).toUInt64 <<< sh
    if sh == 62 then packLoopU R n hn (i + 1) 0 0 (acc.push w) (ok && decide (t < 4))
    else packLoopU R n hn (i + 1) (sh + 2) w acc (ok && decide (t < 4))
  else ⟨acc.push w, ok⟩
termination_by n.toNat - i.toNat
decreasing_by
  all_goals
    have h1 : i.toNat < n.toNat := h
    rw [usz_succ i n h1]; omega

theorem packLoopU_eq (R : ByteArray) (n : USize) (hn : n.toNat = R.size) :
    ∀ k (i : USize) sh w acc ok, R.size - i.toNat = k →
      packLoopU R n hn i sh w acc ok = packLoop R i.toNat sh w acc ok := by
  intro k
  induction k with
  | zero =>
    intro i sh w acc ok hk
    have h' : ¬ i < n := by
      intro h; have : i.toNat < n.toNat := h; omega
    have h'' : ¬ i.toNat < R.size := by omega
    rw [packLoopU, packLoop, dif_neg h', if_neg h'']
  | succ k ih =>
    intro i sh w acc ok hk
    have hlt : i.toNat < R.size := by omega
    have h' : i < n := by show i.toNat < n.toNat; omega
    have h2 : (i + 1).toNat = i.toNat + 1 := usz_succ i n (by omega)
    rw [packLoopU, packLoop, dif_pos h', if_pos hlt, uget_get!]
    simp only []
    split
    · rw [ih (i + 1) _ _ _ _ (by omega), h2]
    · rw [ih (i + 1) _ _ _ _ (by omega), h2]

/-- `packRP` on machine-word indices (`packRP_eqU`). -/
def packRPU (R : ByteArray) : RP :=
  if h : R.size ≤ 256 then packLoopU R R.size.toUSize (usz_small _ h) 0 0 0 (Array.emptyWithCapacity 9) true
  else ⟨#[], false⟩

/-- Compiled code runs `packRPU`. -/
@[csimp] theorem packRP_eqU : @packRP = @packRPU := by
  funext R
  unfold packRP packRPU
  split
  · next h => rw [packLoopU_eq R _ _ _ 0 _ _ _ _ rfl]; rfl
  · rfl

@[csimp] theorem gword_eq_gwordF : @gword = @gwordF := by
  funext w u
  unfold gwordF gwordF.gwordS gword
  simp only []
  split
  · rename_i h
    have e : ∀ k, k < 9 → ((17 * (u / 2) + 1 + 8 * (u % 2)).toUSize + k.toUSize).toNat =
        17 * (u / 2) + 1 + 8 * (u % 2) + k := fun k hk =>
      usz_toNat _ _ (by have := usz_lt _ h.2; omega)
    rw [uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!,
      e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega)]
    rfl
  · rfl

/-- Each 2-bit field folded to its low bit. -/
@[inline] def fold (x : UInt64) : UInt64 := (x ||| x >>> 1) &&& 0x5555555555555555

/-- Fields `[0, c)` kept (`c ≥ 32`: all). -/
@[inline] def lowF (x : UInt64) (c : Nat) : UInt64 :=
  if c < 32 then x &&& ((1 <<< (2 * c).toUInt64) - 1) else x

/-- Fields `[c, 32)` kept. -/
@[inline] def highF (x : UInt64) (c : Nat) : UInt64 :=
  if c = 0 then x else if c < 32 then x &&& ~~~((1 <<< (2 * c).toUInt64) - 1) else 0

/-- Index of the lowest set field (`m ≠ 0`, folded). -/
@[inline] def lowIdx (m : UInt64) : Nat := Packed.cnt64 (m ^^^ (m - 1)) - 1

/-- Index of the highest set field (`m ≠ 0`, folded). -/
@[inline] def highIdx (m : UInt64) : Nat :=
  let m := m ||| m >>> 1
  let m := m ||| m >>> 2
  let m := m ||| m >>> 4
  let m := m ||| m >>> 8
  let m := m ||| m >>> 16
  let m := m ||| m >>> 32
  Packed.cnt64 m - 1

/-- Index of the `k+1`-th lowest set field. -/
def selLow (m : UInt64) : Nat → Nat
  | 0 => lowIdx m
  | k + 1 => selLow (m &&& (m - 1)) k

/-- Index of the `k+1`-th highest set field. -/
def selHigh (m : UInt64) : Nat → Nat
  | 0 => highIdx m
  | k + 1 => selHigh (m ^^^ (1 <<< (2 * highIdx m).toUInt64)) k

/-- Genome letters of read chunk `j`: the aligned words `cur`, `nxt` shifted by `s`
fields (`sh = 2s`, `sh' = 64 − 2s`). -/
@[inline] def comb (cur nxt : UInt64) (s : Nat) (sh sh' : UInt64) : UInt64 :=
  if s = 0 then cur else (cur >>> sh) ||| (nxt <<< sh')

/-- Mismatches of `R[32j, stop)` against the genome added to `acc`, stopping once
above `lim`; the genome at read letter `x` is absolute letter `32·u0 + s + x`, `cur`
is the aligned word `u0 + j`. -/
def hamW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat)
    (j acc : Nat) (cur : UInt64) : Nat :=
  if 32 * j < stop then
    let nxt := gword gw (u0 + j + 1)
    let acc := acc + Packed.cnt64 (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j))
    if lim < acc then lim + 1 else hamW rw gw u0 s sh sh' lim stop (j + 1) acc nxt
  else acc
termination_by stop - 32 * j

/-! ### `hamW` on machine words (compiled code only)

`hamW_eq_hamWF` (`@[csimp]`): the compiled `hamW` is `hamWF`, a `USize` loop (`hamWU`) with
the read word fetched by `Array.uget` (`rwAt`), the genome word's byte offset in `USize`
(`gwordU`) and the count kept as `UInt64` until the end (`cnt64U`).  Statements about
`hamW` are unchanged. -/

theorem usz_n (n : Nat) (h : n < 2 ^ 32) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)]

theorem usz_pow : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size

theorem usz_add' (a b : USize) (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by have := usz_pow; omega)]

theorem usz_mul' (a b : USize) (h : a.toNat * b.toNat < 2 ^ 32) : (a * b).toNat = a.toNat * b.toNat := by
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by have := usz_pow; omega)]

theorem usz_lit (n : Nat) (h : n < 2 ^ 32) : (OfNat.ofNat n : USize).toNat = n := by
  show (USize.ofNat n).toNat = n
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by have := usz_pow; omega)]

theorem usz_shr5 (a : USize) : (a >>> 5).toNat = a.toNat / 32 := by
  rw [USize.toNat_shiftRight, usz_lit 5 (by decide), Nat.mod_eq_of_lt (by cases System.Platform.numBits_eq <;> simp_all),
    Nat.shiftRight_eq_div_pow]

theorem usize_le (a : ByteArray) : a.usize.toNat ≤ a.size := by
  show a.size.toUSize.toNat ≤ a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

theorem ausize_le (a : Array UInt64) : a.usize.toNat ≤ a.size := by
  show a.size.toUSize.toNat ≤ a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

/-- `rw[j]!` with a machine-word index (the `else` branch is unreachable at run time). -/
@[inline] def rwAt (rw : Array UInt64) (j : USize) : UInt64 :=
  if h : j < rw.usize then rw.uget j (Nat.lt_of_lt_of_le h (ausize_le rw)) else rw[j.toNat]!

theorem rwAt_eq (rw : Array UInt64) (j : USize) : rwAt rw j = rw[j.toNat]! := by
  unfold rwAt
  split
  · rename_i h
    rw [getElem!_pos rw j.toNat (Nat.lt_of_lt_of_le h (ausize_le rw))]; rfl
  · rfl

/-- `B.get! p.toNat` with one machine-word bounds check (the `else` branch is unreachable at run time). -/
@[inline] def getU (B : ByteArray) (p : USize) : UInt8 :=
  if h : p < B.usize then B.uget p (Nat.lt_of_lt_of_le h (usize_le B)) else B.get! p.toNat

theorem getU_eq (B : ByteArray) (p : USize) : getU B p = B.get! p.toNat := by
  unfold getU; split
  · rename_i h; exact uget_get! B p _
  · rfl

theorem usz_nowrap (b : USize) (h1 : b < b + (8 : Nat).toUSize) :
    (b + (8 : Nat).toUSize).toNat = b.toNat + 8 := by
  have hb : b.toNat < 2 ^ System.Platform.numBits := USize.toNat_lt_size b
  have h1' : b.toNat < (b + (8 : Nat).toUSize).toNat := h1
  rw [USize.toNat_add, usz_n 8 (by decide)] at h1' ⊢
  have hN := usz_pow
  generalize 2 ^ System.Platform.numBits = N at hb h1' hN ⊢
  by_cases hc : b.toNat + 8 < N
  · exact Nat.mod_eq_of_lt hc
  · exfalso
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1'
    omega

theorem uget_ok (w : ByteArray) (b : USize) (h1 : b < b + (8 : Nat).toUSize)
    (h2 : b + (8 : Nat).toUSize ≤ w.usize) (k : Nat) (hk : k < 8) : (b + k.toUSize).toNat < w.size := by
  have e := usz_nowrap b h1
  have h2' : (b + (8 : Nat).toUSize).toNat ≤ w.usize.toNat := h2
  have := usize_le w
  have hb : b.toNat < 2 ^ System.Platform.numBits := USize.toNat_lt_size b
  rw [USize.toNat_add, usz_n k (by omega)]
  have hN := usz_pow
  have hw : w.usize.toNat < 2 ^ System.Platform.numBits := USize.toNat_lt_size _
  generalize 2 ^ System.Platform.numBits = N at hb hN hw ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `gword` on a machine-word index: byte offset in `USize`, one bounds check
(`gwordU_eq`); the `else` branch is unreachable for genomes below 2^33 letters. -/
@[inline] def gwordU (w : ByteArray) (u : USize) : UInt64 :=
  let b := (17 : USize) * (u >>> (1 : USize)) + 1 + 8 * (u &&& (1 : USize))
  if h : b < b + (8 : Nat).toUSize ∧ b + (8 : Nat).toUSize ≤ w.usize then
    (w.uget (b + (0 : Nat).toUSize) (uget_ok w b h.1 h.2 0 (by decide))).toUInt64 |||
    (w.uget (b + (1 : Nat).toUSize) (uget_ok w b h.1 h.2 1 (by decide))).toUInt64 <<< 8 |||
    (w.uget (b + (2 : Nat).toUSize) (uget_ok w b h.1 h.2 2 (by decide))).toUInt64 <<< 16 |||
    (w.uget (b + (3 : Nat).toUSize) (uget_ok w b h.1 h.2 3 (by decide))).toUInt64 <<< 24 |||
    (w.uget (b + (4 : Nat).toUSize) (uget_ok w b h.1 h.2 4 (by decide))).toUInt64 <<< 32 |||
    (w.uget (b + (5 : Nat).toUSize) (uget_ok w b h.1 h.2 5 (by decide))).toUInt64 <<< 40 |||
    (w.uget (b + (6 : Nat).toUSize) (uget_ok w b h.1 h.2 6 (by decide))).toUInt64 <<< 48 |||
    (w.uget (b + (7 : Nat).toUSize) (uget_ok w b h.1 h.2 7 (by decide))).toUInt64 <<< 56
  else gwordF.gwordS w u.toNat

theorem usz_and1 (u : USize) : (u &&& (1 : USize)).toNat = u.toNat % 2 := by
  rw [USize.toNat_and, usz_lit 1 (by decide), Nat.and_one_is_mod]

theorem usz_shr1 (u : USize) : (u >>> (1 : USize)).toNat = u.toNat / 2 := by
  rw [USize.toNat_shiftRight, usz_lit 1 (by decide), Nat.mod_eq_of_lt (by cases System.Platform.numBits_eq <;> simp_all),
    Nat.shiftRight_eq_div_pow]

/-- The byte offset of word `u` computed in `USize` is the `Nat` one (`u < 2^28 + 2^16`). -/
theorem gwordU_off (u : USize) (hu : u.toNat < 2 ^ 28 + 2 ^ 16) :
    ((17 : USize) * (u >>> (1 : USize)) + 1 + 8 * (u &&& (1 : USize))).toNat = 17 * (u.toNat / 2) + 1 + 8 * (u.toNat % 2) := by
  have h2 : u.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have e1 : ((17 : USize) * (u >>> (1 : USize))).toNat = 17 * (u.toNat / 2) := by
    rw [usz_mul' _ _ (by rw [usz_lit 17 (by decide), usz_shr1]; omega), usz_lit 17 (by decide), usz_shr1]
  have e2 : ((8 : USize) * (u &&& (1 : USize))).toNat = 8 * (u.toNat % 2) := by
    rw [usz_mul' _ _ (by rw [usz_lit 8 (by decide), usz_and1]; omega), usz_lit 8 (by decide), usz_and1]
  have e3 : ((17 : USize) * (u >>> (1 : USize)) + 1).toNat = 17 * (u.toNat / 2) + 1 := by
    rw [usz_add' _ _ (by rw [e1, usz_lit 1 (by decide)]; omega), e1, usz_lit 1 (by decide)]
  rw [usz_add' _ _ (by rw [e3, e2]; omega), e3, e2]

theorem gwordU_eq (w : ByteArray) (u : USize) (hu : u.toNat < 2 ^ 28 + 2 ^ 16) :
    gwordU w u = gword w u.toNat := by
  unfold gwordU
  simp only []
  split
  · rename_i h
    have e : ∀ k, k < 8 → (((17 : USize) * (u >>> (1 : USize)) + 1 + 8 * (u &&& (1 : USize))) + k.toUSize).toNat =
        17 * (u.toNat / 2) + 1 + 8 * (u.toNat % 2) + k := fun k hk => by
      have e8 := usz_nowrap _ h.1
      have hb := gwordU_off u hu
      have hN := usz_pow
      rw [USize.toNat_add, usz_n k (by omega), hb, Nat.mod_eq_of_lt (by omega)]
    rw [uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!,
      e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega)]
    rfl
  · rfl

/-- `lowF` with the field count in `USize`. -/
@[inline] def lowFU (x : UInt64) (c : USize) : UInt64 :=
  if c < 32 then x &&& ((1 <<< (2 * c).toUInt64) - 1) else x

theorem lowFU_eq (x : UInt64) (c : USize) (hc : c.toNat < 2 ^ 20) : lowFU x c = lowF x c.toNat := by
  unfold lowFU lowF
  have e : (c < 32) = (c.toNat < 32) := by
    rw [show (c < 32) = (c.toNat < (32 : USize).toNat) from rfl, usz_lit 32 (by decide)]
  have e2 : (2 * c).toUInt64 = (2 * c.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [USize.toNat_toUInt64, usz_mul' _ _ (by rw [usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide),
      Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  simp only [e, e2]

/-- `comb` with the test `s = 0` done once (`z`). -/
@[inline] def combU (cur nxt : UInt64) (z : Bool) (sh sh' : UInt64) : UInt64 :=
  if z then cur else (cur >>> sh) ||| (nxt <<< sh')

theorem combU_eq (cur nxt : UInt64) (s : Nat) (sh sh' : UInt64) :
    combU cur nxt (s == 0) sh sh' = comb cur nxt s sh sh' := by
  unfold combU comb
  by_cases h : s = 0 <;> simp [h]

/-- `cnt64` before the final `toNat`. -/
@[inline] def cnt64U (x : UInt64) : UInt64 :=
  let t := (x ||| x >>> 1) &&& (0x5555555555555555 : UInt64)
  let a := (t &&& (0x3333333333333333 : UInt64)) + (t >>> 2 &&& (0x3333333333333333 : UInt64))
  let b := (a &&& (0x0f0f0f0f0f0f0f0f : UInt64)) + (a >>> 4 &&& (0x0f0f0f0f0f0f0f0f : UInt64))
  b % 255

theorem cnt64U_lt (x : UInt64) : (cnt64U x).toNat < 255 := by
  unfold cnt64U; simp only []; rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide)

theorem cnt64U_eq (x : UInt64) : (cnt64U x).toUSize.toNat = Packed.cnt64 x := by
  have h := cnt64U_lt x
  rw [UInt64.toNat_toUSize, Nat.mod_eq_of_lt (by have := usz_pow; omega)]
  rfl

/-- `hamW` on machine words: `x = 32 j` letters, `acc`, `lim`, `stop`, `u0` in `USize`
(`hamWU_eq`; `stop < 2^20` keeps `x + 32` from wrapping). -/
def hamWU (rw : Array UInt64) (gw : ByteArray) (u0 : USize) (z : Bool) (sh sh' : UInt64) (lim stop : USize)
    (hs : stop.toNat < 2 ^ 20) (x acc : USize) (cur : UInt64) : USize :=
  if h : x < stop then
    let j := x >>> (5 : USize)
    let nxt := gwordU gw (u0 + j + 1)
    let acc := acc + (cnt64U (lowFU (fold (rwAt rw j ^^^ combU cur nxt z sh sh')) (stop - x))).toUSize
    if lim < acc then lim + 1 else hamWU rw gw u0 z sh sh' lim stop hs (x + 32) acc nxt
  else acc
termination_by stop.toNat - x.toNat
decreasing_by
  have h' : x.toNat < stop.toNat := h
  rw [usz_add' _ _ (by rw [usz_lit 32 (by decide)]; omega), usz_lit 32 (by decide)]
  omega

theorem hamWU_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat)
    (u0U limU stopU : USize) (hu : u0U.toNat = u0) (hl : limU.toNat = lim) (hsU : stopU.toNat = stop)
    (hu' : u0 < 2 ^ 28) (hl' : lim < 2 ^ 20) (hs : stopU.toNat < 2 ^ 20) :
    ∀ n (x accU : USize) (j acc : Nat) (cur : UInt64), stop - 32 * j = n → x.toNat = 32 * j →
      accU.toNat = acc → acc < 2 ^ 21 →
      (hamWU rw gw u0U (s == 0) sh sh' limU stopU hs x accU cur).toNat = hamW rw gw u0 s sh sh' lim stop j acc cur := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro x accU j acc cur hn hx ha hacc
  have hN := usz_pow
  rw [hamWU, hamW]
  by_cases hc : 32 * j < stop
  · have hc' : x < stopU := by show x.toNat < stopU.toNat; omega
    rw [dif_pos hc', if_pos hc]
    simp only []
    have ej : (x >>> (5 : USize)).toNat = j := by rw [usz_shr5, hx]; omega
    have eu : (u0U + x >>> (5 : USize) + 1).toNat = u0 + j + 1 := by
      rw [usz_add' _ _ ?_, usz_add' _ _ ?_, ej, hu, usz_lit 1 (by decide)]
      · rw [ej, hu]; omega
      · rw [usz_add' _ _ (by rw [ej, hu]; omega), ej, hu, usz_lit 1 (by decide)]; omega
    have eg : gwordU gw (u0U + x >>> (5 : USize) + 1) = gword gw (u0 + j + 1) := by
      rw [gwordU_eq _ _ (by rw [eu]; omega), eu]
    have esx : (stopU - x).toNat = stop - 32 * j := by
      rw [USize.toNat_sub_of_le _ _ (by show x.toNat ≤ stopU.toNat; omega), hsU, hx]
    rw [eg, rwAt_eq, ej, combU_eq, lowFU_eq _ _ (by rw [esx]; omega), esx]
    generalize hk : Packed.cnt64 (lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j)) = c
    have hk' := cnt64U_eq (lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j))
    have hc255 : c < 255 := by
      rw [← hk]; exact cnt64U_lt _
    have ea : (accU + (cnt64U (lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j))).toUSize).toNat = acc + c := by
      rw [usz_add' _ _ (by rw [ha, hk', hk]; omega), ha, hk', hk]
    by_cases hlc : lim < acc + c
    · have : limU < accU + (cnt64U (lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j))).toUSize := by
        rw [USize.lt_iff_toNat_lt, ea, hl]; exact hlc
      rw [if_pos this, if_pos hlc, usz_add' _ _ (by rw [hl, usz_lit 1 (by decide)]; omega), hl, usz_lit 1 (by decide)]
    · have : ¬ limU < accU + (cnt64U (lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j))).toUSize := by
        intro h; apply hlc; rw [USize.lt_iff_toNat_lt, ea, hl] at h; exact h
      rw [if_neg this, if_neg hlc]
      exact ih (stop - 32 * (j + 1)) (by omega) _ _ (j + 1) (acc + c) _ rfl
        (by rw [usz_add' _ _ (by rw [usz_lit 32 (by decide)]; omega), usz_lit 32 (by decide), hx]; omega) ea (by omega)
  · have hc' : ¬ x < stopU := by intro h; have h' : x.toNat < stopU.toNat := h; omega
    rw [dif_neg hc', if_neg hc, ha]

/-- `hamW` for the compiled code (`hamW_eq_hamWF`): the `USize` loop `hamWU` when the
genome word index, `lim`, `stop`, `j` and `acc` are small (always, for reads ≤ 256 letters
on genomes below 2^33 letters), else the `Nat` loop. -/
def hamWF (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat)
    (j acc : Nat) (cur : UInt64) : Nat :=
  if h : u0 < 268435456 ∧ lim < 1048576 ∧ stop < 1048576 ∧ j < 16384 ∧ acc < 1048576 then
    (hamWU rw gw u0.toUSize (s == 0) sh sh' lim.toUSize stop.toUSize
      (by rw [usz_n _ (by omega)]; omega) (32 * j).toUSize acc.toUSize cur).toNat
  else hamWS rw gw u0 s sh sh' lim stop j acc cur
where
  /-- The same as `hamW` (its slow path; not rewritten by `csimp`). -/
  hamWS (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat)
      (j acc : Nat) (cur : UInt64) : Nat :=
    if 32 * j < stop then
      let nxt := gword gw (u0 + j + 1)
      let acc := acc + Packed.cnt64 (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j))
      if lim < acc then lim + 1 else hamWS rw gw u0 s sh sh' lim stop (j + 1) acc nxt
    else acc
  termination_by stop - 32 * j

theorem hamWS_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat) :
    ∀ n j acc cur, stop - 32 * j = n →
      hamWF.hamWS rw gw u0 s sh sh' lim stop j acc cur = hamW rw gw u0 s sh sh' lim stop j acc cur := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro j acc cur hn
  rw [hamWF.hamWS, hamW]
  split
  · simp only []
    split
    · rfl
    · exact ih _ (by omega) _ _ _ rfl
  · rfl

@[csimp] theorem hamW_eq_hamWF : @hamW = @hamWF := by
  funext rw gw u0 s sh sh' lim stop j acc cur
  unfold hamWF
  split
  · rename_i h
    exact (hamWU_eq rw gw u0 s sh sh' lim stop _ _ _ (usz_n _ (by omega)) (usz_n _ (by omega))
      (usz_n _ (by omega)) (by omega) (by omega) _ _ _ _ j acc cur rfl (usz_n _ (by omega))
      (usz_n _ (by omega)) (by omega)).symm
  · exact (hamWS_eq rw gw u0 s sh sh' lim stop _ j acc cur rfl).symm

/-- Position of the `k`-th mismatch (`k ≥ 1`) in `R[32j, stop)`, or `stop`. -/
def fwdW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat)
    (j k : Nat) (cur : UInt64) : Nat :=
  if 32 * j < stop then
    let nxt := gword gw (u0 + j + 1)
    let m := lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j)
    let c := Packed.cnt64 m
    if c < k then fwdW rw gw u0 s sh sh' stop (j + 1) (k - c) nxt else 32 * j + selLow m (k - 1)
  else stop
termination_by stop - 32 * j

/-! ### `fwdW` on machine words (compiled code only): `fwdW_eq_fwdWF`, as `hamW_eq_hamWF` -/

/-- `fwdW` on machine words: `x = 32 j`, `k`, `stop`, `u0` in `USize` (`fwdWU_eq`). -/
def fwdWU (rw : Array UInt64) (gw : ByteArray) (u0 : USize) (z : Bool) (sh sh' : UInt64) (stop : USize)
    (hs : stop.toNat < 2 ^ 20) (x k : USize) (cur : UInt64) : Nat :=
  if _h : x < stop then
    let j := x >>> (5 : USize)
    let nxt := gwordU gw (u0 + j + 1)
    let m := lowFU (fold (rwAt rw j ^^^ combU cur nxt z sh sh')) (stop - x)
    let c := (cnt64U m).toUSize
    if c < k then fwdWU rw gw u0 z sh sh' stop hs (x + 32) (k - c) nxt else x.toNat + selLow m (k.toNat - 1)
  else stop.toNat
termination_by stop.toNat - x.toNat
decreasing_by
  have h' : x.toNat < stop.toNat := _h
  rw [usz_add' _ _ (by rw [usz_lit 32 (by decide)]; omega), usz_lit 32 (by decide)]
  omega

theorem fwdWU_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat)
    (u0U stopU : USize) (hu : u0U.toNat = u0) (hsU : stopU.toNat = stop)
    (hu' : u0 < 2 ^ 28) (hs : stopU.toNat < 2 ^ 20) :
    ∀ n (x kU : USize) (j k : Nat) (cur : UInt64), stop - 32 * j = n → x.toNat = 32 * j →
      kU.toNat = k → k < 2 ^ 21 →
      fwdWU rw gw u0U (s == 0) sh sh' stopU hs x kU cur = fwdW rw gw u0 s sh sh' stop j k cur := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro x kU j k cur hn hx hk hk'
  have hN := usz_pow
  rw [fwdWU, fwdW]
  by_cases hc : 32 * j < stop
  · have hc' : x < stopU := by show x.toNat < stopU.toNat; omega
    rw [dif_pos hc', if_pos hc]
    simp only []
    have ej : (x >>> (5 : USize)).toNat = j := by rw [usz_shr5, hx]; omega
    have eu : (u0U + x >>> (5 : USize) + 1).toNat = u0 + j + 1 := by
      rw [usz_add' _ _ ?_, usz_add' _ _ ?_, ej, hu, usz_lit 1 (by decide)]
      · rw [ej, hu]; omega
      · rw [usz_add' _ _ (by rw [ej, hu]; omega), ej, hu, usz_lit 1 (by decide)]; omega
    have eg : gwordU gw (u0U + x >>> (5 : USize) + 1) = gword gw (u0 + j + 1) := by
      rw [gwordU_eq _ _ (by rw [eu]; omega), eu]
    have esx : (stopU - x).toNat = stop - 32 * j := by
      rw [USize.toNat_sub_of_le _ _ (by show x.toNat ≤ stopU.toNat; omega), hsU, hx]
    rw [eg, rwAt_eq, ej, combU_eq, lowFU_eq _ _ (by rw [esx]; omega), esx]
    generalize lowF (fold (rw[j]! ^^^ comb cur (gword gw (u0 + j + 1)) s sh sh')) (stop - 32 * j) = m
    have hk' := cnt64U_eq m
    generalize hcm : Packed.cnt64 m = c at hk'
    have hc255 : c < 255 := by rw [← hcm]; exact cnt64U_lt _
    by_cases hlc : c < k
    · have : (cnt64U m).toUSize < kU := by rw [USize.lt_iff_toNat_lt, hk', hk]; exact hlc
      rw [if_pos this, if_pos hlc]
      exact ih (stop - 32 * (j + 1)) (by omega) _ _ (j + 1) (k - c) _ rfl
        (by rw [usz_add' _ _ (by rw [usz_lit 32 (by decide)]; omega), usz_lit 32 (by decide), hx]; omega)
        (by rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, hk', hk]; omega), hk', hk]) (by omega)
    · have : ¬ (cnt64U m).toUSize < kU := by
        intro h; apply hlc; rw [USize.lt_iff_toNat_lt, hk', hk] at h; exact h
      rw [if_neg this, if_neg hlc, hx, hk]
  · have hc' : ¬ x < stopU := by intro h; have h' : x.toNat < stopU.toNat := h; omega
    rw [dif_neg hc', if_neg hc, hsU]

/-- `fwdW` for the compiled code (`fwdW_eq_fwdWF`): `fwdWU` when the arguments are small,
else the `Nat` loop. -/
def fwdWF (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat)
    (j k : Nat) (cur : UInt64) : Nat :=
  if h : u0 < 268435456 ∧ stop < 1048576 ∧ j < 16384 ∧ k < 1048576 then
    fwdWU rw gw u0.toUSize (s == 0) sh sh' stop.toUSize (by rw [usz_n _ (by omega)]; omega)
      (32 * j).toUSize k.toUSize cur
  else fwdWS rw gw u0 s sh sh' stop j k cur
where
  /-- The same as `fwdW` (its slow path; not rewritten by `csimp`). -/
  fwdWS (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat)
      (j k : Nat) (cur : UInt64) : Nat :=
    if 32 * j < stop then
      let nxt := gword gw (u0 + j + 1)
      let m := lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j)
      let c := Packed.cnt64 m
      if c < k then fwdWS rw gw u0 s sh sh' stop (j + 1) (k - c) nxt else 32 * j + selLow m (k - 1)
    else stop
  termination_by stop - 32 * j

theorem fwdWS_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat) :
    ∀ n j k cur, stop - 32 * j = n →
      fwdWF.fwdWS rw gw u0 s sh sh' stop j k cur = fwdW rw gw u0 s sh sh' stop j k cur := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro j k cur hn
  rw [fwdWF.fwdWS, fwdW]
  split
  · simp only []
    split
    · exact ih _ (by omega) _ _ _ rfl
    · rfl
  · rfl

@[csimp] theorem fwdW_eq_fwdWF : @fwdW = @fwdWF := by
  funext rw gw u0 s sh sh' stop j k cur
  unfold fwdWF
  split
  · rename_i h
    exact (fwdWU_eq rw gw u0 s sh sh' stop _ _ (usz_n _ (by omega)) (usz_n _ (by omega)) (by omega) _ _ _ _
      j k cur rfl (usz_n _ (by omega)) (usz_n _ (by omega)) (by omega)).symm
  · exact (fwdWS_eq rw gw u0 s sh sh' stop _ j k cur rfl).symm

/-- One past the `k`-th mismatch from the right (`k ≥ 1`) in `R[lo, e)`, chunk `j`
and below, or `lo`; `nxt` is the aligned word `u0 + j + 1`. -/
def bwdW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat) :
    (j k : Nat) → UInt64 → Nat
  | j, k, nxt =>
    let cur := gword gw (u0 + j)
    let m := highF (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (e - 32 * j)) (lo - 32 * j)
    let c := Packed.cnt64 m
    if k ≤ c then 32 * j + selHigh m (k - 1) + 1
    else if 32 * j ≤ lo then lo
    else match j with
      | 0 => lo
      | j + 1 => bwdW rw gw u0 s sh sh' lo e j (k - c) cur

/-! ### `bwdW` on machine words (compiled code only): `bwdW_eq_bwdWF`, as `hamW_eq_hamWF`
(the truncated subtractions `e - 32 j`, `lo - 32 j` are `subU`) -/

/-- `a - b` truncated at `0`, on `USize`. -/
@[inline] def subU (a b : USize) : USize := if b ≤ a then a - b else 0

theorem subU_eq (a b : USize) : (subU a b).toNat = a.toNat - b.toNat := by
  unfold subU
  split
  · rename_i h; rw [USize.toNat_sub_of_le _ _ h]
  · rename_i h
    have : ¬ b.toNat ≤ a.toNat := fun h' => h (USize.le_iff_toNat_le.mpr h')
    rw [show (0 : USize).toNat = 0 from rfl]; omega

/-- `highF` with the field count in `USize`. -/
@[inline] def highFU (x : UInt64) (c : USize) : UInt64 :=
  if c = 0 then x else if c < 32 then x &&& ~~~((1 <<< (2 * c).toUInt64) - 1) else 0

theorem highFU_eq (x : UInt64) (c : USize) (hc : c.toNat < 2 ^ 20) : highFU x c = highF x c.toNat := by
  unfold highFU highF
  have e0 : (c = 0) = (c.toNat = 0) := by
    apply propext; constructor
    · intro h; rw [h]; rfl
    · intro h; exact USize.toNat_inj.mp (by rw [h]; rfl)
  have e : (c < 32) = (c.toNat < 32) := by
    rw [show (c < 32) = (c.toNat < (32 : USize).toNat) from rfl, usz_lit 32 (by decide)]
  have e2 : (2 * c).toUInt64 = (2 * c.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [USize.toNat_toUInt64, usz_mul' _ _ (by rw [usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide),
      Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  simp only [e0, e, e2]

/-- `bwdW` on machine words: chunk `j`, `k`, `lo`, `e`, `u0` in `USize` (`bwdWU_eq`). -/
def bwdWU (rw : Array UInt64) (gw : ByteArray) (u0 : USize) (z : Bool) (sh sh' : UInt64) (lo e : USize)
    (j k : USize) (nxt : UInt64) : Nat :=
  let x := j <<< (5 : USize)
  let cur := gwordU gw (u0 + j)
  let m := highFU (lowFU (fold (rwAt rw j ^^^ combU cur nxt z sh sh')) (subU e x)) (subU lo x)
  let c := (cnt64U m).toUSize
  if k ≤ c then x.toNat + selHigh m (k.toNat - 1) + 1
  else if x ≤ lo then lo.toNat
  else if _h : j = 0 then lo.toNat
  else bwdWU rw gw u0 z sh sh' lo e (j - 1) (k - c) cur
termination_by j.toNat
decreasing_by
  have : j.toNat ≠ 0 := fun h' => _h (USize.toNat_inj.mp (by rw [h']; rfl))
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, usz_lit 1 (by decide)]; omega), usz_lit 1 (by decide)]
  omega

theorem usz_shl5 (a : USize) (h : a.toNat < 2 ^ 26) : (a <<< (5 : USize)).toNat = 32 * a.toNat := by
  have h5 : 5 % System.Platform.numBits = 5 := by cases System.Platform.numBits_eq <;> simp_all
  have hN := usz_pow
  rw [USize.toNat_shiftLeft, usz_lit 5 (by decide), h5, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bwdWU_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat)
    (u0U loU eU : USize) (hu : u0U.toNat = u0) (hl : loU.toNat = lo) (he : eU.toNat = e)
    (hu' : u0 < 2 ^ 28) (hl' : lo < 2 ^ 20) (he' : e < 2 ^ 20) :
    ∀ (j : Nat) (jU kU : USize) (k : Nat) (nxt : UInt64), jU.toNat = j → j < 2 ^ 16 →
      kU.toNat = k → k < 2 ^ 21 →
      bwdWU rw gw u0U (s == 0) sh sh' loU eU jU kU nxt = bwdW rw gw u0 s sh sh' lo e j k nxt := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro jU kU k nxt hj hj' hk hk'
  have hN := usz_pow
  rw [bwdWU, bwdW.eq_def]
  simp only []
  have ex : (jU <<< (5 : USize)).toNat = 32 * j := by rw [usz_shl5 _ (by omega), hj]
  have eu : (u0U + jU).toNat = u0 + j := by rw [usz_add' _ _ (by rw [hu, hj]; omega), hu, hj]
  have eg : gwordU gw (u0U + jU) = gword gw (u0 + j) := by rw [gwordU_eq _ _ (by rw [eu]; omega), eu]
  have ee : (subU eU (jU <<< (5 : USize))).toNat = e - 32 * j := by rw [subU_eq, he, ex]
  have el : (subU loU (jU <<< (5 : USize))).toNat = lo - 32 * j := by rw [subU_eq, hl, ex]
  rw [eg, rwAt_eq, hj, combU_eq, lowFU_eq _ _ (by rw [ee]; omega), ee, highFU_eq _ _ (by rw [el]; omega), el]
  generalize highF (lowF (fold (rw[j]! ^^^ comb (gword gw (u0 + j)) nxt s sh sh')) (e - 32 * j)) (lo - 32 * j) = m
  have hk2 := cnt64U_eq m
  generalize hcm : Packed.cnt64 m = c at hk2
  have hc255 : c < 255 := by rw [← hcm]; exact cnt64U_lt _
  by_cases h1 : k ≤ c
  · have : kU ≤ (cnt64U m).toUSize := by rw [USize.le_iff_toNat_le, hk2, hk]; exact h1
    rw [if_pos this, if_pos h1, ex, hk]
  · have : ¬ kU ≤ (cnt64U m).toUSize := by intro h; apply h1; rw [USize.le_iff_toNat_le, hk2, hk] at h; exact h
    rw [if_neg this, if_neg h1]
    by_cases h2 : 32 * j ≤ lo
    · have : jU <<< (5 : USize) ≤ loU := by rw [USize.le_iff_toNat_le, ex, hl]; exact h2
      rw [if_pos this, if_pos h2, hl]
    · have : ¬ jU <<< (5 : USize) ≤ loU := by intro h; apply h2; rw [USize.le_iff_toNat_le, ex, hl] at h; exact h
      rw [if_neg this, if_neg h2]
      cases j with
      | zero =>
        have : jU = 0 := USize.toNat_inj.mp (by rw [hj]; rfl)
        rw [dif_pos this, hl]
      | succ j =>
        have : ¬ jU = 0 := fun h' => by rw [h'] at hj; exact absurd hj (by simp)
        rw [dif_neg this]
        simp only []
        exact ih j (by omega) _ _ (k - c) _
          (by rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, usz_lit 1 (by decide)]; omega),
            usz_lit 1 (by decide), hj]; omega) (by omega)
          (by rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, hk2, hk]; omega), hk2, hk]) (by omega)

/-- `bwdW` for the compiled code (`bwdW_eq_bwdWF`): `bwdWU` when the arguments are small,
else the `Nat` recursion. -/
def bwdWF (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat)
    (j k : Nat) (nxt : UInt64) : Nat :=
  if u0 < 268435456 ∧ lo < 1048576 ∧ e < 1048576 ∧ j < 65536 ∧ k < 1048576 then
    bwdWU rw gw u0.toUSize (s == 0) sh sh' lo.toUSize e.toUSize j.toUSize k.toUSize nxt
  else bwdWS rw gw u0 s sh sh' lo e j k nxt
where
  /-- The same as `bwdW` (its slow path; not rewritten by `csimp`). -/
  bwdWS (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat) :
      (j k : Nat) → UInt64 → Nat
    | j, k, nxt =>
      let cur := gword gw (u0 + j)
      let m := highF (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (e - 32 * j)) (lo - 32 * j)
      let c := Packed.cnt64 m
      if k ≤ c then 32 * j + selHigh m (k - 1) + 1
      else if 32 * j ≤ lo then lo
      else match j with
        | 0 => lo
        | j + 1 => bwdWS rw gw u0 s sh sh' lo e j (k - c) cur

theorem bwdWS_eq (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat) :
    ∀ j k nxt, bwdWF.bwdWS rw gw u0 s sh sh' lo e j k nxt = bwdW rw gw u0 s sh sh' lo e j k nxt := by
  intro j
  induction j with
  | zero => intro k nxt; rw [bwdWF.bwdWS.eq_def, bwdW.eq_def]
  | succ j ih =>
    intro k nxt
    rw [bwdWF.bwdWS.eq_def, bwdW.eq_def]
    simp only [ih]

@[csimp] theorem bwdW_eq_bwdWF : @bwdW = @bwdWF := by
  funext rw gw u0 s sh sh' lo e j k nxt
  unfold bwdWF
  split
  · rename_i h
    exact (bwdWU_eq rw gw u0 s sh sh' lo e _ _ _ (usz_n _ (by omega)) (usz_n _ (by omega))
      (usz_n _ (by omega)) (by omega) (by omega) (by omega) j _ _ k nxt (usz_n _ (by omega)) (by omega)
      (usz_n _ (by omega)) (by omega)).symm
  · exact (bwdWS_eq rw gw u0 s sh sh' lo e j k nxt).symm

/-- Blocks `[b, stop)` all flagged. -/
def flagsOk (w : ByteArray) (b stop : Nat) : Bool :=
  if b < stop then w.get! (17 * b) == 1 && flagsOk w (b + 1) stop else true
termination_by stop - b

/-! `flagsOk` on machine words (compiled code only): `flagsOk_eq_flagsOkF` (`@[csimp]`), the flag
byte offset `17 b` stepped by 17 in `USize` and read by `getU`. -/

/-- `flagsOk w b stop` with `p = 17 b`, `e = 17 stop` (`flagsOkU_eq`). -/
def flagsOkU (w : ByteArray) (p e : USize) : Bool :=
  if h : p < e ∧ e < 4294967278 then getU w p == 1 && flagsOkU w (p + 17) e else true
termination_by e.toNat - p.toNat
decreasing_by
  have h' : p.toNat < e.toNat := h.1
  have h2 : e.toNat < (4294967278 : USize).toNat := h.2
  rw [usz_lit 4294967278 (by decide)] at h2
  rw [usz_add' _ _ (by rw [usz_lit 17 (by decide)]; omega), usz_lit 17 (by decide)]
  omega

theorem flagsOkU_eq (w : ByteArray) (stop : Nat) (e : USize) (he : e.toNat = 17 * stop) (hb : 17 * stop < 4294967278) :
    ∀ n (p : USize) b, stop - b = n → p.toNat = 17 * b → flagsOkU w p e = flagsOk w b stop := by
  intro n
  induction n with
  | zero =>
    intro p b hn hp
    have h : ¬ (p < e ∧ e < 4294967278) := fun h => by have h' : p.toNat < e.toNat := h.1; omega
    rw [flagsOkU, dif_neg h, flagsOk, if_neg (show ¬ b < stop by omega)]
  | succ n ih =>
    intro p b hn hp
    have h : p < e ∧ e < 4294967278 := ⟨by show p.toNat < e.toNat; omega,
      by show e.toNat < (4294967278 : USize).toNat; rw [usz_lit 4294967278 (by decide)]; omega⟩
    rw [flagsOkU, dif_pos h, flagsOk, if_pos (show b < stop by omega), getU_eq, hp,
      ih _ (b + 1) (by omega) (by rw [usz_add' _ _ (by rw [usz_lit 17 (by decide)]; omega), usz_lit 17 (by decide), hp]; omega)]

/-- `flagsOk` (its slow path; not rewritten by `csimp`). -/
def flagsOkS (w : ByteArray) (b stop : Nat) : Bool :=
  if b < stop then w.get! (17 * b) == 1 && flagsOkS w (b + 1) stop else true
termination_by stop - b

theorem flagsOkS_eq (w : ByteArray) (stop : Nat) : ∀ n b, stop - b = n → flagsOkS w b stop = flagsOk w b stop := by
  intro n
  induction n with
  | zero => intro b hn; rw [flagsOkS, flagsOk, if_neg (show ¬ b < stop by omega), if_neg (show ¬ b < stop by omega)]
  | succ n ih =>
    intro b hn
    rw [flagsOkS, flagsOk, if_pos (show b < stop by omega), if_pos (show b < stop by omega), ih _ (by omega)]

/-- `flagsOk` for the compiled code (`flagsOk_eq_flagsOkF`). -/
def flagsOkF (w : ByteArray) (b stop : Nat) : Bool :=
  if 17 * stop < 4294967278 ∧ b ≤ stop then flagsOkU w (17 * b).toUSize (17 * stop).toUSize
  else flagsOkS w b stop

@[csimp] theorem flagsOk_eq_flagsOkF : @flagsOk = @flagsOkF := by
  funext w b stop
  unfold flagsOkF; split
  · rename_i h
    exact (flagsOkU_eq w stop _ (usz_n _ (by omega)) (by omega) _ _ b rfl (usz_n _ (by omega))).symm
  · exact (flagsOkS_eq w stop _ b rfl).symm

/-- The window `[st, st + len)` of `P` lies in flagged blocks (`len ≥ 1`). -/
@[inline] def winOk (P : PGen) (st len : Nat) : Bool :=
  decide (st + len ≤ P.n) && flagsOk P.w ((P.o + st) / 64) ((P.o + st + len - 1) / 64 + 1)

/-- Word scans at absolute genome start `a` (read letter `x` ↦ `a + x`). -/
@[inline] def hamA (rw : Array UInt64) (gw : ByteArray) (a lim stop : Nat) : Nat :=
  let s := a % 32
  hamW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 lim stop 0 0 (gword gw (a / 32))

@[inline] def fwdA (rw : Array UInt64) (gw : ByteArray) (a stop k : Nat) : Nat :=
  let s := a % 32
  fwdW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 stop 0 k (gword gw (a / 32))

@[inline] def bwdA (rw : Array UInt64) (gw : ByteArray) (a lo e k : Nat) : Nat :=
  let s := a % 32
  let j := (e - 1) / 32
  bwdW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 lo e j k (gword gw (a / 32 + j + 1))

/-- Number of letters scanned with bytes before the word path. -/
def pre : Nat := 8

/-- `fwdMis R G st stop 0 k` (`stop ≤ R.size`; words at absolute `a`). -/
@[inline] def fwdK (R G : ByteArray) (rw : Array UInt64) (gw : ByteArray) (a st stop k : Nat) : Nat :=
  let f := fwdMis R G st (min stop pre) 0 k
  if f < min stop pre then f else fwdA rw gw a stop k

/-- `bwdMis R G st len lo R.size k` (words at absolute `a` for the end diagonal). -/
@[inline] def bwdK (R G : ByteArray) (rw : Array UInt64) (gw : ByteArray) (a st len lo k : Nat) : Nat :=
  let b := bwdMis R G st len (max lo (R.size - pre)) R.size k
  if max lo (R.size - pre) < b then b else bwdA rw gw a lo R.size k

/-- `gappedPen2` with a third level (one gap, at most two mismatches): exact up to
`lim ≤ 17` (`gappedPen3_spec`); `= gappedPen2` for `lim ≤ 15`. -/
def gappedPen3 (r g : ByteArray) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdMis r g st (n - skip) 0 1
  let E1 := bwdMis r g st len skip n 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdMis r g st (n - skip) 0 2
  let E2 := bwdMis r g st len skip n 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdMis r g st (n - skip) 0 3
  let E3 := bwdMis r g st len skip n 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

/-- `kerG` with `gappedPen3`: exact up to `lim ≤ 17`. -/
def kerG3 (R G : ByteArray) (st len lim : Nat) : Nat :=
  if st + len ≤ G.size then
    if len = R.size then
      let h := hamming R G st (lim / 4) 0 R.size 0
      if 4 * h ≤ lim then 4 * h else lim + 1
    else gappedPen3 R G st len lim
  else lim + 1

/-- `fwdMis R G st stop 0 k`: the byte pre-scan, then the word scan when the range is
flagged (checked only then), else the byte loop. -/
@[inline] def fwdL (R G : ByteArray) (K : RP) (P : PGen) (st stop k : Nat) : Nat :=
  let f := fwdMis R G st (min stop pre) 0 k
  if f < min stop pre then f
  else if K.ok && decide (stop ≤ R.size) && winOk P st stop then fwdA K.w P.w (P.o + st) stop k
  else fwdMis R G st stop 0 k

/-- `bwdMis R G st len lo R.size k` likewise (end diagonal `st + len − n`). -/
@[inline] def bwdL (R G : ByteArray) (K : RP) (P : PGen) (st len lo k : Nat) : Nat :=
  let n := R.size
  let b := bwdMis R G st len (max lo (n - pre)) n k
  if max lo (n - pre) < b then b
  else if K.ok && decide (n ≤ st + len) && decide (lo < n) && winOk P (st + len - n + lo) (n - lo) then
    bwdA K.w P.w (P.o + (st + len - n)) lo n k
  else bwdMis R G st len lo n k

/-- `gappedPen3` with the scans `fwdL` / `bwdL`. -/
@[inline] def gappedL (R G : ByteArray) (K : RP) (P : PGen) (st len lim : Nat) : Nat :=
  let n := R.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdL R G K P st (n - skip) 1
  let E1 := bwdL R G K P st len skip 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdL R G K P st (n - skip) 2
  let E2 := bwdL R G K P st len skip 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdL R G K P st (n - skip) 3
  let E3 := bwdL R G K P st len skip 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

/-- Word path applies to window `(st, len)`. -/
@[inline] def wordOk (R : ByteArray) (K : RP) (P : PGen) (st len : Nat) : Bool :=
  K.ok && decide (0 < R.size) && decide (0 < len) && decide (R.size ≤ st + len) && winOk P st len

/-- The word kernel: `kerG3` (so `kerG` for `lim ≤ 15`). -/
def kerGK (R : ByteArray) (K : RP) (G : ByteArray) (P : PGen) (st len lim : Nat) : Nat :=
  if len = R.size then
    if wordOk R K P st len then
      let h := hamA K.w P.w (P.o + st) (lim / 4) R.size
      if 4 * h ≤ lim then 4 * h else lim + 1
    else if lim / 4 < hamming R G st (lim / 4) 0 (min R.size pre) 0 then lim + 1
    else kerG3 R G st len lim
  else if st + len ≤ P.n then gappedL R G K P st len lim
  else lim + 1

end MapSpec.Fast
