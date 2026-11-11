import PairPacked
import MapperK250Seed
import MapperK250Words

/-!
# Bucket entries checked with one genome word

`okAtP` (codecs/PairPacked.lean) compares the seed with the genome at a bucket entry
letter by letter (`eqRunP`, three runs).  `okAtW` reads the 25 genome letters at the
entry as one word (`gW`: two aligned words of a `PGen` shifted, `comb`), XORs it with
the seed's little-endian code (`seedLE`, built once per lookup) and checks each run
with a mask (`eqW`).  The word path is taken only when the seed is ACGT, the runs lie
in the 25 letters, and the genome window lies in flagged (pure ACGT) blocks; anything
else is `okAtP` itself.

    okAtW … = okAtP …           (okAtW_eq, for every `PGen`)
    scanAW … = scanAP …         (scanAW_eq)
    lookupPW … = lookupPP …     (lookupPW_eq)
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-! ## Algorithm -/

/-- Little-endian 2-bit code of `R[j, j+k)` (letter `i` in field `i`), and whether all
are ACGT; `i`, `w`, `ok` the state. -/
def seedLE (R : ByteArray) (j k i : Nat) (w : UInt64) (ok : Bool) : UInt64 × Bool :=
  if i < k then
    let t := codeTab.get! (R.get! (j + i)).toNat
    seedLE R j k (i + 1) (w ||| (t &&& 3).toUInt64 <<< (2 * i).toUInt64) (ok && decide (t < 4))
  else (w, ok)
termination_by k - i

/-! ### `seedLE` on machine words (compiled code only): `seedLE_eq_seedLEF`, as `hamW_eq_hamWF`
(kernels/k250/MapperK250.lean) -/

/-- `seedLE` with `j`, `k`, `i` in `USize` (`seedLEU_eq`). -/
def seedLEU (R : ByteArray) (j k i : USize) (w : UInt64) (ok : Bool) : UInt64 × Bool :=
  if _h : i < k then
    let t := codeU (getU R (j + i))
    seedLEU R j k (i + 1) (w ||| (t &&& 3).toUInt64 <<< (2 * i).toUInt64) (ok && decide (t < 4))
  else (w, ok)
termination_by k.toNat - i.toNat
decreasing_by
  have h' : i.toNat < k.toNat := _h
  have := USize.toNat_lt_size k
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, usz_lit 1 (by decide), Nat.mod_eq_of_lt (by omega)]
  omega

theorem seedLEU_eq (R : ByteArray) (j k : Nat) (jU kU : USize) (hj : jU.toNat = j) (hk : kU.toNat = k)
    (hj' : j < 2 ^ 31) (hk' : k < 2 ^ 20) :
    ∀ n (iU : USize) (i : Nat) w ok, k - i = n → iU.toNat = i → i < 2 ^ 20 →
      seedLEU R jU kU iU w ok = seedLE R j k i w ok := by
  intro n
  induction n with
  | zero =>
    intro iU i w ok hn hi hi'
    have h : ¬ iU < kU := fun h => by have h' : iU.toNat < kU.toNat := h; omega
    rw [seedLEU, seedLE, dif_neg h, if_neg (by omega)]
  | succ n ih =>
    intro iU i w ok hn hi hi'
    have hN := usz_pow
    have h : iU < kU := by show iU.toNat < kU.toNat; omega
    rw [seedLEU, seedLE, dif_pos h, if_pos (by omega)]
    have ep : (jU + iU).toNat = j + i := by rw [usz_add' _ _ (by omega), hj, hi]
    have e2 : (2 * iU).toUInt64 = (2 * i).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [USize.toNat_toUInt64, usz_mul' _ _ (by rw [usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide), hi,
        Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [codeU_eq, getU_eq, ep, e2]
    exact ih _ (i + 1) _ _ (by omega)
      (by rw [usz_add' _ _ (by rw [usz_lit 1 (by decide)]; omega), usz_lit 1 (by decide), hi]) (by omega)

/-- `seedLE` for the compiled code (`seedLE_eq_seedLEF`). -/
@[inline] def seedLEF (R : ByteArray) (j k i : Nat) (w : UInt64) (ok : Bool) : UInt64 × Bool :=
  if j < 2147483648 ∧ k < 1048576 ∧ i < 1048576 then
    seedLEU R j.toUSize k.toUSize i.toUSize w ok
  else seedLES R j k i w ok
where
  /-- The same as `seedLE` (its slow path; not rewritten by `csimp`). -/
  seedLES (R : ByteArray) (j k i : Nat) (w : UInt64) (ok : Bool) : UInt64 × Bool :=
    if i < k then
      let t := codeTab.get! (R.get! (j + i)).toNat
      seedLES R j k (i + 1) (w ||| (t &&& 3).toUInt64 <<< (2 * i).toUInt64) (ok && decide (t < 4))
    else (w, ok)
  termination_by k - i

theorem seedLES_eq (R : ByteArray) (j k : Nat) :
    ∀ n i w ok, k - i = n → seedLEF.seedLES R j k i w ok = seedLE R j k i w ok := by
  intro n
  induction n with
  | zero => intro i w ok hn; rw [seedLEF.seedLES, seedLE, if_neg (by omega), if_neg (by omega)]
  | succ n ih =>
    intro i w ok hn
    rw [seedLEF.seedLES, seedLE, if_pos (by omega), if_pos (by omega)]
    exact ih _ _ _ (by omega)

theorem seedLE_eq_seedLEF : @seedLE = @seedLEF := by
  funext R j k i w ok
  unfold seedLEF
  split
  · rename_i h
    exact (seedLEU_eq R j k _ _ (usz_n _ (by omega)) (usz_n _ (by omega)) (by omega) (by omega) _ _ i w ok rfl
      (usz_n _ (by omega)) (by omega)).symm
  · exact (seedLES_eq R j k _ i w ok rfl).symm

/-! ### A 25-letter seed straight-line (compiled code only): `seedLE_eqF2` -/

theorem cU_lt (R : ByteArray) (j : USize) (k : Nat) (h : j.toNat + 25 ≤ R.size) (hj : j.toNat < 2 ^ 31) (hk : k < 25) :
    (j + k.toUSize).toNat < R.size := by
  rw [USize.toNat_add, usz_n k (by omega), Nat.mod_eq_of_lt (by have := usz_pow; omega)]; omega

/-- Letter `k` of the seed at `j`, coded (one bounds test per seed: `h`). -/
@[inline] def cU (R : ByteArray) (j : USize) (k : Nat) (h : j.toNat + 25 ≤ R.size) (hj : j.toNat < 2 ^ 31)
    (hk : k < 25) : UInt8 :=
  codeU (R.uget (j + k.toUSize) (cU_lt R j k h hj hk))

theorem cU_eq (R : ByteArray) (j : USize) (k : Nat) (h : j.toNat + 25 ≤ R.size) (hj : j.toNat < 2 ^ 31) (hk : k < 25) :
    cU R j k h hj hk = codeTab.get! (R.get! (j.toNat + k)).toNat := by
  unfold cU
  rw [codeU_eq, uget_get!, USize.toNat_add, usz_n k (by omega), Nat.mod_eq_of_lt (by have := usz_pow; omega)]

/-- `seedLE R j 25 0 w ok`, straight-line (`seed25_eq`). -/
@[inline] def seed25 (R : ByteArray) (j : USize) (h : j.toNat + 25 ≤ R.size) (hj : j.toNat < 2 ^ 31) (w : UInt64)
    (ok : Bool) : UInt64 × Bool :=
  let t := cU R j 0 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (0 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 1 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (2 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 2 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (4 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 3 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (6 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 4 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (8 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 5 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (10 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 6 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (12 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 7 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (14 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 8 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (16 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 9 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (18 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 10 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (20 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 11 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (22 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 12 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (24 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 13 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (26 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 14 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (28 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 15 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (30 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 16 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (32 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 17 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (34 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 18 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (36 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 19 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (38 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 20 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (40 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 21 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (42 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 22 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (44 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 23 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (46 : UInt64); let ok := ok && decide (t < 4)
  let t := cU R j 24 h hj (by decide); let w := w ||| (t &&& 3).toUInt64 <<< (48 : UInt64); let ok := ok && decide (t < 4)
  (w, ok)

theorem seed25_eq (R : ByteArray) (j : USize) (h : j.toNat + 25 ≤ R.size) (hj : j.toNat < 2 ^ 31) (w : UInt64)
    (ok : Bool) : seed25 R j h hj w ok = seedLE R j.toNat 25 0 w ok := by
  unfold seed25
  simp only [cU_eq]
  repeat (rw [seedLE, if_pos (by omega)]; simp only [])
  rw [seedLE, if_neg (by omega)]
  rfl

/-- `seedLE` for the compiled code: a 25-letter seed from letter 0 straight-line, else `seedLEF`. -/
@[inline] def seedLEF2 (R : ByteArray) (j k i : Nat) (w : UInt64) (ok : Bool) : UInt64 × Bool :=
  if h : k = 25 ∧ i = 0 ∧ j < 2147483648 ∧ j + 25 ≤ R.size then
    seed25 R j.toUSize (by rw [usz_n j (by omega)]; omega) (by rw [usz_n j (by omega)]; omega) w ok
  else seedLEF R j k i w ok

/-- Compiled code runs `seedLEF2`. -/
@[csimp] theorem seedLE_eqF2 : @seedLE = @seedLEF2 := by
  funext R j k i w ok
  unfold seedLEF2
  split
  · rename_i h
    obtain ⟨hk, hi, hj, -⟩ := h
    subst hk hi
    rw [seed25_eq, usz_n j (by omega)]
  · exact seedLE_eq_seedLEF ▸ rfl

/-- Genome letters `[p, p+32)` of `P` (field `i` = letter `p + i`; flagged blocks only). -/
@[inline] def gW (P : PGen) (p : Nat) : UInt64 :=
  let a := P.o + p
  let s := a % 32
  comb (gword P.w (a / 32)) (gword P.w (a / 32 + 1)) s (2 * s).toUInt64 (64 - 2 * s).toUInt64

/-- Fields `[a, a+n)` of `x` all zero. -/
@[inline] def eqW (x : UInt64) (a n : Nat) : Bool := lowF (x >>> (2 * a).toUInt64) n == 0

section MzW
open Mz

/-- `okAtP` with the three runs read from one genome word (`rc`, `rok`: `seedLE R s q 0 0 true`). -/
@[inline] def okAtW (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 t : Nat) : Bool :=
  let e := ix.slot t
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     if rok && decide (o ≤ pos) && decide (n1 ≤ Mz.q) && decide (o + a2 + n2 ≤ Mz.q) &&
         decide (o + ix.k ≤ Mz.q) && winOk G (pos - o) Mz.q then
       let tg := ix.tagOf e
       let x := gW G (pos - o) ^^^ rc
       if ix.flagF tg = 0 then (ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw &&
         eqW x 0 n1 && eqW x (o + a2) n2 && (ix.kf == ix.kb || eqW x o ix.k)
       else eqW x 0 Mz.q
     else okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t)

def scanAW (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanAW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t then
        acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

/-- `lookupPP` with `okAtW`. -/
@[inline] def lookupPW (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  let r := seedLE R s Mz.q 0 0 true
  scanAW ix G R r.1 r.2 s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base bit (ix.loB p.b) #[]

/-- At most one place per slot. -/
theorem scanAW_size (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) : ∀ n t (acc : Array Nat), hi - t = n →
    (scanAW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc).size ≤ acc.size + (hi - t) := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [scanAW, if_neg (by omega)]; omega
  | succ n ih =>
    intro t acc hn
    rw [scanAW, if_pos (by omega)]
    refine Nat.le_trans (ih (t + 1) _ (by omega)) ?_
    split <;> simp <;> omega

/-- A lookup returns at most the bucket's slot count. -/
theorem lookupPW_size (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) :
    (lookupPW ix G R s p base bit).size ≤ ix.hiB p.b - ix.loB p.b := by
  unfold lookupPW
  simpa using scanAW_size ix G R _ _ s _ _ _ _ _ _ _ _ _ _ base bit _ _ #[] rfl

end MzW

/-! ## The key test on `UInt64` slots (compiled in place of `lookupPW`: `lookupPW_eqK`) -/

section MzWU
open Mz

/-- Slot `t` before its `toNat` (`slot_eqW`). -/
@[noinline] def slotW (B : @& ByteArray) (sw t : Nat) : UInt64 :=
  let j := sw * t
  if sw = 4 then rd4 B j
  else if sw = 5 then rd4 B j ||| byteAt B (j + 4) 32
  else if sw = 6 then rd4 B j ||| byteAt B (j + 4) 32 ||| byteAt B (j + 5) 40
  else rd4 B j ||| (rd4 B (j + 4) <<< 32)

theorem slot_eqW (ix : MzIdx) (t : Nat) : ix.slot t = (slotW ix.sl ix.sw t).toNat := rfl

/-! `slotW` on machine words (compiled code only): `slotW_eq_slotWF` (`@[csimp]`). The slot offset
`sw * t` is a `USize`, and the four (or five, six, eight) bytes are read by `uget` behind one bounds
check, so the reads can merge. -/

theorem uget_eq_getElem (B : ByteArray) (u : USize) (i : Nat) (h1 : u.toNat < B.size) (h2 : i < B.size)
    (e : u.toNat = i) : B.uget u h1 = B[i]'h2 := by subst e; rfl

theorem ulit (c : Nat) (h : c < 2 ^ 32) : (OfNat.ofNat c : USize).toNat = c := pgu_n c h

/-- On a 64-bit platform (checked once per call by `slotWF`) machine words do not wrap below 2^64. -/
theorem usz_n64 (hU : System.Platform.numBits = 64) (n : Nat) (h : n < 2 ^ 64) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt (by rw [hU]; exact h)]

theorem uadd64 (hU : System.Platform.numBits = 64) (a b : USize) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by show _ < 2 ^ System.Platform.numBits; rw [hU]; exact h)]

theorem uaddl (hU : System.Platform.numBits = 64) (j : USize) (c : Nat) (hc : c < 2 ^ 32)
    (h : j.toNat + c < 2 ^ 64) : (j + (OfNat.ofNat c : USize)).toNat = j.toNat + c := by
  rw [uadd64 hU _ _ (by rw [ulit c hc]; exact h), ulit c hc]

/-- `rd4` at a machine-word offset `j < 2^60` (`rd4U_eq`). -/
@[inline] def rd4U (hU : System.Platform.numBits = 64) (B : ByteArray) (j : USize) (hj : j.toNat < 2 ^ 60) : UInt64 :=
  if h : j + 3 < B.usize then
    have h3 : (j + 3).toNat < B.usize.toNat := h
    have e3 : (j + 3).toNat = j.toNat + 3 := uaddl hU j 3 (by decide) (by omega)
    have hs := pgu_usize_le B
    (B.uget j (by omega)).toUInt64 |||
      ((B.uget (j + 1) (by rw [uaddl hU j 1 (by decide) (by omega)]; omega)).toUInt64 <<< 8) |||
      ((B.uget (j + 2) (by rw [uaddl hU j 2 (by decide) (by omega)]; omega)).toUInt64 <<< 16) |||
      ((B.uget (j + 3) (by omega)).toUInt64 <<< 24)
  else rd4 B j.toNat

theorem rd4U_eq (hU : System.Platform.numBits = 64) (B : ByteArray) (j : USize) (hj : j.toNat < 2 ^ 60) :
    rd4U hU B j hj = rd4 B j.toNat := by
  unfold rd4U
  by_cases h : j + 3 < B.usize
  · rw [dif_pos h]
    have h3 : (j + 3).toNat < B.usize.toNat := h
    have e3 : (j + 3).toNat = j.toNat + 3 := uaddl hU j 3 (by decide) (by omega)
    have hs := pgu_usize_le B
    unfold rd4
    rw [dif_pos (by omega)]
    dsimp only
    rw [uget_eq_getElem B j j.toNat _ (by omega) rfl,
      uget_eq_getElem B (j + 1) (j.toNat + 1) _ (by omega) (uaddl hU j 1 (by decide) (by omega)),
      uget_eq_getElem B (j + 2) (j.toNat + 2) _ (by omega) (uaddl hU j 2 (by decide) (by omega)),
      uget_eq_getElem B (j + 3) (j.toNat + 3) _ (by omega) e3]
  · rw [dif_neg h]

/-- `byteAt` at a machine-word offset. -/
@[inline] def byteAtU (B : ByteArray) (j : USize) (sh : UInt64) : UInt64 := (pgGet B j).toUInt64 <<< sh

theorem umul64 (hU : System.Platform.numBits = 64) (sw t : USize) (hs : sw.toNat < 16) (ht : t.toNat < 2 ^ 40) :
    (sw * t).toNat = sw.toNat * t.toNat := by
  have : sw.toNat * t.toNat < 2 ^ 44 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hs) (Nat.le_refl _))
      (by rw [show (2 : Nat) ^ 44 = 16 * 2 ^ 40 by decide]; exact Nat.mul_lt_mul_of_pos_left ht (by decide))
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by show _ < 2 ^ System.Platform.numBits; rw [hU]; omega)]

/-- `slotW` with `sw`, `t`, the offset in `USize` (`slotWU_eq`). -/
@[inline] def slotWU (hU : System.Platform.numBits = 64) (B : ByteArray) (sw t : USize) (hs : sw.toNat < 16)
    (ht : t.toNat < 2 ^ 40) : UInt64 :=
  let j := sw * t
  have ej : j.toNat = sw.toNat * t.toNat := umul64 hU sw t hs ht
  have hm : sw.toNat * t.toNat < 2 ^ 44 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hs) (Nat.le_refl _))
      (by rw [show (2 : Nat) ^ 44 = 16 * 2 ^ 40 by decide]; exact Nat.mul_lt_mul_of_pos_left ht (by decide))
  if sw = 4 then rd4U hU B j (by omega)
  else if sw = 5 then rd4U hU B j (by omega) ||| byteAtU B (j + 4) 32
  else if sw = 6 then rd4U hU B j (by omega) ||| byteAtU B (j + 4) 32 ||| byteAtU B (j + 5) 40
  else rd4U hU B j (by omega) ||| (rd4U hU B (j + 4) (by rw [uaddl hU j 4 (by decide) (by omega)]; omega) <<< 32)

theorem slotWU_eq (hU : System.Platform.numBits = 64) (B : ByteArray) (sw t : USize) (hs : sw.toNat < 16)
    (ht : t.toNat < 2 ^ 40) : slotWU hU B sw t hs ht = slotW B sw.toNat t.toNat := by
  have ej : (sw * t).toNat = sw.toNat * t.toNat := umul64 hU sw t hs ht
  have hm : sw.toNat * t.toNat < 2 ^ 44 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hs) (Nat.le_refl _))
      (by rw [show (2 : Nat) ^ 44 = 16 * 2 ^ 40 by decide]; exact Nat.mul_lt_mul_of_pos_left ht (by decide))
  have e4 : (sw * t + 4).toNat = sw.toNat * t.toNat + 4 := by
    rw [uaddl hU _ 4 (by decide) (by rw [ej]; omega), ej]
  have e5 : (sw * t + 5).toNat = sw.toNat * t.toNat + 5 := by
    rw [uaddl hU _ 5 (by decide) (by rw [ej]; omega), ej]
  have q : ∀ c : Nat, c < 16 → ((sw = (OfNat.ofNat c : USize)) ↔ sw.toNat = c) := fun c hc => by
    constructor
    · intro h; rw [h]; exact ulit c (by omega)
    · intro h; apply USize.toNat_inj.mp; rw [h]; exact (ulit c (by omega)).symm
  unfold slotWU slotW byteAtU
  simp only [rd4U_eq, pgGet_eq, ej, e4, e5, Mz.byteAt, q 4 (by decide), q 5 (by decide), q 6 (by decide)]

/-- 2^40 as a constant (a literal ≥ 2^32 in a body is rebuilt from its digits at every call). -/
@[noinline] def two40 : Nat := 1099511627776

/-- `slotW` for the compiled code. -/
@[inline] def slotWF (B : @& ByteArray) (sw t : Nat) : UInt64 :=
  if h : System.Platform.numBits = 64 ∧ sw < 16 ∧ t < two40 then
    slotWU h.1 B sw.toUSize t.toUSize (by rw [usz_n64 h.1 sw (by omega)]; exact h.2.1)
      (by rw [usz_n64 h.1 t (by have := h.2.2; unfold two40 at this; omega)]; have := h.2.2; unfold two40 at this; exact this)
  else slotW B sw t

@[csimp] theorem slotW_eq_slotWF : @slotW = @slotWF := by
  funext B sw t
  unfold slotWF; split
  · rename_i h
    have := h.2.2; unfold two40 at this
    rw [slotWU_eq, usz_n64 h.1 sw (by omega), usz_n64 h.1 t (by omega)]
  · rfl

/-- `scanAW` with the key test on the `UInt64` slot first (`kb`, `key`: `ix.kbM`, the key, as
`UInt64`s); an entry whose key differs is skipped without `okAtW`. -/
def scanAWK (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if (slotW ix.sl ix.sw t &&& kb) != keyU then acc
       else if okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t then
        acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

theorem okAtW_key (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 t : Nat) (hkb : ix.kbM < 2 ^ 64) (hkey : key < 2 ^ 64)
    (h : (slotW ix.sl ix.sw t &&& ix.kbM.toUInt64) != key.toUInt64) :
    okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t = false := by
  have hne : (ix.slot t &&& ix.kbM == key) = false := by
    rw [slot_eqW]
    have e1 : (slotW ix.sl ix.sw t &&& ix.kbM.toUInt64).toNat = (slotW ix.sl ix.sw t).toNat &&& ix.kbM := by
      rw [UInt64.toNat_and]; congr 1; simp; omega
    have hk : (key.toUInt64).toNat = key := by simp; omega
    simp only [bne_iff_ne, ne_eq] at h
    rw [← e1]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h2; apply h; apply UInt64.toNat_inj.1; rw [h2, hk]
  unfold okAtW
  simp only [hne, Bool.false_and]

theorem scanAWK_eq (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (hkb : ix.kbM < 2 ^ 64) (hkey : key < 2 ^ 64) :
    ∀ n t acc, hi - t = n →
      scanAWK ix G R rc rok ix.kbM.toUInt64 key.toUInt64 s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
        scanAW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro n
  induction n with
  | zero =>
    intro t acc hn
    have h' : ¬ t < hi := by omega
    rw [scanAWK, scanAW, if_neg h', if_neg h']
  | succ n ih =>
    intro t acc hn
    have h' : t < hi := by omega
    rw [scanAWK, scanAW, if_pos h', if_pos h']
    rw [ih (t + 1) _ (by omega)]
    congr 1
    split
    · next hk => rw [okAtW_key ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t hkb hkey hk]; rfl
    · rfl

/-- First `t' ∈ [t, hi)` whose slot has key bits `keyU` (`max t hi` if none): the key test
alone, with few arguments (`scanAWK_nextK`). -/
def nextK (B : ByteArray) (sw : Nat) (kb keyU : UInt64) (hi t : Nat) : Nat :=
  if t < hi then
    if (slotW B sw t &&& kb) != keyU then nextK B sw kb keyU hi (t + 1) else t
  else t
termination_by hi - t

theorem nextK_spec (B : ByteArray) (sw : Nat) (kb keyU : UInt64) (hi : Nat) :
    ∀ n t, hi - t = n → t ≤ nextK B sw kb keyU hi t ∧
      (nextK B sw kb keyU hi t < hi → (slotW B sw (nextK B sw kb keyU hi t) &&& kb) = keyU) ∧
      (¬ nextK B sw kb keyU hi t < hi → hi ≤ nextK B sw kb keyU hi t) := by
  intro n
  induction n with
  | zero => intro t hn; rw [nextK, if_neg (by omega)]; omega
  | succ n ih =>
    intro t hn
    rw [nextK, if_pos (by omega)]
    split
    · obtain ⟨h1, h2, h3⟩ := ih (t + 1) (by omega); exact ⟨by omega, h2, h3⟩
    · next h => simp only [bne_iff_ne, ne_eq, Classical.not_not] at h; exact ⟨Nat.le_refl _, fun _ => h, by omega⟩

/-- `scanAWK` skipping to the next key match with `nextK` (`scanAWK_eq2`). -/
def scanAWK2 (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  let t' := nextK ix.sl ix.sw kb keyU hi t
  if h : t' < hi then
    have : t ≤ t' := (nextK_spec ix.sl ix.sw kb keyU hi _ t rfl).1
    scanAWK2 ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (t' + 1)
      (if okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t' then
        acc.push (anc base bit (ix.posOf (ix.slot t') - o)) else acc)
  else acc
termination_by hi - t

/-- Slots before `nextK` add nothing. -/
theorem scanAWK_skip (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ n t acc, hi - t = n →
      scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
        scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (nextK ix.sl ix.sw kb keyU hi t) acc := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [nextK, if_neg (by omega)]
  | succ n ih =>
    intro t acc hn
    rw [nextK, if_pos (by omega)]
    split
    · next h => rw [scanAWK, if_pos (by omega), if_pos h]; exact ih (t + 1) acc (by omega)
    · rfl

theorem scanAWK_eq2 (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ n t acc, hi - t = n →
      scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
        scanAWK2 ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn
    rw [scanAWK_skip ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit _ t acc rfl, scanAWK2]
    have hs := nextK_spec ix.sl ix.sw kb keyU hi _ t rfl
    simp only []
    split
    · next h =>
      rw [scanAWK, if_pos h, if_neg (by simp [hs.2.1 h])]
      exact ih _ (by omega) _ _ rfl
    · next h => rw [scanAWK, if_neg (by omega)]

@[inline] def eqWU (x sh m : UInt64) : Bool := ((x >>> sh) &&& m) == 0

/-- `gW P p` for `a = P.o + p`, on machine words. -/
@[inline] def gWU (w : @& ByteArray) (a : UInt64) : UInt64 :=
  let u := (a >>> 5).toUSize
  let s5 := a &&& 31
  combU (gwordU w u) (gwordU w (u + 1)) (s5 == 0) ((2 : UInt64) * s5) ((64 : UInt64) - 2 * s5)

/-- The flag test of `winOk P p 25`, `a = P.o + p`, on machine words. -/
@[inline] def winFlagsU (w : @& ByteArray) (a : UInt64) : Bool :=
  flagsOkU w ((17 : UInt64) * (a >>> 6)).toUSize ((17 : UInt64) * (((a + 24) >>> 6) + 1)).toUSize

/-- The per-match test of `okAtW` on machine words, for a match whose key bits are known to agree and under the
guard of `scanAWK3`; `2`: not on the word path (use `okAtW`). -/
@[inline] def fastOkW (w : @& ByteArray) (Gn Go oU rc e : UInt64) (Tu tM fsh bsh ash fM pmoU bwU awU o2U : UInt64)
    (sh2 sh3 m1 m2 m3 : UInt64) (kfEq : Bool) : UInt8 :=
  let pos := e >>> Tu
  if oU ≤ pos then
    let st := pos - oU
    if 25 ≤ Gn && st ≤ Gn - 25 then
      let a := Go + st
      if winFlagsU w a then
        let x := gWU w a ^^^ rc
        let tg := e &&& tM
        if tg >>> fsh == 0 then
          if ((tg >>> bsh) &&& fM &&& pmoU) == bwU && (((tg >>> ash) &&& fM) >>> o2U) == awU &&
              eqWU x 0 m1 && eqWU x sh2 m2 && (kfEq || eqWU x sh3 m3) then 1 else 0
        else if eqWU x 0 1125899906842623 then 1 else 0
      else 2
    else 2
  else 2

theorem u64n (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega

theorem shr64 (e T : UInt64) (hT : T.toNat < 64) : (e >>> T).toNat = e.toNat >>> T.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hT]

theorem eqW_eqWU (x : UInt64) (a n : Nat) (hn : n < 32) :
    eqW x a n = eqWU x (2 * a).toUInt64 ((1 <<< (2 * n).toUInt64) - 1) := by
  unfold eqW eqWU lowF
  rw [ite_cond_eq_true _ _ (by simpa using hn)]

theorem winFlagsU_eq (P : PGen) (p : Nat) (a : UInt64) (ha : a.toNat = P.o + p) (hp : p + 25 ≤ P.n)
    (hn : P.n < 2 ^ 32) (hGo : P.o < 2 ^ 32) :
    winFlagsU P.w a = flagsOk P.w ((P.o + p) / 64) ((P.o + p + 25 - 1) / 64 + 1) := by
  have hN := usz_pow
  have hA : a.toNat < 2 ^ 33 := by omega
  have sh6 : ∀ y : UInt64, (y >>> 6).toNat = y.toNat / 64 := fun y => by
    rw [UInt64.toNat_shiftRight]; simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow]; rfl
  have h24 : (a + 24).toNat = a.toNat + 24 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_ofNat]; omega
  have hb0 : ((17 : UInt64) * (a >>> 6)).toNat = 17 * (a.toNat / 64) := by
    rw [UInt64.toNat_mul, sh6]; simp only [UInt64.toNat_ofNat]; omega
  have hb1 : ((17 : UInt64) * (((a + 24) >>> 6) + 1)).toNat = 17 * ((a.toNat + 24) / 64 + 1) := by
    have h1 : (((a + 24) >>> 6) + 1).toNat = (a.toNat + 24) / 64 + 1 := by
      rw [UInt64.toNat_add, sh6, h24]; simp only [UInt64.toNat_ofNat]; omega
    rw [UInt64.toNat_mul, h1]; simp only [UInt64.toNat_ofNat]; omega
  unfold winFlagsU
  have e1 : (a.toNat + 24) / 64 + 1 = (P.o + p + 25 - 1) / 64 + 1 := by omega
  rw [e1] at hb1
  have hb0' : (((17 : UInt64) * (a >>> 6))).toUSize.toNat = 17 * ((P.o + p) / 64) := by
    rw [UInt64.toNat_toUSize, hb0, ha]; exact Nat.mod_eq_of_lt (by omega)
  have hb1' : (((17 : UInt64) * (((a + 24) >>> 6) + 1))).toUSize.toNat = 17 * ((P.o + p + 25 - 1) / 64 + 1) := by
    rw [UInt64.toNat_toUSize, hb1]; exact Nat.mod_eq_of_lt (by omega)
  exact flagsOkU_eq P.w ((P.o + p + 25 - 1) / 64 + 1) _ hb1' (by omega) _ _ _ rfl hb0'

theorem gWU_eq (P : PGen) (p : Nat) (a : UInt64) (ha : a.toNat = P.o + p) (hp : p + 25 ≤ P.n)
    (hn : P.n < 2 ^ 32) (hGo : P.o < 2 ^ 32) :
    gWU P.w a = gW P p := by
  have hA : a.toNat < 2 ^ 33 := by omega
  have hN := usz_pow
  have hu : ((a >>> 5).toUSize).toNat = a.toNat / 32 := by
    have h5 : (a >>> 5).toNat = a.toNat / 32 := by
      rw [UInt64.toNat_shiftRight]
      simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      rfl
    rw [UInt64.toNat_toUSize, h5]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (a &&& 31).toNat = a.toNat % 32 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod a.toNat 5
  have hA' : a.toNat = P.o + p := ha
  have hu1 : (((a >>> 5).toUSize) + 1).toNat = a.toNat / 32 + 1 := by
    rw [usz_add' _ _ (by rw [hu, usz_lit 1 (by decide)]; omega), hu, usz_lit 1 (by decide)]
  have g1 := gwordU_eq P.w (a >>> 5).toUSize (by rw [hu]; omega)
  have g2 := gwordU_eq P.w ((a >>> 5).toUSize + 1) (by rw [hu1]; omega)
  rw [hu] at g1
  rw [hu1] at g2
  have h2 : ((2 : UInt64) * (a &&& 31)) = (2 * (a.toNat % 32)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, hs, u64n _ (by omega)]
    simp only [UInt64.toNat_ofNat]
    omega
  have h3 : ((64 : UInt64) - (2 * (a.toNat % 32)).toUInt64) = (64 - 2 * (a.toNat % 32)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    have hm : (2 * (a.toNat % 32)).toUInt64.toNat = 2 * (a.toNat % 32) := u64n _ (by omega)
    have hle : (2 * (a.toNat % 32)).toUInt64 ≤ (64 : UInt64) := by
      rw [UInt64.le_iff_toNat_le, hm]; simp only [UInt64.toNat_ofNat]; omega
    rw [UInt64.toNat_sub_of_le _ _ hle, hm, u64n _ (by omega)]
    simp only [UInt64.toNat_ofNat]
  have hz : ((a &&& 31) == 0) = (a.toNat % 32 == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h; rw [← hs, h]; rfl
    · intro h; apply UInt64.toNat_inj.mp; rw [hs, h]; rfl
  unfold gWU gW
  simp only [g1, g2, h2, h3, hz, combU_eq]
  rw [hA']


theorem fastOkW_eq (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool)
    (s o key bw aw pmo o2 n1 a2 n2 t : Nat) (e : UInt64) (he : e.toNat = ix.slot t)
    (hrok : rok = true) (hn1 : n1 ≤ 25) (hn2 : o + a2 + n2 ≤ 25) (hk : o + ix.k ≤ 25)
    (hkb : ix.kbM < 2 ^ 32) (hkey : key < 2 ^ 32) (hke : (e &&& ix.kbM.toUInt64) = key.toUInt64)
    (hT : ix.T < 64) (hfsh : ix.fsh < 64) (hbsh : ix.bsh < 64) (hash : ix.ash < 64) (ho2 : o2 < 64)
    (htM : ix.tM < 2 ^ 32) (hfM : ix.fM < 2 ^ 32) (hpmo : pmo < 2 ^ 32) (hbw : bw < 2 ^ 32) (haw : aw < 2 ^ 32)
    (ho : o < 2 ^ 32) (hGn : G.n < 2 ^ 32) (hGo : G.o < 2 ^ 32) :
    (let r := fastOkW G.w G.n.toUInt64 G.o.toUInt64 o.toUInt64 rc e ix.T.toUInt64 ix.tM.toUInt64 ix.fsh.toUInt64
        ix.bsh.toUInt64 ix.ash.toUInt64 ix.fM.toUInt64 pmo.toUInt64 bw.toUInt64 aw.toUInt64 o2.toUInt64
        (2 * (o + a2)).toUInt64 (2 * o).toUInt64 ((1 <<< (2 * n1).toUInt64) - 1) ((1 <<< (2 * n2).toUInt64) - 1)
        ((1 <<< (2 * ix.k).toUInt64) - 1) (ix.kf == ix.kb)
     if r == 2 then okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t else r == 1) =
      okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t := by
  have hq : Mz.q = 25 := rfl
  have hkt : (ix.slot t &&& ix.kbM == key) = true := by
    have h1 : (e &&& ix.kbM.toUInt64).toNat = e.toNat &&& ix.kbM := by
      rw [UInt64.toNat_and, u64n _ (by omega)]
    rw [beq_iff_eq, ← he, ← h1, hke, u64n _ (by omega)]
  by_cases hr : fastOkW G.w G.n.toUInt64 G.o.toUInt64 o.toUInt64 rc e ix.T.toUInt64 ix.tM.toUInt64 ix.fsh.toUInt64
        ix.bsh.toUInt64 ix.ash.toUInt64 ix.fM.toUInt64 pmo.toUInt64 bw.toUInt64 aw.toUInt64 o2.toUInt64
        (2 * (o + a2)).toUInt64 (2 * o).toUInt64 ((1 <<< (2 * n1).toUInt64) - 1) ((1 <<< (2 * n2).toUInt64) - 1)
        ((1 <<< (2 * ix.k).toUInt64) - 1) (ix.kf == ix.kb) = 2
  · simp only [hr, beq_self_eq_true, if_true]
  · have hT' : ix.T.toUInt64.toNat = ix.T := u64n _ (by omega)
    have hpos : (e >>> ix.T.toUInt64).toNat = ix.posOf (ix.slot t) := by
      rw [shr64 _ _ (by omega), hT', he]; rfl
    have c1 : o.toUInt64 ≤ e >>> ix.T.toUInt64 := by
      refine Classical.byContradiction fun h => hr ?_
      simp [fastOkW, h]
    have c2 : (decide (25 ≤ G.n.toUInt64) && decide (e >>> ix.T.toUInt64 - o.toUInt64 ≤ G.n.toUInt64 - 25)) = true := by
      refine Classical.byContradiction fun h => hr ?_
      simp only [Bool.not_eq_true] at h
      simp [fastOkW, c1, h]
    -- Nat facts
    have hle : o ≤ ix.posOf (ix.slot t) := by
      have := (UInt64.le_iff_toNat_le).mp c1
      rwa [u64n _ (by omega), hpos] at this
    have hst : (e >>> ix.T.toUInt64 - o.toUInt64).toNat = ix.posOf (ix.slot t) - o := by
      rw [UInt64.toNat_sub_of_le _ _ c1, hpos, u64n _ (by omega)]
    have hGn25 : 25 ≤ G.n ∧ ix.posOf (ix.slot t) - o ≤ G.n - 25 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at c2
      obtain ⟨c2a, c2b⟩ := c2
      rw [UInt64.le_iff_toNat_le, u64n _ (by omega)] at c2a
      rw [UInt64.le_iff_toNat_le, hst, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, u64n _ (by omega)]; simpa using c2a), u64n _ (by omega)] at c2b
      simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at c2b c2a
      omega
    have ha : (G.o.toUInt64 + (e >>> ix.T.toUInt64 - o.toUInt64)).toNat = G.o + (ix.posOf (ix.slot t) - o) := by
      rw [UInt64.toNat_add, hst, u64n _ (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have c3 : winFlagsU G.w (G.o.toUInt64 + (e >>> ix.T.toUInt64 - o.toUInt64)) = true := by
      refine Classical.byContradiction fun h => hr ?_
      simp only [Bool.not_eq_true] at h
      simp [fastOkW, c1, c2, h]
    have hw : winOk G (ix.posOf (ix.slot t) - o) 25 = true := by
      have := winFlagsU_eq G (ix.posOf (ix.slot t) - o) _ ha (by omega) hGn hGo
      unfold winOk
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      rw [← this]; exact c3
    -- the tag fields
    have hm64 : ∀ m : Nat, m < 2 ^ 32 → m < 2 ^ 64 := fun m h => by omega
    have uEq : ∀ (x : UInt64) (n m : Nat), x.toNat = n → m < 2 ^ 64 → (x == m.toUInt64) = (n == m) := by
      intro x n m hx hm
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      constructor
      · intro h; rw [← hx, h, u64n _ hm]
      · intro h; apply UInt64.toNat_inj.mp; rw [hx, u64n _ hm, h]
    have htg : (e &&& ix.tM.toUInt64).toNat = ix.tagOf (ix.slot t) := by
      rw [UInt64.toNat_and, he, u64n _ (by omega)]; rfl
    have hfl : ((e &&& ix.tM.toUInt64) >>> ix.fsh.toUInt64 == 0) = decide (ix.flagF (ix.tagOf (ix.slot t)) = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro h
        have := congrArg UInt64.toNat h
        rw [shr64 _ _ (by rw [u64n _ (by omega)]; omega), htg, u64n _ (by omega)] at this
        exact this
      · intro h
        apply UInt64.toNat_inj.mp
        rw [shr64 _ _ (by rw [u64n _ (by omega)]; omega), htg, u64n _ (by omega)]
        exact h
    have hbf : ((e &&& ix.tM.toUInt64) >>> ix.bsh.toUInt64 &&& ix.fM.toUInt64 &&& pmo.toUInt64 == bw.toUInt64) =
        (ix.befF (ix.tagOf (ix.slot t)) &&& pmo == bw) := by
      apply uEq _ _ _ _ (by omega)
      rw [UInt64.toNat_and, UInt64.toNat_and, shr64 _ _ (by rw [u64n _ (by omega)]; omega), htg,
        u64n _ (by omega), u64n _ (by omega), u64n _ (by omega)]
      rfl
    have haf : (((e &&& ix.tM.toUInt64) >>> ix.ash.toUInt64 &&& ix.fM.toUInt64) >>> o2.toUInt64 == aw.toUInt64) =
        (ix.aftF (ix.tagOf (ix.slot t)) >>> o2 == aw) := by
      apply uEq _ _ _ _ (by omega)
      rw [shr64 _ _ (by rw [u64n _ (by omega)]; omega), UInt64.toNat_and,
        shr64 _ _ (by rw [u64n _ (by omega)]; omega), htg, u64n _ (by omega), u64n _ (by omega), u64n _ (by omega)]
      rfl
    have hx := gWU_eq G (ix.posOf (ix.slot t) - o) _ ha (by omega) hGn hGo
    have hC : (decide (o ≤ ix.posOf (ix.slot t)) && true && true && true && winOk G (ix.posOf (ix.slot t) - o) 25) = true := by
      simp [hle, hw]
    have hval : fastOkW G.w G.n.toUInt64 G.o.toUInt64 o.toUInt64 rc e ix.T.toUInt64 ix.tM.toUInt64 ix.fsh.toUInt64
        ix.bsh.toUInt64 ix.ash.toUInt64 ix.fM.toUInt64 pmo.toUInt64 bw.toUInt64 aw.toUInt64 o2.toUInt64
        (2 * (o + a2)).toUInt64 (2 * o).toUInt64 ((1 <<< (2 * n1).toUInt64) - 1) ((1 <<< (2 * n2).toUInt64) - 1)
        ((1 <<< (2 * ix.k).toUInt64) - 1) (ix.kf == ix.kb) =
        (if ((e &&& ix.tM.toUInt64) >>> ix.fsh.toUInt64 == 0) = true then
          if (((e &&& ix.tM.toUInt64) >>> ix.bsh.toUInt64 &&& ix.fM.toUInt64 &&& pmo.toUInt64 == bw.toUInt64) &&
              (((e &&& ix.tM.toUInt64) >>> ix.ash.toUInt64 &&& ix.fM.toUInt64) >>> o2.toUInt64 == aw.toUInt64) &&
              eqWU (gW G (ix.posOf (ix.slot t) - o) ^^^ rc) 0 ((1 <<< (2 * n1).toUInt64) - 1) &&
              eqWU (gW G (ix.posOf (ix.slot t) - o) ^^^ rc) (2 * (o + a2)).toUInt64 ((1 <<< (2 * n2).toUInt64) - 1) &&
              (ix.kf == ix.kb || eqWU (gW G (ix.posOf (ix.slot t) - o) ^^^ rc) (2 * o).toUInt64 ((1 <<< (2 * ix.k).toUInt64) - 1))) = true
          then (1 : UInt8) else 0
        else if eqWU (gW G (ix.posOf (ix.slot t) - o) ^^^ rc) 0 1125899906842623 = true then 1 else 0) := by
      simp only [fastOkW, c1, c2, c3, hx, if_true]
    rw [hval]
    unfold okAtW
    simp only [hkt, Bool.true_and, hrok, hq, hn1, hn2, hk, decide_true, hC, if_true]
    rw [hfl, hbf, haf]
    have e0 : (2 * 0 : Nat).toUInt64 = 0 := rfl
    have e25 : (1125899906842623 : UInt64) = (1 <<< (2 * 25 : Nat).toUInt64) - 1 := by decide
    by_cases hf : ix.flagF (ix.tagOf (ix.slot t)) = 0
    · simp only [hf, decide_true, if_true]
      rw [eqW_eqWU _ 0 n1 (by omega), eqW_eqWU _ (o + a2) n2 (by omega), eqW_eqWU _ o ix.k (by omega), e0]
      split <;> simp_all
    · simp only [hf, decide_false, if_false]
      rw [eqW_eqWU _ 0 25 (by omega), e0, e25]
      generalize eqWU (gW G (ix.posOf (ix.slot t) - o) ^^^ rc) 0 ((1 <<< (2 * 25 : Nat).toUInt64) - 1) = b
      cases b <;> rfl


@[inline] def lt32M (a : Nat) : Bool := a >>> 32 == 0

theorem lt32M_iff (a : Nat) : lt32M a = true ↔ a < 2 ^ 32 := by
  unfold lt32M
  rw [beq_iff_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  omega

/-- All the conversions of `scanAWF` are exact. -/
@[inline] def fastG (ix : MzIdx) (G : PGen) (rok : Bool) (kb keyU : UInt64)
    (o key bw aw pmo o2 n1 a2 n2 : Nat) : Bool :=
  rok && decide (n1 ≤ 25) && decide (o + a2 + n2 ≤ 25) && decide (o + ix.k ≤ 25) &&
  lt32M ix.kbM && lt32M key && (kb == ix.kbM.toUInt64) && (keyU == key.toUInt64) &&
  decide (ix.T < 64) && decide (ix.fsh < 64) && decide (ix.bsh < 64) && decide (ix.ash < 64) && decide (o2 < 64) &&
  lt32M ix.tM && lt32M ix.fM && lt32M pmo && lt32M bw && lt32M aw && lt32M o && lt32M G.n && lt32M G.o

/-! ## EXPERIMENT (exp/prefetch, measurement only; not for merge)
`prefetchAt` / `touchAt` are the identity on `i`; the C body touches the byte `i` of the array (inline C, no new .c file or build change).
`pfB` / `pfMode` read `LA_PF_B` (look-ahead in slots, 0 = off) and `LA_PF_MODE` (1 = volatile read, 2 = prefetch) from the environment once. -/

@[extern c inline "(__builtin_prefetch(lean_sarray_cptr(#1) + #2, 0, 3), #2)"]
def prefetchAt (a : @& ByteArray) (i : USize) : USize := i

@[extern c inline "((void)*(volatile unsigned char*)(lean_sarray_cptr(#1) + #2), #2)"]
def touchAt (a : @& ByteArray) (i : USize) : USize := i

@[extern c inline "({ extern char* getenv(const char*); extern int atoi(const char*); static size_t v = (size_t)-1; if (v == (size_t)-1) { const char* s = getenv(\"LA_PF_B\"); v = s ? (size_t)atoi(s) : 0; } v; })"]
def pfB (_ : Unit) : USize := 0

@[extern c inline "({ extern char* getenv(const char*); extern int atoi(const char*); static size_t v = (size_t)-1; if (v == (size_t)-1) { const char* s = getenv(\"LA_PF_MODE\"); v = s ? (size_t)atoi(s) : 0; } v; })"]
def pfMode (_ : Unit) : USize := 0

/-- Touch the genome block that the candidate with slot `e` will read (`0` always). -/
@[inline] def pfOne (w : @& ByteArray) (Go oU Tu e : UInt64) (mode : USize) : USize :=
  let pos := e >>> Tu
  if oU ≤ pos then
    let a := Go + (pos - oU)
    let off : USize := ((17 : UInt64) * (a >>> 6)).toUSize
    let off2 : USize := ((17 : UInt64) * (((a + 24) >>> 6) + 1)).toUSize
    if mode == 2 then (prefetchAt w off - off) + (prefetchAt w off2 - off2)
    else if mode == 1 && off2 < w.usize then (touchAt w off - off) + (touchAt w off2 - off2)
    else 0
  else 0

/-- The look-ahead for slot `t + B` (`0`). -/
def pfAhead (sl : @& ByteArray) (sw hi t : Nat) (w : @& ByteArray) (Go oU Tu : UInt64) : Nat :=
  let B := (pfB ()).toNat
  if B == 0 then 0 else
  if t + B < hi then (pfOne w Go oU Tu (slotW sl sw (t + B)) (pfMode ())).toNat else 0

/-- The first `k` slots from `t`. -/
def pfInit (sl : @& ByteArray) (sw hi t : Nat) (w : @& ByteArray) (Go oU Tu : UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => (if t + k < hi then (pfOne w Go oU Tu (slotW sl sw (t + k)) (pfMode ())).toNat else 0) +
      pfInit sl sw hi t w Go oU Tu k

/-- `scanAWK2` with the match test on machine words (`scanAWF_eq`). -/
def scanAWF (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat)
    (Gn Go oU Tu tM fsh bsh ash fM pmoU bwU awU o2U sh2 sh3 m1 m2 m3 : UInt64) (kfEq : Bool)
    (t : Nat) (acc : Array Nat) : Array Nat :=
  let t' := nextK ix.sl ix.sw kb keyU hi t
  if h : t' < hi then
    have : t ≤ t' := (nextK_spec ix.sl ix.sw kb keyU hi _ t rfl).1
    let e := slotW ix.sl ix.sw t'
    let ahead := pfAhead ix.sl ix.sw hi t' G.w Go oU Tu
    let r := fastOkW G.w Gn Go oU rc e Tu tM fsh bsh ash fM pmoU bwU awU o2U sh2 sh3 m1 m2 m3 kfEq
    scanAWF ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit Gn Go oU Tu tM fsh bsh ash fM pmoU bwU awU
      o2U sh2 sh3 m1 m2 m3 kfEq (t' + 1 + ahead)
      (if (if r == 2 then okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t' else r == 1) then
        acc.push (anc base bit ((e >>> Tu).toNat - o)) else acc)
  else acc
termination_by hi - t


theorem scanAWF_eq (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat)
    (hg : fastG ix G rok kb keyU o key bw aw pmo o2 n1 a2 n2 = true) :
    ∀ n t acc, hi - t = n →
      scanAWF ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit G.n.toUInt64 G.o.toUInt64 o.toUInt64
        ix.T.toUInt64 ix.tM.toUInt64 ix.fsh.toUInt64 ix.bsh.toUInt64 ix.ash.toUInt64 ix.fM.toUInt64 pmo.toUInt64
        bw.toUInt64 aw.toUInt64 o2.toUInt64 (2 * (o + a2)).toUInt64 (2 * o).toUInt64
        ((1 <<< (2 * n1).toUInt64) - 1) ((1 <<< (2 * n2).toUInt64) - 1) ((1 <<< (2 * ix.k).toUInt64) - 1)
        (ix.kf == ix.kb) t acc =
      scanAWK2 ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  simp only [fastG, Bool.and_eq_true, decide_eq_true_eq, lt32M_iff, beq_iff_eq, and_assoc] at hg
  obtain ⟨hrok, hn1, hn2, hk, hkb, hkey, hkbe, hkeye, hT, hfsh, hbsh, hash, ho2, htM, hfM, hpmo, hbw, haw, ho, hGn, hGo⟩ := hg
  subst hkbe hkeye
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn
    rw [scanAWF, scanAWK2]
    simp only []
    split
    · next h =>
      have hs := nextK_spec ix.sl ix.sw ix.kbM.toUInt64 key.toUInt64 hi _ t rfl
      have hke := hs.2.1 h
      have heq := fastOkW_eq ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 (nextK ix.sl ix.sw ix.kbM.toUInt64 key.toUInt64 hi t)
        (slotW ix.sl ix.sw (nextK ix.sl ix.sw ix.kbM.toUInt64 key.toUInt64 hi t)) (by rw [slot_eqW]) hrok hn1 hn2 hk hkb hkey hke
        hT hfsh hbsh hash ho2 htM hfM hpmo hbw haw ho hGn hGo
      simp only [] at heq
      rw [heq]
      have hpos : (slotW ix.sl ix.sw (nextK ix.sl ix.sw ix.kbM.toUInt64 key.toUInt64 hi t) >>> ix.T.toUInt64).toNat =
          ix.posOf (ix.slot (nextK ix.sl ix.sw ix.kbM.toUInt64 key.toUInt64 hi t)) := by
        rw [shr64 _ _ (by rw [u64n _ (by omega)]; omega), u64n _ (by omega), slot_eqW]; rfl
      rw [hpos]
      exact ih _ (by have := hs.1; omega) _ _ rfl
    · rfl


/-- `scanAWK2` with the match test on machine words when every conversion is exact (`scanAWK_eq3`). -/
def scanAWK3 (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if fastG ix G rok kb keyU o key bw aw pmo o2 n1 a2 n2 then
    scanAWF ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit G.n.toUInt64 G.o.toUInt64 o.toUInt64
      ix.T.toUInt64 ix.tM.toUInt64 ix.fsh.toUInt64 ix.bsh.toUInt64 ix.ash.toUInt64 ix.fM.toUInt64 pmo.toUInt64
      bw.toUInt64 aw.toUInt64 o2.toUInt64 (2 * (o + a2)).toUInt64 (2 * o).toUInt64
      ((1 <<< (2 * n1).toUInt64) - 1) ((1 <<< (2 * n2).toUInt64) - 1) ((1 <<< (2 * ix.k).toUInt64) - 1)
      (ix.kf == ix.kb) (t + pfInit ix.sl ix.sw hi t G.w G.o.toUInt64 o.toUInt64 ix.T.toUInt64 (pfB ()).toNat) acc
  else scanAWK2 ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc

/-- Compiled code runs `scanAWK3`. -/
@[csimp] theorem scanAWK_eqC : @scanAWK = @scanAWK3 := by
  funext ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc
  rw [scanAWK_eq2 ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit _ t acc rfl, scanAWK3]
  split
  · next hg => exact (scanAWF_eq ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit hg _ t acc rfl).symm
  · rfl

/-- `lookupPW` through `scanAWK` when the key mask fits a `UInt64` (`lookupPW_eqK`). -/
@[inline] def lookupPWK (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  let r := seedLE R s Mz.q 0 0 true
  let key := p.h &&& ix.kbM
  if ix.kbM < 2 ^ 64 && key < 2 ^ 64 then
    scanAWK ix G R r.1 r.2 ix.kbM.toUInt64 key.toUInt64 s o key ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
      ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
      (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
      (ix.hiB p.b) base bit (ix.loB p.b) #[]
  else
    scanAW ix G R r.1 r.2 s o key ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
      ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
      (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
      (ix.hiB p.b) base bit (ix.loB p.b) #[]

/-- Compiled code runs `lookupPWK`. -/
@[csimp] theorem lookupPW_eqK : @lookupPW = @lookupPWK := by
  funext ix G R s p base bit
  unfold lookupPW lookupPWK
  simp only []
  split
  · next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [scanAWK_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.1 h.2 _ _ _ rfl]
  · rfl

/-! ## The first `k` anchors of a lookup (`lookupPWk_extract`): the bucket is scanned in pieces of 256 slots
and the scan stops once `k` anchors are in hand.  `scanAWK` only appends, in slot order, so the first `k`
anchors are the same as the whole lookup's. -/

theorem scanAWK_app (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) : ∀ n t (acc : Array Nat), hi - t = n →
    scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
      acc ++ scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t #[] := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn
    conv => lhs; rw [scanAWK.eq_def]
    conv => rhs; rw [scanAWK.eq_def]
    split
    · rw [ih (hi - (t + 1)) (by omega) (t + 1) _ rfl,
        ih (hi - (t + 1)) (by omega) (t + 1) (if (slotW ix.sl ix.sw t &&& kb != keyU) = true then #[] else
          if okAtW ix G R rc rok s o key bw aw pmo o2 n1 a2 n2 t = true then
            #[].push (anc base bit (ix.posOf (ix.slot t) - o)) else #[]) rfl]
      split
      · simp
      · split <;> simp [Array.append_assoc]
    · simp

theorem scanAWK_split (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit m : Nat) (hm : m ≤ hi) : ∀ n t (acc : Array Nat), m - t = n →
    scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
      scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (max t m)
        (scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 m base bit t acc) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn
    by_cases ht : t < m
    · conv => lhs; rw [scanAWK.eq_def, if_pos (show t < hi by omega)]
      conv => rhs; rw [scanAWK.eq_def (hi := m), if_pos ht]
      rw [ih (m - (t + 1)) (by omega) (t + 1) _ rfl, show max (t + 1) m = max t m by omega]
    · conv => rhs; rw [scanAWK.eq_def (hi := m), if_neg ht]
      rw [show max t m = t by omega]

/-- `scanAWK` from `t` in pieces of `256` slots, stopped once `acc` holds `k` anchors (`scanAWKk_extract`). -/
def scanAWKk (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit k : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if k ≤ acc.size ∨ hi ≤ t then acc
  else scanAWKk ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit k (min hi (t + 256))
    (scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 (min hi (t + 256)) base bit t acc)
termination_by hi - t

theorem scanAWKk_extract (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit k : Nat) : ∀ n t (acc : Array Nat), hi - t = n →
    (scanAWKk ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit k t acc).extract 0 k =
      (scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc).extract 0 k := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn
    rw [scanAWKk]
    split
    · rename_i h
      rcases h with h | h
      · rw [scanAWK_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl,
          Array.extract_append, show k - acc.size = 0 by omega]
        simp
      · rw [scanAWK.eq_def, if_neg (by omega)]
    · rename_i h
      rw [ih (hi - min hi (t + 256)) (by omega) _ _ rfl,
        scanAWK_split ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (min hi (t + 256))
          (Nat.min_le_left _ _) _ t acc rfl, show max t (min hi (t + 256)) = min hi (t + 256) by omega]

/-- `lookupPWK` keeping (at least) the first `k` anchors (`lookupPWk_extract`). -/
def lookupPWk (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit k : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  let r := seedLE R s Mz.q 0 0 true
  let key := p.h &&& ix.kbM
  if ix.kbM < 2 ^ 64 && key < 2 ^ 64 then
    scanAWKk ix G R r.1 r.2 ix.kbM.toUInt64 key.toUInt64 s o key ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
      ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
      (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
      (ix.hiB p.b) base bit k (ix.loB p.b) #[]
  else lookupPW ix G R s p base bit

theorem lookupPWk_extract (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit k : Nat) :
    (lookupPWk ix G R s p base bit k).extract 0 k = (lookupPW ix G R s p base bit).extract 0 k := by
  rw [lookupPW_eqK]
  unfold lookupPWk lookupPWK
  simp only []
  split
  · exact scanAWKk_extract _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
  · rw [lookupPW_eqK]; unfold lookupPWK; simp only []; rw [if_neg (by assumption)]

/-- A result shorter than `k` is the whole result. -/
theorem scanAWKk_small (ix : MzIdx) (G : PGen) (R : ByteArray) (rc : UInt64) (rok : Bool) (kb keyU : UInt64)
    (s o key bw aw pmo o2 n1 a2 n2 hi base bit k : Nat) : ∀ n t (acc : Array Nat), hi - t = n →
    (scanAWKk ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit k t acc).size < k →
    scanAWKk ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit k t acc =
      scanAWK ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t acc hn hs
    rw [scanAWKk] at hs ⊢
    split
    · rename_i h
      rw [if_pos h] at hs
      rcases h with h | h
      · omega
      · rw [scanAWK.eq_def, if_neg (by omega)]
    · rename_i h
      rw [if_neg h] at hs
      rw [ih (hi - min hi (t + 256)) (by omega) _ _ rfl hs,
        scanAWK_split ix G R rc rok kb keyU s o key bw aw pmo o2 n1 a2 n2 hi base bit (min hi (t + 256))
          (Nat.min_le_left _ _) _ t acc rfl, show max t (min hi (t + 256)) = min hi (t + 256) by omega]

theorem lookupPWk_small (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit k : Nat)
    (h : (lookupPWk ix G R s p base bit k).size < k) :
    lookupPWk ix G R s p base bit k = lookupPW ix G R s p base bit := by
  rw [lookupPW_eqK]
  unfold lookupPWk at h ⊢
  unfold lookupPWK
  simp only [] at h ⊢
  split
  · rename_i hc
    rw [if_pos hc] at h
    exact scanAWKk_small _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl h
  · rw [lookupPW_eqK]; unfold lookupPWK; simp only []; rw [if_neg (by assumption)]

end MzWU


/-! ## Proofs -/

theorem seedLE_spec (R : ByteArray) (j k : Nat) (hk : k ≤ 32) :
    ∀ n i w ok, k - i = n → i ≤ k → w.toNat = wv R j i →
      (ok = true → ∀ t, t < i → acgt (R.get! (j + t)) = true) →
      (seedLE R j k i w ok).2 = true →
      ∀ t, t < k → acgt (R.get! (j + t)) = true ∧ dig (seedLE R j k i w ok).1.toNat t = c2N (R.get! (j + t)) := by
  intro n
  induction n with
  | zero =>
    intro i w ok hn hi hw hok hr t ht
    have e : i = k := by omega
    subst e
    rw [seedLE, if_neg (by omega)] at hr ⊢
    exact ⟨hok hr t ht, by rw [hw, wv_dig _ _ _ _ ht]⟩
  | succ n ih =>
    intro i w ok hn hi hw hok hr t ht
    have hik : i < k := by omega
    rw [seedLE, if_pos hik] at hr ⊢
    have hs : ((2 * i).toUInt64).toNat = 2 * i := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    have hstep := step_toNat w (2 * i).toUInt64 i (R.get! (j + i)) (by omega) hs
      (by rw [hw]; exact wv_lt _ _ _)
    refine ih (i + 1) _ _ (by omega) (by omega) ?_ ?_ hr t ht
    · rw [hstep, wv, hw]
    · intro h t' ht'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases e : t' = i
      · subst e; simpa [acgt] using h.2
      · exact hok h.1 t' (by omega)

theorem seedLE_ok (R : ByteArray) (s : Nat) (h : (seedLE R s Mz.q 0 0 true).2 = true) :
    ∀ t, t < Mz.q → acgt (R.get! (s + t)) = true ∧
      dig (seedLE R s Mz.q 0 0 true).1.toNat t = c2N (R.get! (s + t)) :=
  seedLE_spec R s Mz.q (by decide) _ 0 0 true rfl (Nat.zero_le _) rfl (fun _ t ht => by omega) h

theorem gW_dig (P : PGen) (G : ByteArray) (hP : Rep P G) (p t : Nat) (ht : t < 32) (hin : p + t < P.n)
    (hfl : P.w.get! (17 * ((P.o + (p + t)) / 64)) = 1) :
    dig (gW P p).toNat t = (P.code (P.o + p + t)).toNat ∧ G.get! (p + t) = letter (P.code (P.o + p + t)) := by
  refine ⟨?_, ?_⟩
  · unfold gW
    rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) ht]
    split
    · rw [code_dig _ _ _ (by omega)]; congr 2; omega
    · rw [code_dig _ _ _ (by omega)]; congr 2; omega
  · rw [← hP.2, PGen.get, if_pos hin, raw_eq, Nat.shiftRight_eq_div_pow, hfl,
      show P.o + (p + t) = P.o + p + t by omega]
    rfl

theorem gW_xor (P : PGen) (G R : ByteArray) (hP : Rep P G) (rc : UInt64) (s p : Nat)
    (hr : ∀ t, t < Mz.q → acgt (R.get! (s + t)) = true ∧ dig rc.toNat t = c2N (R.get! (s + t)))
    (hw : winOk P p Mz.q = true) (t : Nat) (ht : t < Mz.q) :
    dig (gW P p ^^^ rc).toNat t = 0 ↔ G.get! (p + t) = R.get! (s + t) := by
  obtain ⟨hn, hf⟩ := winOk_flags P p Mz.q hw
  have hq : Mz.q = 25 := rfl
  obtain ⟨g1, g2⟩ := gW_dig P G hP p t (by omega) (by omega) (hf (p + t) (by omega) (by omega))
  obtain ⟨r1, r2⟩ := hr t ht
  have hc : (P.code (P.o + p + t)).toNat < 4 := by
    unfold PGen.code
    rw [UInt8.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [xor_dig, g1, r2, g2]
  exact eq_comm.trans (eq_comm.trans (letter_iff _ _ r1 hc)).symm

theorem eqW_iff (x : UInt64) (a n : Nat) (ha : a < 32) (han : a + n ≤ 32) :
    eqW x a n = true ↔ ∀ t, t < n → dig x.toNat (a + t) = 0 := by
  unfold eqW
  rw [beq_iff_eq]
  have hK : ((2 * a).toUInt64).toNat = 2 * a := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  constructor
  · intro h t ht
    have := lowF_dig (x >>> (2 * a).toUInt64) n t (by omega)
    rw [h, if_pos ht, shr_dig _ _ a _ hK (by omega)] at this
    rw [Nat.add_comm]; exact this.symm.trans (by simp [dig])
  · intro h
    apply UInt64.toNat_inj.mp
    apply eq_of_dig 32 _ _ (UInt64.toNat_lt _) (by decide)
    intro t ht
    rw [lowF_dig _ _ _ ht]
    split
    · rw [shr_dig _ _ a _ hK (by omega), Nat.add_comm, h t ‹_›]; simp [dig]
    · simp [dig]

theorem eqW_run (P : PGen) (G R : ByteArray) (hP : Rep P G) (rc : UInt64) (s p : Nat)
    (hr : ∀ t, t < Mz.q → acgt (R.get! (s + t)) = true ∧ dig rc.toNat t = c2N (R.get! (s + t)))
    (hw : winOk P p Mz.q = true) (a n i j : Nat) (han : a + n ≤ Mz.q) (hi : i = p + a) (hj : j = s + a) :
    eqW (gW P p ^^^ rc) a n = eqRunP P R i j n := by
  have hq : Mz.q = 25 := rfl
  apply Bool.eq_iff_iff.mpr
  rw [eqW_iff _ _ _ (by omega) (by omega), eqRunP_eqMz hP, Mz.eqRun_iff]
  constructor
  · intro h t ht
    have := (gW_xor P G R hP rc s p hr hw (a + t) (by omega)).mp (h t ht)
    rw [hi, hj, Nat.add_assoc, Nat.add_assoc]; exact this
  · intro h t ht
    apply (gW_xor P G R hP rc s p hr hw (a + t) (by omega)).mpr
    have := h t ht
    rw [hi, hj, Nat.add_assoc, Nat.add_assoc] at this; exact this

section
open Mz

theorem okAtW_eq (ix : MzIdx) (P : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) :
    okAtW ix P R (seedLE R s Mz.q 0 0 true).1 (seedLE R s Mz.q 0 0 true).2 s o key bw aw pmo o2 n1 a2 n2 t =
      okAtP ix P R s o key bw aw pmo o2 n1 a2 n2 t := by
  have hP := rep_unpack P
  unfold okAtW
  simp only []
  split
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hok, hop⟩, hn1⟩, hn2⟩, hk⟩, hw⟩ := hc
    have hr := seedLE_ok R s hok
    have hn := (winOk_flags P _ _ hw).1
    have e0 := fun a n i j han hi hj =>
      eqW_run P (unpack P) R hP (seedLE R s Mz.q 0 0 true).1 s (ix.posOf (ix.slot t) - o) hr hw a n i j han hi hj
    unfold okAtP
    simp only [hop, decide_true, Bool.true_and, show ix.posOf (ix.slot t) - o + Mz.q ≤ P.n from hn]
    split
    · rw [e0 0 n1 (ix.posOf (ix.slot t) - o) s (by omega) (by omega) (by omega),
        e0 (o + a2) n2 (ix.posOf (ix.slot t) + a2) (s + o + a2) (by omega) (by omega) (by omega),
        e0 o ix.k (ix.posOf (ix.slot t)) (s + o) (by omega) (by omega) rfl]
      simp only [Bool.and_true]
    · rw [e0 0 Mz.q (ix.posOf (ix.slot t) - o) s (by omega) (by omega) (by omega)]
  · cases hkey : (ix.slot t &&& ix.kbM) == key
    · unfold okAtP; simp only [hkey, Bool.false_and]
    · rfl

theorem scanAW_eq (ix : MzIdx) (P : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ d t acc, hi - t = d →
      scanAW ix P R (seedLE R s Mz.q 0 0 true).1 (seedLE R s Mz.q 0 0 true).2 s o key bw aw pmo o2 n1 a2 n2 hi
        base bit t acc = scanAP ix P R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanAW scanAP; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro t acc hd
    unfold scanAW scanAP
    have ih' := fun acc => ih (t + 1) acc (by omega)
    simp only [show t < hi from by omega, if_true, okAtW_eq, ih']

theorem lookupPW_eq (ix : MzIdx) (P : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) :
    lookupPW ix P R s p base bit = lookupPP ix P R s p base bit := by
  unfold lookupPW lookupPP
  exact scanAW_eq ix P R s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl

end

end MapSpec.Fast

#print axioms MapSpec.Fast.okAtW_eq
#print axioms MapSpec.Fast.lookupPW_eq
