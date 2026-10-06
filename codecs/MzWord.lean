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

end MzW

/-! ## The key test on `UInt64` slots (compiled in place of `lookupPW`: `lookupPW_eqK`) -/

section MzWU
open Mz

/-- Slot `t` before its `toNat` (`slot_eqW`). -/
@[inline] def slotW (B : ByteArray) (sw t : Nat) : UInt64 :=
  let j := sw * t
  if sw = 4 then rd4 B j
  else if sw = 5 then rd4 B j ||| byteAt B (j + 4) 32
  else if sw = 6 then rd4 B j ||| byteAt B (j + 4) 32 ||| byteAt B (j + 5) 40
  else rd4 B j ||| (rd4 B (j + 4) <<< 32)

theorem slot_eqW (ix : MzIdx) (t : Nat) : ix.slot t = (slotW ix.sl ix.sw t).toNat := rfl

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
