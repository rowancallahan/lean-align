import MapperFastScore
import MapperBandKernel

/-!
Window penalties at byte level.

`penB R G st len` is the penalty (scoring (0, −4, −6, −2), `T = −12`, 13 = no
hit) of the read `R` against the window `G[st, st+len)` of chromosome `G`,
written with mismatch counts over byte ranges (`cntP`), the form the fast
kernels compute.  `penB_eq` : for byte strings that spell the read and the
chromosome (`Encodes`), `penB` is the specification's window penalty.
-/

namespace MapSpec

open AlignmentSpec

/-- Number of `k ∈ [i, i+m)` with `p k`. -/
def cntP (p : Nat → Bool) (i : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => (if p i then 1 else 0) + cntP p (i + 1) m

theorem cntP_add (p : Nat → Bool) (i a b : Nat) : cntP p i (a + b) = cntP p i a + cntP p (i + a) b := by
  induction a generalizing i with
  | zero => simp [cntP]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, cntP, cntP, ih (i + 1)]
    rw [show i + 1 + a = i + (a + 1) by omega]; omega

theorem cntP_congr (p p' : Nat → Bool) (i m : Nat) (h : ∀ k, i ≤ k → k < i + m → p k = p' k) :
    cntP p i m = cntP p' i m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [cntP]
    rw [h i (by omega) (by omega), ih (i + 1) (fun k h1 h2 => h k (by omega) (by omega))]

theorem cntP_shift (p : Nat → Bool) (i j m : Nat) : cntP (fun k => p (i + k)) j m = cntP p (i + j) m := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp only [cntP]; rw [ih (j + 1), show i + (j + 1) = i + j + 1 by omega]

theorem cntP_le (p : Nat → Bool) (i m : Nat) : cntP p i m ≤ m := by
  induction m generalizing i with
  | zero => simp [cntP]
  | succ m ih => simp only [cntP]; have := ih (i + 1); split <;> omega

theorem cntP_eq_zero (p : Nat → Bool) (i m : Nat) (h : cntP p i m = 0) (k : Nat) (h1 : i ≤ k)
    (h2 : k < i + m) : p k = false := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    simp only [cntP] at h
    by_cases hk : k = i
    · subst hk; cases hp : p k <;> simp_all
    · exact ih (i + 1) (by omega) (by omega) (by omega)

theorem cntP_zero_of (p : Nat → Bool) (i m : Nat) (h : ∀ k, i ≤ k → k < i + m → p k = false) :
    cntP p i m = 0 := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [cntP]; rw [h i (by omega) (by omega), ih (i + 1) (fun k h1 h2 => h k (by omega) (by omega))]
    rfl

theorem cntP_mono (p : Nat → Bool) (i m i' m' : Nat) (h1 : i ≤ i') (h2 : i' + m' ≤ i + m) :
    cntP p i' m' ≤ cntP p i m := by
  have e : m = (i' - i) + (m' + (i + m - i' - m')) := by omega
  rw [e, cntP_add, cntP_add, show i + (i' - i) = i' by omega]
  omega

/-- `hamming` is a count over positions. -/
theorem hamming_cnt (u v : List Char) (f : Nat → Bool)
    (hf : ∀ k (h1 : k < u.length) (h2 : k < v.length), f k = decide (u[k] ≠ v[k])) :
    hamming u v = cntP f 0 (min u.length v.length) := by
  induction u generalizing v f with
  | nil => simp [hamming, cntP]
  | cons x u ih =>
    cases v with
    | nil => simp [hamming, cntP]
    | cons y v =>
      rw [List.length_cons, List.length_cons, Nat.min_def]
      have hm : (if u.length + 1 ≤ v.length + 1 then u.length + 1 else v.length + 1) =
          min u.length v.length + 1 := by rw [Nat.min_def]; split <;> split <;> omega
      rw [hm, cntP, hamming, ih v (fun k => f (k + 1)) (fun k h1 h2 => by
        have := hf (k + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact this)]
      rw [← cntP_shift f 1 0]
      have h0 := hf 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [h0]
      congr 1
      · by_cases hxy : x = y <;> simp [hxy]
      · apply cntP_congr; intro k _ _; rw [Nat.add_comm]

/-! ## The byte-level penalty -/

/-- Mismatches of `R[0, i)` against `G[st ..]`. -/
def preB (R G : ByteArray) (st i : Nat) : Nat := cntP (fun k => R.get! k != G.get! (st + k)) 0 i

/-- Mismatches of `R[j, n)` against the end diagonal of window `(st, len)`. -/
def sufB (R G : ByteArray) (st len j : Nat) : Nat :=
  cntP (fun k => R.get! k != G.get! (st + len + k - R.size)) j (R.size - j)

/-- Mismatches with the gap at read position `i` (read letters `i ..< i+skip` deleted). -/
def misB (R G : ByteArray) (st len skip i : Nat) : Nat := preB R G st i + sufB R G st len (i + skip)

/-- Gap length of a window of length `len`. -/
def gapLen (n len : Nat) : Nat := if n < len then len - n else n - len

/-- Read letters deleted by the gap. -/
def skipOf (n len : Nat) : Nat := if len < n then n - len else 0

/-- Least mismatch count over the gap positions. -/
def minMis (R G : ByteArray) (st len : Nat) : Nat :=
  minUpTo (misB R G st len (skipOf R.size len)) (R.size - skipOf R.size len)

def penSame (R G : ByteArray) (st : Nat) : Nat :=
  if preB R G st R.size ≤ 3 then 4 * preB R G st R.size else 13

def penGap (R G : ByteArray) (st len : Nat) : Nat :=
  if 6 + 2 * gapLen R.size len + 4 * minMis R G st len ≤ 12
  then 6 + 2 * gapLen R.size len + 4 * minMis R G st len else 13

/-- Penalty of the read against window `(st, len)` of `G` (13 = not a hit). -/
def penB (R G : ByteArray) (st len : Nat) : Nat :=
  if st + len ≤ G.size then
    if len = R.size then penSame R G st
    else if gapLen R.size len ≤ 3 then penGap R G st len
    else 13
  else 13

/-! ## `penB` is the specification's penalty -/

theorem neq_bytes {R G : ByteArray} {xs seq : List Char} (hr : Encodes R xs) (hg : Encodes G seq)
    (k j : Nat) (hk : k < xs.length) (hj : j < seq.length) :
    (R.get! k != G.get! j) = decide (xs[k] ≠ seq[j]) := by
  have := Encodes.beq_iff hr hg k j hk hj
  simp only [bne, this]
  by_cases h : xs[k] = seq[j] <;> simp [h]

theorem minUpTo_congr (f f' : Nat → Nat) (k : Nat) (h : ∀ i, i ≤ k → f i = f' i) :
    minUpTo f k = minUpTo f' k := by
  induction k with
  | zero => simp [minUpTo, h 0 (Nat.le_refl _)]
  | succ k ih => simp only [minUpTo]; rw [ih (fun i hi => h i (by omega)), h (k + 1) (Nat.le_refl _)]

theorem penB_eq_penL (R G : ByteArray) (xs seq : List Char) (hr : Encodes R xs) (hg : Encodes G seq)
    (st len : Nat) (hfit : st + len ≤ seq.length) :
    penL xs ((seq.drop st).take len) = penB R G st len := by
  have hn : R.size = xs.length := hr.1
  have hG : G.size = seq.length := hg.1
  generalize hys : (seq.drop st).take len = ys
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  -- prefix mismatches
  have hpre : ∀ i, i ≤ xs.length → i ≤ len →
      hamming (xs.take i) (ys.take i) = preB R G st i := by
    intro i h1 h2
    unfold preB
    rw [hamming_cnt _ _ (fun k => R.get! k != G.get! (st + k)) (fun k h1' h2' => by
      simp only [List.getElem_take]
      rw [neq_bytes hr hg k (st + k) (by simp at h1'; omega) (by simp at h2'; omega), hyk k (by simp at h2'; omega)])]
    congr 1; simp; omega
  unfold penB
  rw [if_pos (by omega)]
  by_cases hsame : len = R.size
  · rw [if_pos hsame, penL_same xs ys (by omega)]
    have := hpre xs.length (Nat.le_refl _) (by omega)
    rw [List.take_length, List.take_of_length_le (by omega)] at this
    unfold penSame
    rw [this, hn]
  rw [if_neg hsame]
  by_cases hfar : gapLen R.size len ≤ 3
  · rw [if_pos hfar]
    unfold penGap minMis gapLen skipOf at *
    by_cases hlt : R.size < len
    · -- insertion
      simp only [hlt, if_true, show ¬ len < R.size by omega, if_false] at hfar ⊢
      rw [penL_ins xs ys (len - R.size) (by omega) (by omega) (by omega)]
      have hM : minUpTo (misIns xs ys (len - R.size)) xs.length =
          minUpTo (misB R G st len 0) (R.size - 0) := by
        rw [Nat.sub_zero, hn]
        apply minUpTo_congr
        intro i hi
        unfold misIns misB
        rw [hpre i hi (by omega), Nat.add_zero]
        congr 1
        unfold sufB
        rw [hamming_cnt _ _ (fun k => R.get! (i + k) != G.get! (st + len + (i + k) - R.size)) (fun k h1 h2 => by
          simp only [List.getElem_drop]
          simp at h1 h2
          rw [neq_bytes hr hg (i + k) (st + len + (i + k) - R.size) (by omega) (by omega),
            hyk _ (by omega)]
          have e : st + (i + (len - xs.length) + k) = st + len + (i + k) - R.size := by omega
          simp only [e])]
        rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) i 0]
        congr 1 <;> simp <;> omega
      rw [hM]
    · -- deletion
      have hlt' : len < R.size := by omega
      simp only [hlt, hlt', if_true, if_false] at hfar ⊢
      rw [penL_del xs ys (R.size - len) (by omega) (by omega) (by omega)]
      have hM : minUpTo (misDel xs ys (R.size - len)) ys.length =
          minUpTo (misB R G st len (R.size - len)) (R.size - (R.size - len)) := by
        rw [show R.size - (R.size - len) = ys.length by omega]
        apply minUpTo_congr
        intro i hi
        unfold misDel misB
        rw [hpre i (by omega) (by omega)]
        congr 1
        unfold sufB
        rw [hamming_cnt _ _ (fun k => R.get! (i + (R.size - len) + k) !=
            G.get! (st + len + (i + (R.size - len) + k) - R.size)) (fun k h1 h2 => by
          simp only [List.getElem_drop]
          simp at h1 h2
          rw [neq_bytes hr hg _ _ (by omega) (by omega), hyk (i + k) (by omega)]
          have e : st + (i + k) = st + len + (i + (R.size - len) + k) - R.size := by omega
          simp only [e])]
        rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + (R.size - len)) 0]
        congr 1 <;> simp <;> omega
      rw [hM]
  · rw [if_neg hfar]
    unfold gapLen at hfar
    exact penL_far xs ys (by split at hfar <;> omega)

end MapSpec

#print axioms MapSpec.penB_eq_penL
