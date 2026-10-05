import FastGenShort

/-!
# Batched seed scan for short reads

`scanL` scans a chromosome once per seed.  `batchScan` scans it once for a
batch of seeds whose first `K = 12` letters are ACGT: a rolling 2-bit code of the
last 12 genome letters (`roll`, invariant `RollOk`), a 4^12-byte table of the
seeds' prefix codes, and a binary search in the sorted keys `code·S + sid`; each
candidate is verified letter by letter.  The result for every seed is exactly
`scanL` (`batchScan_eq`), so the short-read proofs apply unchanged.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Codes of ACGT words -/

/-- 2-bit value of a letter; `4` = not ACGT. -/
@[inline] def acgtV (b : UInt8) : Nat :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

theorem acgtV_le (b : UInt8) : acgtV b ≤ 4 := by unfold acgtV; split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- Code of `A[p, p+k)` (first letter most significant), if all ACGT. -/
def codeW (A : ByteArray) (p : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => match codeW A p k with
    | some c => if acgtV (A.get! (p + k)) < 4 then some (c * 4 + acgtV (A.get! (p + k))) else none
    | none => none

/-- Equal letters, equal codes. -/
theorem codeW_congr (A B : ByteArray) (p s : Nat) : ∀ k, (∀ i, i < k → A.get! (p + i) = B.get! (s + i)) →
    codeW A p k = codeW B s k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [codeW]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem codeW_some (A : ByteArray) (p : Nat) : ∀ k, (∀ i, i < k → acgtV (A.get! (p + i)) < 4) →
    ∃ c, codeW A p k = some c ∧ c < 4 ^ k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, rfl, by simp⟩
  | succ k ih =>
    intro h
    obtain ⟨c, hc, hlt⟩ := ih (fun i hi => h i (by omega))
    have hv := h k (by omega)
    refine ⟨c * 4 + acgtV (A.get! (p + k)), by simp only [codeW, hc, if_pos hv], ?_⟩
    rw [Nat.pow_succ]; omega

theorem codeW_acgt (A : ByteArray) (p : Nat) : ∀ k c, codeW A p k = some c →
    ∀ i, i < k → acgtV (A.get! (p + i)) < 4 := by
  intro k
  induction k with
  | zero => intro c _ i hi; omega
  | succ k ih =>
    intro c h i hi
    simp only [codeW] at h
    cases hk : codeW A p k with
    | none => rw [hk] at h; cases h
    | some c' =>
      rw [hk] at h
      simp only [] at h
      split at h
      · next hv =>
        by_cases e : i = k
        · subst e; exact hv
        · exact ih c' hk i (by omega)
      · cases h

/-! ## The rolling code -/

def K12 : Nat := 12

/-- After letter `x`: `c` = code of the last `min r K` letters (mod `4^K`), `r` = the
length of the ACGT run ending at `x` (capped at `K`). -/
@[inline] def roll (G : ByteArray) (x : Nat) (st : Nat × Nat) : Nat × Nat :=
  let v := acgtV (G.get! x)
  if v < 4 then ((st.1 * 4 + v) % 4 ^ K12, min (st.2 + 1) K12) else (0, 0)

/-- The state after the letters `[0, x)`. -/
structure RollOk (G : ByteArray) (x : Nat) (st : Nat × Nat) : Prop where
  le : st.2 ≤ K12
  le_x : st.2 ≤ x
  code : ∀ r, r ≤ st.2 → codeW G (x - r) r = some (st.1 % 4 ^ r)
  run : ∀ r, r ≤ K12 → r ≤ x → (∀ i, i < r → acgtV (G.get! (x - r + i)) < 4) → r ≤ st.2

theorem rollOk_zero (G : ByteArray) : RollOk G 0 (0, 0) :=
  ⟨by unfold K12; omega, Nat.le_refl _, fun r hr => by
    have : r = 0 := by simpa using hr
    subst this; rfl, fun r _ hr _ => by omega⟩

theorem mod_step (c v r : Nat) (hv : v < 4) : (c * 4 + v) % 4 ^ (r + 1) = c % 4 ^ r * 4 + v := by
  rw [Nat.pow_succ]
  have h4 : 0 < 4 ^ r := Nat.pow_pos (by decide : (0 : Nat) < 4)
  rw [Nat.mul_comm (4 ^ r) 4]
  have e : c * 4 + v = (c % 4 ^ r * 4 + v) + (c / 4 ^ r) * (4 * 4 ^ r) := by
    have := Nat.div_add_mod c (4 ^ r)
    have : c * 4 = (4 ^ r * (c / 4 ^ r) + c % 4 ^ r) * 4 := by rw [this]
    rw [this]
    rw [Nat.add_mul, Nat.mul_comm (4 ^ r) (c / 4 ^ r), Nat.mul_assoc, Nat.mul_comm (4 ^ r) 4]
    omega
  rw [e, Nat.add_mul_mod_self_right]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt c h4
  have : c % 4 ^ r * 4 + v < (c % 4 ^ r + 1) * 4 := by omega
  have : (c % 4 ^ r + 1) * 4 ≤ 4 * 4 ^ r := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem rollOk_step (G : ByteArray) (x : Nat) (st : Nat × Nat) (h : RollOk G x st) :
    RollOk G (x + 1) (roll G x st) := by
  obtain ⟨hle, hlx, hcode, hrun⟩ := h
  unfold roll
  dsimp only
  have hK : K12 = 12 := rfl
  split
  · next hv =>
    refine ⟨by simp only; omega, by simp only; omega, fun r hr => ?_, fun r hr hrx hall => ?_⟩
    · simp only at hr
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp [codeW, Nat.mod_one]
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hc := hcode r' (by omega)
        have e : x + 1 - (r' + 1) = x - r' := by omega
        rw [e]
        simp only [codeW, hc]
        have e2 : x - r' + r' = x := by omega
        rw [e2, if_pos hv]
        congr 1
        rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 4 (by omega : r' + 1 ≤ K12)), mod_step _ _ _ hv]
    · simp only
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · omega
      · have := hrun (r - 1) (by omega) (by omega) (fun i hi => by
          have := hall i (by omega)
          rwa [show x + 1 - r + i = x - (r - 1) + i by omega] at this)
        omega
  · next hv =>
    refine ⟨by simp only; unfold K12; omega, by simp only; omega, fun r hr => ?_, fun r hr hrx hall => ?_⟩
    · simp only at hr
      have : r = 0 := by omega
      subst this; rfl
    · simp only
      apply Classical.byContradiction; intro hne
      have := hall (r - 1) (by omega)
      rw [show x + 1 - r + (r - 1) = x by omega] at this
      exact hv this

end MapSpec.Fast
