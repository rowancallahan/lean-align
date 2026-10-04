import AlignmentWfaU32Step

/-!
# Equal penalties: the X and Y fronts come from the M front alone

When `pe = po`, the X source (`frontAtR hist pe (·.xf)`) and the M source
(`frontAtR hist po (·.mf)`) are the X and M fronts of the same level.  Every
level `nextLevelR` builds (and the seed) has `xf ≤ mf` and `yf ≤ mf`
pointwise on codes, `pushXR`/`pushYR` are monotone in the code, and
`betterR a b = b` when `a ≤ b`; so the `betterR` of the two pushes collapses
to the push of the M source.  A kernel with equal penalties may therefore
skip the X/Y source reads and push the M front only.

Side conditions found: `pushXR_mono` needs none; `pushYR_mono` needs
`1 ≤ t` (at `t = 0`, code `m + 1` pushes to `0` while code `m` pushes to
`m + 1`); the `*_single` lemmas need only the pointwise `≤` (no code bound).
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity of the pushes; bounds on betterR / extR
-- ══════════════════════════════════════════════════════════════════

/-- `pushXR` is monotone in the code (no bound on the code needed). -/
theorem pushXR_mono (m n t a b : Nat) (hab : a ≤ b) :
    pushXR m n t a ≤ pushXR m n t b := by
  simp only [pushXR, joffOf]
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;>
    by_cases h3 : a - 1 + t - m < n <;> by_cases h4 : b - 1 + t - m < n <;>
    by_cases h5 : 1 ≤ a - 1 ∧ 1 ≤ a - 1 + t - m <;>
    by_cases h6 : 1 ≤ b - 1 ∧ 1 ≤ b - 1 + t - m <;>
    simp only [h1, h2, h3, h4, h5, h6, if_true, if_false, and_self] <;>
    omega

/-- `pushYR` is monotone in the code on diagonals `t ≥ 1` (no bound on the
code needed).  The condition is necessary: at `t = 0`, `m ≥ 1`,
`pushYR m n 0 m = m + 1` but `pushYR m n 0 (m + 1) = 0`. -/
theorem pushYR_mono (m n t a b : Nat) (hab : a ≤ b) (ht : 1 ≤ t) :
    pushYR m n t a ≤ pushYR m n t b := by
  simp only [pushYR, joffOf]
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;>
    by_cases h3 : a - 1 < m <;> by_cases h4 : b - 1 < m <;>
    by_cases h5 : 1 ≤ a - 1 ∧ 1 ≤ a - 1 + t - m <;>
    by_cases h6 : 1 ≤ b - 1 ∧ 1 ≤ b - 1 + t - m <;>
    simp only [h1, h2, h3, h4, h5, h6, if_true, if_false, and_self] <;>
    omega

theorem betterR_left_le (a b : Nat) : a ≤ betterR a b := by
  unfold betterR; split <;> omega

theorem betterR_right_le (a b : Nat) : b ≤ betterR a b := by
  unfold betterR; split <;> omega

theorem betterR_eq_right (a b : Nat) (h : a ≤ b) : betterR a b = b := by
  unfold betterR; split <;> omega

theorem le_extR (m : Nat) (xa ya : Array Char) (t a : Nat) : a ≤ extR m xa ya t a := by
  simp only [extR]
  split <;> omega

-- ══════════════════════════════════════════════════════════════════
-- Single-source pushes
-- ══════════════════════════════════════════════════════════════════

/-- With the X source below the M source pointwise, the X point is the push
of the M source alone. -/
theorem pointX_single (m n : Nat) (xf mf : RFront) (hle : ∀ t, rget xf t ≤ rget mf t)
    (t : Nat) :
    pointX m n xf mf t = if t = 0 then 0 else pushXR m n (t - 1) (rget mf (t - 1)) := by
  by_cases h : t = 0
  · simp only [pointX, h, if_true]
  · simp only [pointX, h, if_false]
    exact betterR_eq_right _ _ (pushXR_mono m n (t - 1) _ _ (hle (t - 1)))

/-- With the Y source below the M source pointwise, the Y point is the push
of the M source alone (the diagonal argument `t + 1` is `≥ 1`). -/
theorem pointY_single (m n len : Nat) (yf mf : RFront) (hle : ∀ t, rget yf t ≤ rget mf t)
    (t : Nat) :
    pointY m n len yf mf t =
      if t + 1 < len then pushYR m n (t + 1) (rget mf (t + 1)) else 0 := by
  by_cases h : t + 1 < len
  · simp only [pointY, h, if_true]
    exact betterR_eq_right _ _ (pushYR_mono m n (t + 1) _ _ (hle (t + 1)) (by omega))
  · simp only [pointY, h, if_false]

-- ══════════════════════════════════════════════════════════════════
-- Every level has X ≤ M and Y ≤ M pointwise
-- ══════════════════════════════════════════════════════════════════

/-- The M front of a `nextLevelP` level, read at `t`, is `pointM` of its own
X and Y fronts. -/
theorem rget_nextLevelP_mf (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) (t : Nat) :
    rget (nextLevelP m n xa ya len pe po px hist).mf t =
      pointM m n xa ya (frontAtR hist px (·.mf))
        (nextLevelP m n xa ya len pe po px hist).xf
        (nextLevelP m n xa ya len pe po px hist).yf t := by
  simp only [nextLevelP, packPointM_eq]
  rw [← pointM_eq]

theorem nextLevelR_xf_le_mf (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) (t : Nat) :
    rget (nextLevelR m n xa ya len pe po px hist).xf t ≤
      rget (nextLevelR m n xa ya len pe po px hist).mf t := by
  rw [← nextLevelP_eq, rget_nextLevelP_mf]
  unfold pointM
  exact Nat.le_trans (betterR_right_le _ _)
    (Nat.le_trans (betterR_left_le _ _) (le_extR _ _ _ _ _))

theorem nextLevelR_yf_le_mf (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) (t : Nat) :
    rget (nextLevelR m n xa ya len pe po px hist).yf t ≤
      rget (nextLevelR m n xa ya len pe po px hist).mf t := by
  rw [← nextLevelP_eq, rget_nextLevelP_mf]
  unfold pointM
  exact Nat.le_trans (betterR_right_le _ _) (le_extR _ _ _ _ _)

theorem rget_empty (lo t : Nat) : rget ⟨lo, #[]⟩ t = 0 := by
  simp [rget]

theorem seedR_xf_le_mf (m len : Nat) (xa ya : Array Char) (t : Nat) :
    rget (seedR m len xa ya).xf t ≤ rget (seedR m len xa ya).mf t := by
  simp only [seedR, rget_empty]
  exact Nat.zero_le _

theorem seedR_yf_le_mf (m len : Nat) (xa ya : Array Char) (t : Nat) :
    rget (seedR m len xa ya).yf t ≤ rget (seedR m len xa ya).mf t := by
  simp only [seedR, rget_empty]
  exact Nat.zero_le _

end AlignmentSpec.U32Proof

#print axioms AlignmentSpec.U32Proof.pushXR_mono
#print axioms AlignmentSpec.U32Proof.pushYR_mono
#print axioms AlignmentSpec.U32Proof.betterR_left_le
#print axioms AlignmentSpec.U32Proof.betterR_right_le
#print axioms AlignmentSpec.U32Proof.le_extR
#print axioms AlignmentSpec.U32Proof.pointX_single
#print axioms AlignmentSpec.U32Proof.pointY_single
#print axioms AlignmentSpec.U32Proof.nextLevelR_xf_le_mf
#print axioms AlignmentSpec.U32Proof.nextLevelR_yf_le_mf
#print axioms AlignmentSpec.U32Proof.seedR_xf_le_mf
#print axioms AlignmentSpec.U32Proof.seedR_yf_le_mf
