import MapperDefs
import MapperWalk
import MapperLists

/-! Gapless (all-diagonal) alignments: their score is a Hamming count, any
walk with a gap pays at least `gapOpen + gapExtend`, and a gapless walk
scoring at least `T` has a clean seed at exactly its own offset. -/

namespace MapSpec

open AlignmentSpec

/-- Positions (up to the shorter length) where the two lists differ. -/
def hamming : List Char → List Char → Nat
  | x :: xs, y :: ys => (if x = y then 0 else 1) + hamming xs ys
  | _, _ => 0

/-- Positions (up to the shorter length) where the two lists agree. -/
def agree : List Char → List Char → Nat
  | x :: xs, y :: ys => (if x = y then 1 else 0) + agree xs ys
  | _, _ => 0

/-- Score of the all-diagonal walk of two equal-length lists. -/
def gaplessScore (sc : Scoring) (xs ys : List Char) : Int :=
  sc.matchScore * ((xs.length - hamming xs ys : Nat) : Int) + sc.mismatchScore * (hamming xs ys : Int)

/-- The gap penalty of a single gap column that opens a run. -/
def gapCost1 (sc : Scoring) : Int := sc.gapOpen + sc.gapExtend

theorem agree_add_hamming (xs ys : List Char) (h : xs.length = ys.length) :
    agree xs ys + hamming xs ys = xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [agree, hamming]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have := ih ys (by simpa using h)
      simp only [agree, hamming, List.length_cons]
      split <;> omega

theorem scoreWalk_diags_counts (sc : Scoring) (xs ys : List Char) (prev : Option Step)
    (h : xs.length = ys.length) :
    scoreWalk sc (List.replicate xs.length .diag) xs ys prev =
      sc.matchScore * (agree xs ys : Int) + sc.mismatchScore * (hamming xs ys : Int) := by
  induction xs generalizing ys prev with
  | nil => cases ys <;> simp_all [scoreWalk, agree, hamming]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have := ih ys (some .diag) (by simpa using h)
      simp only [List.length_cons, List.replicate_succ, scoreWalk, agree, hamming, this]
      by_cases hxy : x = y
      · simp only [hxy, if_true]; push_cast; simp only [Int.mul_add, Int.mul_zero, Int.mul_one]; omega
      · simp only [hxy, if_false]; push_cast; simp only [Int.mul_add, Int.mul_zero, Int.mul_one]; omega

/-- **Gapless score.**  For lists of equal length the all-diagonal walk scores
`matchScore × (n − hamming) + mismatchScore × hamming`. -/
theorem walkScore_diags (sc : Scoring) (xs ys : List Char) (h : xs.length = ys.length) :
    walkScore sc xs ys (List.replicate xs.length .diag) = gaplessScore sc xs ys := by
  unfold walkScore gaplessScore
  rw [scoreWalk_diags_counts sc xs ys none h]
  have := agree_add_hamming xs ys h
  have : agree xs ys = xs.length - hamming xs ys := by omega
  rw [this]

/-- With `matchScore = 0` the gapless score is `mismatchScore × hamming`. -/
theorem gaplessScore_match_zero (sc : Scoring) (hm : sc.matchScore = 0) (xs ys : List Char) :
    gaplessScore sc xs ys = sc.mismatchScore * (hamming xs ys : Int) := by
  simp [gaplessScore, hm]

theorem diags_isMonotoneWalk (xs ys : List Char) (h : xs.length = ys.length) :
    IsMonotoneWalk (List.replicate xs.length .diag) xs ys := by
  constructor <;> simp [xConsumed, yConsumed, h]

theorem scoreWalk_nonpos (sc : Scoring) (hv : ValidScoring sc) (path : List Step) (xs ys : List Char)
    (prev : Option Step) : scoreWalk sc path xs ys prev ≤ 0 := by
  have := scoreWalk_add_errs_le sc hv 0 (by omega) (by have := hv.2.1; omega)
    (by have := hv.2.2.2; omega) path xs ys prev 0
  simpa using this

/-- **Gap lower bound.**  A valid walk containing a gap column, entered from a
non-gap state, scores at most `gapOpen + gapExtend` (the rest is non-positive). -/
theorem scoreWalk_gap_le (sc : Scoring) (hv : ValidScoring sc) (path : List Step) (xs ys : List Char)
    (prev : Option Step) (hp1 : prev ≠ some .gapX) (hp2 : prev ≠ some .gapY)
    (hw : IsMonotoneWalk path xs ys) (hg : Step.gapX ∈ path ∨ Step.gapY ∈ path) :
    scoreWalk sc path xs ys prev ≤ gapCost1 sc := by
  unfold gapCost1
  obtain ⟨hx, hy⟩ := hw
  induction path generalizing xs ys prev with
  | nil => simp at hg
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          simp [xConsumed, yConsumed] at hx hy
          have := ih xs ys (some .diag) (by simp) (by simp) (by simpa using hg) (by omega) (by omega)
          have hm := hv.1; have hmm := hv.2.1
          simp only [scoreWalk]; split <;> omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        have := scoreWalk_nonpos sc hv rest xs ys (some .gapX)
        cases xs <;> (simp only [scoreWalk]; rw [if_neg hp1]; omega)
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        have := scoreWalk_nonpos sc hv rest xs ys (some .gapY)
        cases ys <;> (simp only [scoreWalk]; rw [if_neg hp2]; omega)

/-- A valid walk with no gap column is the all-diagonal walk, and the lists have equal length. -/
theorem eq_diags_of_no_gap (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hg : ¬(Step.gapX ∈ path ∨ Step.gapY ∈ path)) :
    xs.length = ys.length ∧ path = List.replicate xs.length .diag := by
  have hall : ∀ s ∈ path, s = Step.diag := by
    intro s hs
    cases s with
    | diag => rfl
    | gapX => exact absurd (Or.inl hs) hg
    | gapY => exact absurd (Or.inr hs) hg
  have hp := List.eq_replicate_of_mem hall
  obtain ⟨hx, hy⟩ := hw
  rw [hp] at hx hy
  simp [xConsumed, yConsumed] at hx hy
  exact ⟨by omega, by rw [hp, hx]⟩

/-- **Consequence.**  If the optimal score of the read against `ys` is above
`gapOpen + gapExtend`, then `ys` has the read's length and the optimum is the
gapless score. -/
theorem best_gapless (sc : Scoring) (hv : ValidScoring sc) (xs ys : List Char) (path : List Step)
    (bs : Int) (hb : getBestAlignment sc xs ys = some (path, bs)) (hS : gapCost1 sc < bs) :
    xs.length = ys.length ∧ path = List.replicate xs.length .diag ∧ bs = gaplessScore sc xs ys := by
  obtain ⟨hw, hws⟩ := getBestAlignment_returns_a_valid_walk sc xs ys path bs hb
  by_cases hg : Step.gapX ∈ path ∨ Step.gapY ∈ path
  · have := scoreWalk_gap_le sc hv path xs ys none (by simp) (by simp) hw hg
    unfold walkScore at hws
    omega
  · obtain ⟨hl, hp⟩ := eq_diags_of_no_gap path xs ys hw hg
    refine ⟨hl, hp, ?_⟩
    rw [← hws, hp, walkScore_diags sc xs ys hl]

/-! ## A gapless walk scoring at least `T` has a clean seed at its own offset -/

/-! ## `selectUnique` -/

end MapSpec

#print axioms MapSpec.walkScore_diags
#print axioms MapSpec.scoreWalk_gap_le
#print axioms MapSpec.best_gapless
