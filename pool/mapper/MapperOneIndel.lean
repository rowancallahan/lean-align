import MapperGapless

/-! Walks scoring exactly `gapOpen + gapExtend` with a gap (when
`matchScore = 0`): one gap column, every other column a match.  So the two
lists differ by deleting one letter from the longer (`delOk`). -/

namespace MapSpec

open AlignmentSpec

/-- `xs` with one letter removed is `ys`. -/
def delOk : List Char → List Char → Bool
  | x :: xs, y :: ys => if x = y then delOk xs ys else xs == y :: ys
  | [_], [] => true
  | _, _ => false

theorem delOk_cons_self (a : Char) (l : List Char) : delOk (a :: l) l = true := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [delOk]
    split
    · next h => subst h; exact ih a
    · simp

theorem delOk_spec (xs ys : List Char) (h : delOk xs ys = true) :
    ∃ i, i < xs.length ∧ ys = xs.take i ++ xs.drop (i + 1) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [delOk] at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      cases xs with
      | nil => exact ⟨0, by simp, by simp⟩
      | cons _ _ => simp [delOk] at h
    | cons y ys =>
      simp only [delOk] at h
      split at h
      · next hxy =>
        obtain ⟨i, hi, he⟩ := ih ys h
        exact ⟨i + 1, by simp; omega, by simp [hxy, he]⟩
      · have : xs = y :: ys := by simpa using h
        exact ⟨0, by simp, by simp [this]⟩

/-- Any valid walk with a gap column scores at most `gapExtend`. -/
theorem scoreWalk_gap_le_ext (sc : Scoring) (hv : ValidScoring sc) (path : List Step) (xs ys : List Char)
    (prev : Option Step) (hw : IsMonotoneWalk path xs ys) (hg : Step.gapX ∈ path ∨ Step.gapY ∈ path) :
    scoreWalk sc path xs ys prev ≤ sc.gapExtend := by
  obtain ⟨hx, hy⟩ := hw
  obtain ⟨h1, h2, h3, h4⟩ := hv
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
          have := ih xs ys (some .diag) (by simpa using hg) (by omega) (by omega)
          simp only [scoreWalk]; split <;> omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        have := scoreWalk_nonpos sc ⟨h1, h2, h3, h4⟩ rest xs ys (some .gapX)
        cases xs <;> (simp only [scoreWalk]; split <;> omega)
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        have := scoreWalk_nonpos sc ⟨h1, h2, h3, h4⟩ rest xs ys (some .gapY)
        cases ys <;> (simp only [scoreWalk]; split <;> omega)

theorem hamming_self (xs : List Char) : hamming xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [hamming, ih]

theorem eq_of_hamming_zero (xs ys : List Char) (hl : xs.length = ys.length) (h : hamming xs ys = 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [hamming] at h
      split at h
      · next hxy => rw [hxy, ih ys (by simpa using hl) (by omega)]
      · omega

/-- **Structure.**  With `matchScore = 0`, a valid walk with a gap, entered
from a non-gap state and scoring at least `gapOpen + gapExtend`, is one gap
column plus matches: the longer list minus one letter is the shorter. -/
theorem one_gap_structure (sc : Scoring) (hv : ValidScoring sc) (hm : sc.matchScore = 0)
    (path : List Step) (xs ys : List Char) (prev : Option Step)
    (hp1 : prev ≠ some .gapX) (hp2 : prev ≠ some .gapY)
    (hw : IsMonotoneWalk path xs ys) (hg : Step.gapX ∈ path ∨ Step.gapY ∈ path)
    (hs : gapCost1 sc ≤ scoreWalk sc path xs ys prev) :
    (xs.length = ys.length + 1 ∧ delOk xs ys = true) ∨
    (ys.length = xs.length + 1 ∧ delOk ys xs = true) := by
  have hv' := hv
  obtain ⟨h1, h2, h3, h4⟩ := hv
  unfold gapCost1 at hs
  induction path generalizing xs ys prev with
  | nil => simp at hg
  | cons s rest ih =>
    obtain ⟨hx, hy⟩ := hw
    cases s with
    | diag =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          simp [xConsumed, yConsumed] at hx hy
          have hg' : Step.gapX ∈ rest ∨ Step.gapY ∈ rest := by simpa using hg
          have hrest := scoreWalk_gap_le sc hv' rest xs ys (some .diag) (by simp) (by simp)
            ⟨by omega, by omega⟩ hg'
          unfold gapCost1 at hrest
          simp only [scoreWalk] at hs
          by_cases hxy : x = y
          · subst hxy
            rw [if_pos rfl, hm] at hs
            rcases ih xs ys (some .diag) (by simp) (by simp) ⟨by omega, by omega⟩ hg' (by omega) with
              ⟨hl, hd⟩ | ⟨hl, hd⟩
            · left; simp [delOk, hl, hd]
            · right; simp [delOk, hl, hd]
          · rw [if_neg hxy] at hs; omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        simp [xConsumed, yConsumed] at hx hy
        have hc : scoreWalk sc (Step.gapX :: rest) xs (y :: ys) prev =
            sc.gapOpen + sc.gapExtend + scoreWalk sc rest xs ys (some .gapX) := by
          cases xs <;> (simp only [scoreWalk]; rw [if_neg hp1])
        rw [hc] at hs
        have hng : ¬(Step.gapX ∈ rest ∨ Step.gapY ∈ rest) := by
          intro hg'
          have := scoreWalk_gap_le_ext sc hv' rest xs ys (some .gapX) ⟨by omega, by omega⟩ hg'
          omega
        obtain ⟨hl, hp⟩ := eq_diags_of_no_gap rest xs ys ⟨by omega, by omega⟩ hng
        have h0 := scoreWalk_diags_counts sc xs ys (some .gapX) hl
        rw [← hp, hm] at h0
        have hh : hamming xs ys = 0 := by
          apply Classical.byContradiction; intro hne
          have : sc.mismatchScore * (hamming xs ys : Int) ≤ sc.mismatchScore := by
            have : (1 : Int) ≤ hamming xs ys := by omega
            have := Int.mul_le_mul_of_nonpos_left (by omega : sc.mismatchScore ≤ 0) this
            simpa using this
          simp at h0; omega
        have := eq_of_hamming_zero xs ys hl hh
        subst this
        right; exact ⟨by simp, delOk_cons_self y xs⟩
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        simp [xConsumed, yConsumed] at hx hy
        have hc : scoreWalk sc (Step.gapY :: rest) (x :: xs) ys prev =
            sc.gapOpen + sc.gapExtend + scoreWalk sc rest xs ys (some .gapY) := by
          cases ys <;> (simp only [scoreWalk]; rw [if_neg hp2])
        rw [hc] at hs
        have hng : ¬(Step.gapX ∈ rest ∨ Step.gapY ∈ rest) := by
          intro hg'
          have := scoreWalk_gap_le_ext sc hv' rest xs ys (some .gapY) ⟨by omega, by omega⟩ hg'
          omega
        obtain ⟨hl, hp⟩ := eq_diags_of_no_gap rest xs ys ⟨by omega, by omega⟩ hng
        have h0 := scoreWalk_diags_counts sc xs ys (some .gapY) hl
        rw [← hp, hm] at h0
        have hh : hamming xs ys = 0 := by
          apply Classical.byContradiction; intro hne
          have : sc.mismatchScore * (hamming xs ys : Int) ≤ sc.mismatchScore := by
            have : (1 : Int) ≤ hamming xs ys := by omega
            have := Int.mul_le_mul_of_nonpos_left (by omega : sc.mismatchScore ≤ 0) this
            simpa using this
          simp at h0; omega
        have := eq_of_hamming_zero xs ys hl hh
        subst this
        left; exact ⟨by simp, delOk_cons_self x xs⟩

/-! ## Soundness: a one-letter deletion gives a walk scoring `gapOpen + gapExtend` -/

theorem scoreWalk_prefix (sc : Scoring) (hm : sc.matchScore = 0) (pre a b : List Char)
    (p : List Step) (prev : Option Step) (hp1 : prev ≠ some .gapX) (hp2 : prev ≠ some .gapY) :
    ∃ prev', prev' ≠ some .gapX ∧ prev' ≠ some .gapY ∧
      scoreWalk sc (List.replicate pre.length .diag ++ p) (pre ++ a) (pre ++ b) prev =
        scoreWalk sc p a b prev' := by
  induction pre generalizing prev with
  | nil => exact ⟨prev, hp1, hp2, by simp⟩
  | cons c pre ih =>
    obtain ⟨q, hq1, hq2, hq⟩ := ih (some .diag) (by simp) (by simp)
    refine ⟨q, hq1, hq2, ?_⟩
    simp only [List.length_cons, List.replicate_succ, List.cons_append, scoreWalk, ↓reduceIte, hm,
      Int.zero_add]
    exact hq

theorem del_walk_core (sc : Scoring) (hm : sc.matchScore = 0) (pre suf : List Char) (c : Char) :
    ∃ p, IsMonotoneWalk p (pre ++ c :: suf) (pre ++ suf) ∧
      walkScore sc (pre ++ c :: suf) (pre ++ suf) p = gapCost1 sc := by
  refine ⟨List.replicate pre.length .diag ++ (Step.gapY :: List.replicate suf.length .diag), ?_, ?_⟩
  · constructor <;> simp [xConsumed, yConsumed] <;> omega
  · unfold walkScore
    obtain ⟨q, hq1, hq2, hq⟩ := scoreWalk_prefix sc hm pre (c :: suf) suf
      (Step.gapY :: List.replicate suf.length .diag) none (by simp) (by simp)
    rw [hq]
    simp only [scoreWalk, if_neg hq2]
    rw [scoreWalk_diags_counts sc _ _ _ rfl, hamming_self]
    simp [hm, gapCost1]

theorem ins_walk_core (sc : Scoring) (hm : sc.matchScore = 0) (pre suf : List Char) (c : Char) :
    ∃ p, IsMonotoneWalk p (pre ++ suf) (pre ++ c :: suf) ∧
      walkScore sc (pre ++ suf) (pre ++ c :: suf) p = gapCost1 sc := by
  refine ⟨List.replicate pre.length .diag ++ (Step.gapX :: List.replicate suf.length .diag), ?_, ?_⟩
  · constructor <;> simp [xConsumed, yConsumed] <;> omega
  · unfold walkScore
    obtain ⟨q, hq1, hq2, hq⟩ := scoreWalk_prefix sc hm pre suf (c :: suf)
      (Step.gapX :: List.replicate suf.length .diag) none (by simp) (by simp)
    rw [hq]
    cases suf with
    | nil => simp only [scoreWalk, if_neg hq1, List.replicate_zero, List.length_nil]; simp [gapCost1]
    | cons z zs =>
      simp only [scoreWalk, if_neg hq1]
      rw [scoreWalk_diags_counts sc _ _ _ rfl, hamming_self]
      simp [hm, gapCost1]

theorem split_at (xs : List Char) (i : Nat) (hi : i < xs.length) :
    ∃ pre c suf, xs = pre ++ c :: suf ∧ xs.take i ++ xs.drop (i + 1) = pre ++ suf :=
  ⟨xs.take i, xs[i], xs.drop (i + 1), by
    conv => lhs; rw [← List.take_append_drop i xs]
    rw [List.drop_eq_getElem_cons hi], rfl⟩

/-- **Soundness.**  `delOk xs ys` gives a walk of `xs` against `ys` scoring
exactly `gapOpen + gapExtend`; `delOk ys xs` likewise. -/
theorem delOk_walk (sc : Scoring) (hm : sc.matchScore = 0) (xs ys : List Char) (h : delOk xs ys = true) :
    ∃ p, IsMonotoneWalk p xs ys ∧ walkScore sc xs ys p = gapCost1 sc := by
  obtain ⟨i, hi, he⟩ := delOk_spec xs ys h
  obtain ⟨pre, c, suf, rfl, h2⟩ := split_at xs i hi
  rw [he, h2]
  exact del_walk_core sc hm pre suf c

theorem delOk_walk' (sc : Scoring) (hm : sc.matchScore = 0) (xs ys : List Char) (h : delOk ys xs = true) :
    ∃ p, IsMonotoneWalk p xs ys ∧ walkScore sc xs ys p = gapCost1 sc := by
  obtain ⟨i, hi, he⟩ := delOk_spec ys xs h
  obtain ⟨pre, c, suf, rfl, h2⟩ := split_at ys i hi
  rw [he, h2]
  exact ins_walk_core sc hm pre suf c

end MapSpec

#print axioms MapSpec.one_gap_structure
#print axioms MapSpec.delOk_walk
#print axioms MapSpec.delOk_walk'
