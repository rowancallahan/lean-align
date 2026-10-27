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

/-- The gapless score never exceeds the optimum. -/
theorem gapless_le_best (sc : Scoring) (xs ys : List Char) (path : List Step) (bs : Int)
    (hb : getBestAlignment sc xs ys = some (path, bs)) (hl : xs.length = ys.length) :
    gaplessScore sc xs ys ≤ bs := by
  have := getBestAlignment_returns_a_maximum_score sc xs ys path bs _ hb (diags_isMonotoneWalk xs ys hl)
  rwa [walkScore_diags sc xs ys hl] at this

/-- A Hamming count above `cap = (−(gapOpen+gapExtend)) / (−mismatch)` puts the
gapless score strictly below `gapOpen + gapExtend`. -/
def gapCap (sc : Scoring) : Nat := ((-gapCost1 sc) / (-sc.mismatchScore)).toNat

theorem gaplessScore_lt_of_cap (sc : Scoring) (hv : ValidScoring sc) (xs ys : List Char)
    (h : gapCap sc < hamming xs ys) : gaplessScore sc xs ys < gapCost1 sc := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  unfold gapCap at h
  unfold gaplessScore
  have hpos : 0 < -sc.mismatchScore := by omega
  have hG : 0 ≤ -gapCost1 sc := by unfold gapCost1; omega
  have hq : 0 ≤ (-gapCost1 sc) / (-sc.mismatchScore) := Int.ediv_nonneg hG (by omega)
  have hlt : (-gapCost1 sc) / (-sc.mismatchScore) < (hamming xs ys : Int) := by omega
  have hmul : -gapCost1 sc < (hamming xs ys : Int) * (-sc.mismatchScore) :=
    (Int.ediv_lt_iff_lt_mul hpos).mp hlt
  have hm : sc.matchScore * ((xs.length - hamming xs ys : Nat) : Int) ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg h1 (by omega)
  have : sc.mismatchScore * (hamming xs ys : Int) = -((hamming xs ys : Int) * (-sc.mismatchScore)) := by
    rw [Int.mul_neg, Int.mul_comm]; omega
  omega

/-! ## A gapless walk scoring at least `T` has a clean seed at its own offset -/

theorem errCoords_diags_length (xs ys : List Char) (i : Nat) (h : xs.length = ys.length) :
    (errCoords (List.replicate xs.length .diag) xs ys i).length = hamming xs ys := by
  induction xs generalizing ys i with
  | nil => cases ys <;> simp [errCoords, hamming]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have := ih ys (i+1) (by simpa using h)
      simp only [List.length_cons, List.replicate_succ, errCoords, hamming, List.length_append]
      split <;> simp_all <;> omega

theorem diags_clean (xs ys : List Char) (i d m : Nat) (h : xs.length = ys.length)
    (hm : d + m ≤ xs.length)
    (hc : ∀ c ∈ errCoords (List.replicate xs.length .diag) xs ys i,
      ¬(2 * (i + d) < c ∧ c < 2 * (i + d + m))) :
    (ys.drop d).take m = (xs.drop d).take m := by
  induction xs generalizing ys i d m with
  | nil =>
    have hd : d = 0 := by simp at hm; omega
    have hm0 : m = 0 := by simp at hm; omega
    subst hd hm0; simp
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h hm
      have hsub : ∀ c ∈ errCoords (List.replicate xs.length .diag) xs ys (i+1),
          c ∈ errCoords (List.replicate (x :: xs).length .diag) (x :: xs) (y :: ys) i := by
        intro c hcm
        simp only [List.length_cons, List.replicate_succ, errCoords]
        exact List.mem_append_right _ hcm
      cases d with
      | zero =>
        cases m with
        | zero => simp
        | succ m =>
          have hxy : x = y := by
            apply Classical.byContradiction
            intro hxy
            exact hc (2*i+1) (by simp [List.replicate_succ, errCoords, hxy]) (by omega)
          have := ih ys (i+1) 0 m (by omega) (by omega) (fun c hcm => by
            have := hc c (hsub c hcm)
            omega)
          simp only [List.drop_zero] at this ⊢
          simp [hxy, this]
      | succ d =>
        have := ih ys (i+1) d m (by omega) (by omega) (fun c hcm => by
          have := hc c (hsub c hcm)
          omega)
        simpa using this

/-- **Seed lemma, gapless case.**  If the gapless walk of two equal-length
lists scores at least `T`, one of the `errBound + 1` seeds (length
`n / (errBound+1)`) is identical in both at the same offset. -/
theorem gapless_clean_seed (sc : Scoring) (hv : ValidScoring sc) (T : Int) (xs ys : List Char)
    (hl : xs.length = ys.length) (hs : T ≤ walkScore sc xs ys (List.replicate xs.length .diag)) :
    ∃ j, j ≤ errBound sc T ∧
      j * (xs.length / (errBound sc T + 1)) + xs.length / (errBound sc T + 1) ≤ xs.length ∧
      (ys.drop (j * (xs.length / (errBound sc T + 1)))).take (xs.length / (errBound sc T + 1)) =
        (xs.drop (j * (xs.length / (errBound sc T + 1)))).take (xs.length / (errBound sc T + 1)) := by
  have hE := errs_le_errBound sc hv T xs ys _ hs
  generalize errBound sc T = k at *
  generalize hl' : xs.length / (k + 1) = l
  have hlk : (k + 1) * l ≤ xs.length := by
    rw [← hl', Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  by_cases hl0 : l = 0
  · subst hl0; exact ⟨0, by omega, by omega, by simp⟩
  have hex : ∃ j, j ≤ k ∧ ∀ c ∈ errCoords (List.replicate xs.length .diag) xs ys 0,
      ¬(2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l)) := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ j, j < k + 1 →
        j ∈ (errCoords (List.replicate xs.length .diag) xs ys 0).map (fun c => c / (2 * l)) := by
      intro j hj
      have : ∃ c ∈ errCoords (List.replicate xs.length .diag) xs ys 0,
          2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l) := by
        apply Classical.byContradiction
        intro hc
        exact hno ⟨j, by omega, fun c hcm hcc => hc ⟨c, hcm, hcc⟩⟩
      obtain ⟨c, hcm, hc1, hc2⟩ := this
      refine List.mem_map.mpr ⟨c, hcm, ?_⟩
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_left_comm]; omega
      · rw [Nat.add_mul, Nat.mul_left_comm]; omega
    have := le_length_of_all_mem (k + 1) _ hall
    simp at this
    omega
  obtain ⟨j, hj, hc⟩ := hex
  have hjl : j * l + l ≤ xs.length := by
    have : j * l ≤ k * l := Nat.mul_le_mul_right l hj
    rw [Nat.add_mul] at hlk; omega
  exact ⟨j, hj, hjl, diags_clean xs ys 0 (j * l) l hl hjl hc⟩

/-! ## `selectUnique` -/

theorem selectUnique_eq_some_iff (l : List (Window × Int))
    (hfun : ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2) (a : Window × Int) :
    selectUnique l = some a ↔ a ∈ l ∧ ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
  have hq : ∀ a : Window × Int, (l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) = true ↔
      ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
    intro a; simp [List.all_eq_true]
  unfold selectUnique
  constructor
  · intro h
    have h2 := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, (hq a).1 h2⟩
  · rintro ⟨hm, hp⟩
    cases h : l.find? (fun a => l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) with
    | none => exact absurd ((hq a).2 hp) (List.find?_eq_none.1 h a hm)
    | some c =>
      have hc0 := List.find?_some h
      have hc := (hq c).1 hc0
      have hcm := List.mem_of_find?_eq_some h
      have h1 := hp c hcm
      have h2 := hc a hm
      have h12 : c.1 = a.1 := by
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · omega
          · exact h2.symm
        · exact h1
      rw [Prod.ext h12 (hfun c hcm a hm h12)]

/-- Dropping hits below a score `S` that some hit reaches does not change the answer. -/
theorem selectUnique_filter (l : List (Window × Int)) (S : Int)
    (hfun : ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2) (hS : ∃ a ∈ l, S ≤ a.2) :
    selectUnique (l.filter fun a => decide (S ≤ a.2)) = selectUnique l := by
  have hfun' : ∀ a ∈ l.filter (fun a => decide (S ≤ a.2)), ∀ b ∈ l.filter (fun a => decide (S ≤ a.2)),
      a.1 = b.1 → a.2 = b.2 := by
    intro a ha b hb; exact hfun a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1
  apply Option.ext
  intro a
  rw [selectUnique_eq_some_iff _ hfun', selectUnique_eq_some_iff _ hfun]
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ha, hSa⟩, hall⟩
    refine ⟨ha, fun b hb => ?_⟩
    by_cases hSb : S ≤ b.2
    · exact hall b ⟨hb, hSb⟩
    · left; omega
  · rintro ⟨ha, hall⟩
    obtain ⟨a0, ha0, hS0⟩ := hS
    have : S ≤ a.2 := by
      rcases hall a0 ha0 with h | h
      · omega
      · have := hfun a0 ha0 a ha h; omega
    exact ⟨⟨ha, this⟩, fun b hb => hall b hb.1⟩

end MapSpec

#print axioms MapSpec.walkScore_diags
#print axioms MapSpec.scoreWalk_gap_le
#print axioms MapSpec.best_gapless
#print axioms MapSpec.gapless_clean_seed
#print axioms MapSpec.selectUnique_filter
