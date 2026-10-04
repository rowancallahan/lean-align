import AlignmentAlgorithms

/-!
An adaptive, wavefront-style alignment algorithm with an UNCONDITIONAL
proof of equality to the frozen spec `getBestAlignment`.

The adaptive principle is the one underlying WFA / Ukkonen's band
doubling: alignments of similar strings stay near the main diagonal, so
compute only a band around it and widen the band until the answer is
*certified* optimal.  Certification is the trick that keeps the equality
theorem unconditional: the algorithm checks at run time both that the
scoring is well-behaved (`reasonableB`) and that the in-band optimum
provably beats every alignment that could leave the band; when either
check fails it widens the band, and in the worst case the band covers
the whole grid, where the banded computation coincides with the exact
one.  So `ReasonableScoring` never appears in the final theorem — it
only decides how fast the answer is found.

Contents:
1. Walk statistics and the exact score decomposition
   (`scoreWalk_eq_stats`).
2. The match-zero translation: `pathPenalty` with nonnegative penalties
   and `penalty_transform`, turning score maximisation into penalty
   minimisation (the model WFA computes in).
3. The band predicate, banded spec, and banded Bellman recursion.
4. Banded row tabulation.
5. The certification lemmas and the band-doubling driver `bandDoublingAlign`,
   with `bandDoublingAlign_equals_getBestAlignment` for every scoring and input.
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- PART 1: walk statistics and the exact score decomposition
-- ══════════════════════════════════════════════════════════════════

structure WalkStats where
  matchCount    : Nat
  mismatchCount : Nat
  gapXCount     : Nat
  gapYCount     : Nat
  runCount      : Nat
deriving Repr

/-- Count matches, mismatches, gap columns, and gap runs along a walk,
with the same case structure as `scoreWalk`. -/
def walkStats : List Step → List Char → List Char → Option Step →
    WalkStats
  | [], _, _, _ => ⟨0, 0, 0, 0, 0⟩
  | .diag :: rest, x :: xs, y :: ys, _ =>
      let s := walkStats rest xs ys (some .diag)
      if x = y then { s with matchCount := s.matchCount + 1 }
      else { s with mismatchCount := s.mismatchCount + 1 }
  | .gapX :: rest, xs, _ :: ys, prev =>
      let s := walkStats rest xs ys (some .gapX)
      { s with gapXCount := s.gapXCount + 1,
               runCount := s.runCount + (if prev = some .gapX then 0 else 1) }
  | .gapY :: rest, _ :: xs, ys, prev =>
      let s := walkStats rest xs ys (some .gapY)
      { s with gapYCount := s.gapYCount + 1,
               runCount := s.runCount + (if prev = some .gapY then 0 else 1) }
  | _, _, _, _ => ⟨0, 0, 0, 0, 0⟩

/-- Shorthand for the score a `WalkStats` implies. -/
def statsScore (sc : Scoring) (s : WalkStats) : Int :=
  sc.matchScore * (s.matchCount : Int) +
  sc.mismatchScore * (s.mismatchCount : Int) +
  sc.gapExtend * ((s.gapXCount : Int) + (s.gapYCount : Int)) +
  sc.gapOpen * (s.runCount : Int)

/-- The exact decomposition of a walk's score into its statistics.
Holds for every step list, valid or not, because `walkStats` mirrors
`scoreWalk` case by case. -/
theorem scoreWalk_eq_stats (sc : Scoring) (p : List Step)
    (xs ys : List Char) (prev : Option Step) :
    scoreWalk sc p xs ys prev = statsScore sc (walkStats p xs ys prev) := by
  induction p generalizing xs ys prev with
  | nil =>
      simp [scoreWalk, walkStats, statsScore]
  | cons s rest ih =>
      cases s with
      | diag =>
          cases xs with
          | nil => simp [scoreWalk, walkStats, statsScore]
          | cons x xs =>
              cases ys with
              | nil => simp [scoreWalk, walkStats, statsScore]
              | cons y ys =>
                  by_cases hxy : x = y <;>
                    simp [scoreWalk, walkStats, statsScore, hxy, ih,
                      Int.mul_add, Int.mul_one] <;>
                    omega
      | gapX =>
          cases ys with
          | nil => simp [scoreWalk, walkStats, statsScore]
          | cons y ys =>
              rw [scoreWalk_gapX_cons]
              by_cases hprev : prev = some Step.gapX <;>
                simp [walkStats, statsScore, gapXCost, hprev, ih,
                  Int.mul_add, Int.mul_one] <;>
                omega
      | gapY =>
          cases xs with
          | nil => simp [scoreWalk, walkStats, statsScore]
          | cons x xs =>
              rw [scoreWalk_gapY_cons]
              by_cases hprev : prev = some Step.gapY <;>
                simp [walkStats, statsScore, gapYCost, hprev, ih,
                  Int.mul_add, Int.mul_one] <;>
                omega

-- Statistics agree with plain step counts on valid walks.
theorem stats_eq_counts (p : List Step) (xs ys : List Char)
    (prev : Option Step) (hvalid : IsMonotoneWalk p xs ys) :
    ((walkStats p xs ys prev).matchCount +
      (walkStats p xs ys prev).mismatchCount = p.count .diag) ∧
    ((walkStats p xs ys prev).gapXCount = p.count .gapX) ∧
    ((walkStats p xs ys prev).gapYCount = p.count .gapY) := by
  induction p generalizing xs ys prev with
  | nil => simp [walkStats]
  | cons s rest ih =>
      obtain ⟨hx, hy⟩ := hvalid
      cases s with
      | diag =>
          cases xs with
          | nil => simp [xConsumed] at hx
          | cons x xs =>
              cases ys with
              | nil => simp [yConsumed] at hy
              | cons y ys =>
                  simp [xConsumed, yConsumed] at hx hy
                  have hrest := ih xs ys (some .diag)
                    (by constructor <;> omega)
                  by_cases hxy : x = y <;>
                    simp +decide [walkStats, hxy, List.count_cons,
                      hrest] <;>
                    omega
      | gapX =>
          cases ys with
          | nil => simp [yConsumed] at hy
          | cons y ys =>
              simp [xConsumed, yConsumed] at hx hy
              have hrest := ih xs ys (some .gapX)
                (by constructor <;> omega)
              simp +decide [walkStats, List.count_cons, hrest]
      | gapY =>
          cases xs with
          | nil => simp [xConsumed] at hx
          | cons x xs =>
              simp [xConsumed, yConsumed] at hx hy
              have hrest := ih xs ys (some .gapY)
                (by constructor <;> omega)
              simp +decide [walkStats, List.count_cons, hrest]

-- Consumption sums are step counts (no validity needed).
theorem xConsumed_sum_eq_counts (p : List Step) :
    (p.map xConsumed).sum = p.count .diag + p.count .gapY := by
  induction p with
  | nil => simp
  | cons s rest ih =>
      cases s <;>
        simp +decide [xConsumed, List.count_cons, ih] <;> omega

theorem yConsumed_sum_eq_counts (p : List Step) :
    (p.map yConsumed).sum = p.count .diag + p.count .gapX := by
  induction p with
  | nil => simp
  | cons s rest ih =>
      cases s <;>
        simp +decide [yConsumed, List.count_cons, ih] <;> omega

-- A walk that starts from a non-gap state and contains a gap column
-- opens at least one run.
theorem gaps_eq_zero_of_runs_zero (p : List Step) (xs ys : List Char)
    (prev : Option Step)
    (hneutral : prev ≠ some .gapX ∧ prev ≠ some .gapY)
    (hruns : (walkStats p xs ys prev).runCount = 0) :
    (walkStats p xs ys prev).gapXCount = 0 ∧
    (walkStats p xs ys prev).gapYCount = 0 := by
  induction p generalizing xs ys prev with
  | nil => simp [walkStats]
  | cons s rest ih =>
      cases s with
      | diag =>
          cases xs with
          | nil => simp [walkStats]
          | cons x xs =>
              cases ys with
              | nil => simp [walkStats]
              | cons y ys =>
                  by_cases hxy : x = y <;>
                    simp [walkStats, hxy] at hruns ⊢ <;>
                    exact ih xs ys (some .diag) ⟨by simp, by simp⟩ hruns
      | gapX =>
          cases ys with
          | nil => simp [walkStats]
          | cons y ys =>
              have : ¬ (prev = some Step.gapX) := hneutral.1
              simp [walkStats, this] at hruns
      | gapY =>
          cases xs with
          | nil => simp [walkStats]
          | cons x xs =>
              have : ¬ (prev = some Step.gapY) := hneutral.2
              simp [walkStats, this] at hruns

-- ══════════════════════════════════════════════════════════════════
-- PART 2: the match-zero translation (score ↔ penalty)
-- ══════════════════════════════════════════════════════════════════

/-- The scoring conditions under which the adaptive machinery is fast.
NOT part of any equality theorem — the algorithm checks them at run
time and certification only fires when they hold. -/
structure ReasonableScoring (sc : Scoring) : Prop where
  match_best : sc.mismatchScore ≤ sc.matchScore
  match_pos  : 0 ≤ sc.matchScore
  extend_neg : sc.gapExtend ≤ 0
  open_neg   : sc.gapOpen ≤ 0

def reasonableB (sc : Scoring) : Bool :=
  decide (sc.mismatchScore ≤ sc.matchScore) &&
  decide (0 ≤ sc.matchScore) &&
  decide (sc.gapExtend ≤ 0) &&
  decide (sc.gapOpen ≤ 0)

theorem reasonableB_iff (sc : Scoring) :
    reasonableB sc = true ↔ ReasonableScoring sc := by
  constructor
  · intro h
    simp [reasonableB, Bool.and_eq_true, decide_eq_true_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · intro h
    simp [reasonableB, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨⟨⟨h.match_best, h.match_pos⟩, h.extend_neg⟩, h.open_neg⟩

/-- The penalty of a walk in the doubled match-zero model: a match
costs 0, a mismatch costs `2(M − X)`, a gap column costs `M − 2E`,
opening a run costs `−2O`.  Under `ReasonableScoring` every unit is
nonnegative — this is exactly the penalty model WFA-style algorithms
run on. -/
def pathPenalty (sc : Scoring) (p : List Step) (xs ys : List Char)
    (prev : Option Step) : Int :=
  let s := walkStats p xs ys prev
  2 * (sc.matchScore - sc.mismatchScore) * (s.mismatchCount : Int) +
  (sc.matchScore - 2 * sc.gapExtend) *
    ((s.gapXCount : Int) + (s.gapYCount : Int)) +
  (-2 * sc.gapOpen) * (s.runCount : Int)

/-- The match-zero translation theorem: on every valid walk, twice the
similarity score plus the penalty is the constant `M·(m+n)`.  Hence
maximising score is exactly minimising penalty, ties included. -/
theorem penalty_transform (sc : Scoring) (p : List Step)
    (xs ys : List Char) (prev : Option Step)
    (hvalid : IsMonotoneWalk p xs ys) :
    2 * scoreWalk sc p xs ys prev + pathPenalty sc p xs ys prev =
      sc.matchScore * ((xs.length : Int) + (ys.length : Int)) := by
  obtain ⟨hx, hy⟩ := hvalid
  rw [xConsumed_sum_eq_counts] at hx
  rw [yConsumed_sum_eq_counts] at hy
  obtain ⟨hmm, hgx, hgy⟩ := stats_eq_counts p xs ys prev
    ⟨by rw [xConsumed_sum_eq_counts]; exact hx,
     by rw [yConsumed_sum_eq_counts]; exact hy⟩
  rw [scoreWalk_eq_stats, pathPenalty, statsScore]
  -- both string lengths in terms of the statistics
  have hxlen : (xs.length : Int) =
      ((walkStats p xs ys prev).matchCount : Int) +
        ((walkStats p xs ys prev).mismatchCount : Int) +
        ((walkStats p xs ys prev).gapYCount : Int) := by omega
  have hylen : (ys.length : Int) =
      ((walkStats p xs ys prev).matchCount : Int) +
        ((walkStats p xs ys prev).mismatchCount : Int) +
        ((walkStats p xs ys prev).gapXCount : Int) := by omega
  rw [hxlen, hylen]
  -- distribute all products into literal-scaled atoms, then decide
  -- the linear combination
  simp only [Int.mul_add, Int.add_mul, Int.sub_mul, Int.mul_sub,
    Int.neg_mul, Int.mul_assoc, Int.mul_one, Int.one_mul]
  omega

/-- Under a reasonable scoring, penalties are nonnegative — the WFA
precondition, derived rather than assumed. -/
theorem pathPenalty_nonneg (sc : Scoring) (p : List Step)
    (xs ys : List Char) (prev : Option Step)
    (h : ReasonableScoring sc) :
    0 ≤ pathPenalty sc p xs ys prev := by
  rw [pathPenalty]
  have h1 : (0 : Int) ≤ 2 * (sc.matchScore - sc.mismatchScore) := by
    have := h.match_best; omega
  have h2 : (0 : Int) ≤ sc.matchScore - 2 * sc.gapExtend := by
    have := h.match_pos; have := h.extend_neg; omega
  have h3 : (0 : Int) ≤ -2 * sc.gapOpen := by
    have := h.open_neg; omega
  have c1 : (0 : Int) ≤ ((walkStats p xs ys prev).mismatchCount : Int) := by
    omega
  have c2 : (0 : Int) ≤ ((walkStats p xs ys prev).gapXCount : Int) +
      ((walkStats p xs ys prev).gapYCount : Int) := by omega
  have c3 : (0 : Int) ≤ ((walkStats p xs ys prev).runCount : Int) := by
    omega
  have m1 := Int.mul_nonneg h1 c1
  have m2 := Int.mul_nonneg h2 c2
  have m3 := Int.mul_nonneg h3 c3
  omega

/-- Order reversal: comparing scores is comparing penalties backwards.
This is the bridge that lets a minimising wavefront search stand in for
the maximising spec. -/
theorem score_le_iff_penalty_ge (sc : Scoring) (p q : List Step)
    (xs ys : List Char)
    (hp : IsMonotoneWalk p xs ys) (hq : IsMonotoneWalk q xs ys) :
    scoreWalk sc p xs ys none ≤ scoreWalk sc q xs ys none ↔
      pathPenalty sc q xs ys none ≤ pathPenalty sc p xs ys none := by
  have h1 := penalty_transform sc p xs ys none hp
  have h2 := penalty_transform sc q xs ys none hq
  omega

-- ══════════════════════════════════════════════════════════════════
-- PART 3: the band predicate and the banded Bellman recursion
-- ══════════════════════════════════════════════════════════════════

/-- How one step moves the walk across diagonals. -/
def stepDev : Step → Int
  | .diag => 0
  | .gapX => 1
  | .gapY => -1

/-- Does every prefix of the walk stay within the diagonal band
`[lo, hi]`?  (Deviation of a prefix = gap-in-x columns minus gap-in-y
columns consumed so far; the empty prefix has deviation 0, and the
window shifts as columns are consumed.) -/
def inBand (lo hi : Int) : List Step → Bool
  | [] => decide (lo ≤ 0 ∧ 0 ≤ hi)
  | s :: p =>
      decide (lo ≤ 0 ∧ 0 ≤ hi) &&
        inBand (lo - stepDev s) (hi - stepDev s) p

/-- Leaving the band pins down gap counts: a walk rejected by the band
check either exceeds `hi` many gap-in-x columns or `−lo` many gap-in-y
columns. -/
theorem counts_of_not_inBand (lo hi : Int) (p : List Step)
    (h : inBand lo hi p = false) :
    hi < (p.count .gapX : Int) ∨ (p.count .gapY : Int) > -lo := by
  induction p generalizing lo hi with
  | nil =>
      simp [inBand] at h
      simp
      omega
  | cons s rest ih =>
      rw [inBand, Bool.and_eq_false_iff] at h
      rcases h with hguard | hrest
      · simp at hguard
        cases s <;> simp +decide [List.count_cons] <;> omega
      · cases s <;>
        · have hcount := ih _ _ hrest
          simp [stepDev] at hcount
          simp +decide [List.count_cons]
          omega

/-- A valid walk fits in any band wide enough to hold both whole
strings. -/
theorem inBand_of_wide (p : List Step) (xs ys : List Char) (lo hi : Int)
    (hvalid : IsMonotoneWalk p xs ys)
    (hlo : lo ≤ -(xs.length : Int)) (hhi : (ys.length : Int) ≤ hi) :
    inBand lo hi p = true := by
  induction p generalizing xs ys lo hi with
  | nil =>
      simp [inBand]
      omega
  | cons s rest ih =>
      obtain ⟨hx, hy⟩ := hvalid
      cases s with
      | diag =>
          cases xs with
          | nil => simp [xConsumed] at hx
          | cons x xs =>
              cases ys with
              | nil => simp [yConsumed] at hy
              | cons y ys =>
                  simp [xConsumed, yConsumed] at hx hy
                  rw [inBand, Bool.and_eq_true]
                  refine ⟨by simp; omega, ?_⟩
                  simp [stepDev]
                  exact ih xs ys lo hi (by constructor <;> omega)
                    (by simp at hlo ⊢; omega) (by simp at hhi ⊢; omega)
      | gapX =>
          cases ys with
          | nil => simp [yConsumed] at hy
          | cons y ys =>
              simp [xConsumed, yConsumed] at hx hy
              rw [inBand, Bool.and_eq_true]
              refine ⟨by simp; omega, ?_⟩
              simp [stepDev]
              exact ih xs ys (lo - 1) (hi - 1) (by constructor <;> omega)
                (by omega) (by simp at hhi ⊢; omega)
      | gapY =>
          cases xs with
          | nil => simp [xConsumed] at hx
          | cons x xs =>
              simp [xConsumed, yConsumed] at hx hy
              rw [inBand, Bool.and_eq_true]
              refine ⟨by simp; omega, ?_⟩
              simp [stepDev]
              exact ih xs ys (lo + 1) (hi + 1) (by constructor <;> omega)
                (by simp at hlo ⊢; omega) (by omega)

/-- The banded specification: the best walk among those staying inside
the band, with the same earliest-maximum tie policy as the spec. -/
def bandedBestAux (sc : Scoring) (xs ys : List Char) (prev : Option Step)
    (lo hi : Int) : Option (List Step × Int) :=
  (((allPaths xs ys).filter (fun p => inBand lo hi p)).map
    fun p => (p, scoreWalk sc p xs ys prev)).maxOn? fun item => item.2

/-- Filtering a cons-mapped path list by the band splits into the
window guard and the shifted filter on the tails. -/
theorem filter_inBand_map_cons (L : List (List Step)) (s : Step)
    (lo hi : Int) :
    (L.map (s :: ·)).filter (fun p => inBand lo hi p) =
      if lo ≤ 0 ∧ 0 ≤ hi then
        (L.filter
          (fun p => inBand (lo - stepDev s) (hi - stepDev s) p)).map
          (s :: ·)
      else [] := by
  induction L with
  | nil => simp
  | cons p L ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hg : lo ≤ 0 ∧ 0 ≤ hi
      · by_cases hp : inBand (lo - stepDev s) (hi - stepDev s) p = true <;>
          simp [inBand, hg, hp, ih]
      · simp [inBand, hg, ih]

/-- The banded Bellman recursion: the executable counterpart of
`bandedBestAux`, with the window guard evaluated at every node. -/
def bBellman (sc : Scoring) :
    List Char → List Char → Option Step → Int → Int →
      Option (List Step × Int)
  | [], [], _, lo, hi =>
      if lo ≤ 0 ∧ 0 ≤ hi then some ([], 0) else none
  | [], _ :: ys, prev, lo, hi =>
      if lo ≤ 0 ∧ 0 ≤ hi then
        (bBellman sc [] ys (some .gapX) (lo - 1) (hi - 1)).map
          fun r => (.gapX :: r.1, gapXCost sc prev + r.2)
      else none
  | _ :: xs, [], prev, lo, hi =>
      if lo ≤ 0 ∧ 0 ≤ hi then
        (bBellman sc xs [] (some .gapY) (lo + 1) (hi + 1)).map
          fun r => (.gapY :: r.1, gapYCost sc prev + r.2)
      else none
  | x :: xs, y :: ys, prev, lo, hi =>
      if lo ≤ 0 ∧ 0 ≤ hi then
        Option.merge (maxOn fun item : List Step × Int => item.2)
          (Option.merge (maxOn fun item : List Step × Int => item.2)
            ((bBellman sc xs ys (some .diag) lo hi).map
              fun r => (.diag :: r.1, diagCost sc x y + r.2))
            ((bBellman sc (x :: xs) ys (some .gapX) (lo - 1) (hi - 1)).map
              fun r => (.gapX :: r.1, gapXCost sc prev + r.2)))
          ((bBellman sc xs (y :: ys) (some .gapY) (lo + 1) (hi + 1)).map
            fun r => (.gapY :: r.1, gapYCost sc prev + r.2))
      else none

theorem inBand_false_of_bad (lo hi : Int) (p : List Step)
    (h : ¬ (lo ≤ 0 ∧ 0 ≤ hi)) : inBand lo hi p = false := by
  cases p <;> simp [inBand, h]

theorem bandedBestAux_none_of_bad (sc : Scoring) (xs ys : List Char)
    (prev : Option Step) (lo hi : Int) (hg : ¬ (lo ≤ 0 ∧ 0 ≤ hi)) :
    bandedBestAux sc xs ys prev lo hi = none := by
  rw [bandedBestAux]
  have hf : (allPaths xs ys).filter (fun p => inBand lo hi p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p _
    simp [inBand_false_of_bad lo hi p hg]
  rw [hf]
  rfl

theorem bandedBestAux_eq_bBellman (sc : Scoring) (xs ys : List Char)
    (prev : Option Step) (lo hi : Int) :
    bandedBestAux sc xs ys prev lo hi = bBellman sc xs ys prev lo hi := by
  induction xs, ys, prev, lo, hi using bBellman.induct with
  | case1 prev lo hi hg =>
      simp [bandedBestAux, bBellman, allPaths, inBand, hg, scoreWalk]
  | case2 prev lo hi hg =>
      rw [bandedBestAux_none_of_bad sc _ _ _ _ _ hg]
      simp [bBellman, hg]
  | case3 y ys prev lo hi hg ih =>
      rw [bandedBestAux, bBellman]
      simp only [allPaths]
      rw [filter_inBand_map_cons]
      rw [if_pos hg, if_pos hg, List.map_map]
      have hcomp :
          ((fun p => (p, scoreWalk sc p [] (y :: ys) prev)) ∘
              (Step.gapX :: ·)) =
            fun p => (Step.gapX :: p,
              gapXCost sc prev + scoreWalk sc p [] ys (some .gapX)) := by
        funext p
        simp [Function.comp, scoreWalk_gapX_cons]
      rw [hcomp, maxOn?_map_shift]
      simp only [stepDev] at ih ⊢
      rw [← ih]
      rfl
  | case4 y ys prev lo hi hg =>
      rw [bandedBestAux_none_of_bad sc _ _ _ _ _ hg]
      simp [bBellman, hg]
  | case5 x xs prev lo hi hg ih =>
      rw [bandedBestAux, bBellman]
      simp only [allPaths]
      rw [filter_inBand_map_cons]
      rw [if_pos hg, if_pos hg, List.map_map]
      have hcomp :
          ((fun p => (p, scoreWalk sc p (x :: xs) [] prev)) ∘
              (Step.gapY :: ·)) =
            fun p => (Step.gapY :: p,
              gapYCost sc prev + scoreWalk sc p xs [] (some .gapY)) := by
        funext p
        simp [Function.comp, scoreWalk_gapY_cons]
      rw [hcomp, maxOn?_map_shift]
      simp only [stepDev] at ih ⊢
      rw [← ih]
      rfl
  | case6 x xs prev lo hi hg =>
      rw [bandedBestAux_none_of_bad sc _ _ _ _ _ hg]
      simp [bBellman, hg]
  | case7 x xs y ys prev lo hi hg ihDiag ihGapX ihGapY =>
      rw [bandedBestAux, bBellman]
      simp only [allPaths]
      rw [List.filter_append, List.filter_append,
        filter_inBand_map_cons, filter_inBand_map_cons,
        filter_inBand_map_cons]
      rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg,
        List.map_append, List.map_append,
        List.maxOn?_append, List.maxOn?_append,
        List.map_map, List.map_map, List.map_map]
      have hdiag :
          ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
              (Step.diag :: ·)) =
            fun p => (Step.diag :: p,
              diagCost sc x y + scoreWalk sc p xs ys (some .diag)) := by
        funext p
        simp [Function.comp, scoreWalk_diag_cons]
      have hgapX :
          ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
              (Step.gapX :: ·)) =
            fun p => (Step.gapX :: p,
              gapXCost sc prev +
                scoreWalk sc p (x :: xs) ys (some .gapX)) := by
        funext p
        simp [Function.comp, scoreWalk_gapX_cons]
      have hgapY :
          ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
              (Step.gapY :: ·)) =
            fun p => (Step.gapY :: p,
              gapYCost sc prev +
                scoreWalk sc p xs (y :: ys) (some .gapY)) := by
        funext p
        simp [Function.comp, scoreWalk_gapY_cons]
      rw [hdiag, hgapX, hgapY,
        maxOn?_map_shift, maxOn?_map_shift, maxOn?_map_shift]
      simp only [stepDev, Int.sub_zero, Int.sub_neg] at ihDiag ihGapX ihGapY ⊢
      rw [← ihDiag, ← ihGapX, ← ihGapY]
      rfl
  | case8 x xs y ys prev lo hi hg =>
      rw [bandedBestAux_none_of_bad sc _ _ _ _ _ hg]
      simp [bBellman, hg]

/-- Behind a wide enough band the banded recursion is the exact one. -/
theorem bBellman_wide (sc : Scoring) (xs ys : List Char)
    (prev : Option Step) (lo hi : Int)
    (hlo : lo ≤ -(xs.length : Int)) (hhi : (ys.length : Int) ≤ hi) :
    bBellman sc xs ys prev lo hi = some (bellmanAux sc xs ys prev) := by
  rw [← bandedBestAux_eq_bBellman, ← bestAux_eq_bellmanAux]
  rw [bandedBestAux, bestAux]
  congr 1
  congr 1
  apply List.filter_eq_self.mpr
  intro p hp
  exact inBand_of_wide p xs ys lo hi
    (isMonotoneWalk_of_mem_allPaths xs ys p hp) hlo hhi

-- ══════════════════════════════════════════════════════════════════
-- PART 4: banded row tabulation
-- ══════════════════════════════════════════════════════════════════

theorem bBellman_none_of_neg (sc : Scoring) (xs ys : List Char)
    (prev : Option Step) (lo hi : Int) (hneg : hi < 0) :
    bBellman sc xs ys prev lo hi = none := by
  have hg : ¬ (lo ≤ 0 ∧ 0 ≤ hi) := by omega
  cases xs <;> cases ys <;> simp [bBellman, hg]

theorem bBellman_diag_eq_none_prev (sc : Scoring) (xs ys : List Char)
    (lo hi : Int) :
    bBellman sc xs ys (some .diag) lo hi = bBellman sc xs ys none lo hi := by
  cases xs <;> cases ys <;> simp [bBellman, gapXCost, gapYCost]

structure BCell where
  neutral   : Option (List Step × Int)
  afterGapX : Option (List Step × Int)
  afterGapY : Option (List Step × Int)

def bCellNone : BCell := ⟨none, none, none⟩

def bCellHead (row : List BCell) : BCell := row.headD bCellNone

theorem bCellHead_cons (c : BCell) (rest : List BCell) :
    bCellHead (c :: rest) = c :=
  rfl

/-- Proof-side: the value every banded table cell must hold. -/
def specBCell (sc : Scoring) (xs ys : List Char) (lo hi : Int) : BCell :=
  { neutral   := bBellman sc xs ys none lo hi
  , afterGapX := bBellman sc xs ys (some .gapX) lo hi
  , afterGapY := bBellman sc xs ys (some .gapY) lo hi }

theorem specBCell_none_of_neg (sc : Scoring) (xs ys : List Char)
    (lo hi : Int) (hneg : hi < 0) :
    specBCell sc xs ys lo hi = bCellNone := by
  simp [specBCell, bCellNone, bBellman_none_of_neg _ _ _ _ _ _ hneg]

-- ── Cell builders (implementation side) ──

def bMkBase (lo hi : Int) : BCell :=
  if lo ≤ 0 ∧ 0 ≤ hi then ⟨some ([], 0), some ([], 0), some ([], 0)⟩
  else bCellNone

def bMkGapXOnly (sc : Scoring) (lo hi : Int) (next : BCell) : BCell :=
  if lo ≤ 0 ∧ 0 ≤ hi then
    let r := next.afterGapX
    let oe := sc.gapOpen + sc.gapExtend
    { neutral   := r.map fun t => (.gapX :: t.1, oe + t.2)
    , afterGapX := r.map fun t => (.gapX :: t.1, sc.gapExtend + t.2)
    , afterGapY := r.map fun t => (.gapX :: t.1, oe + t.2) }
  else bCellNone

def bMkGapYOnly (sc : Scoring) (lo hi : Int) (next : BCell) : BCell :=
  if lo ≤ 0 ∧ 0 ≤ hi then
    let r := next.afterGapY
    let oe := sc.gapOpen + sc.gapExtend
    { neutral   := r.map fun t => (.gapY :: t.1, oe + t.2)
    , afterGapX := r.map fun t => (.gapY :: t.1, oe + t.2)
    , afterGapY := r.map fun t => (.gapY :: t.1, sc.gapExtend + t.2) }
  else bCellNone

def bMkMain (sc : Scoring) (x y : Char) (lo hi : Int)
    (nj nj1 cur1 : BCell) : BCell :=
  if lo ≤ 0 ∧ 0 ≤ hi then
    let dCand := nj1.neutral.map
      fun t => (Step.diag :: t.1, diagCost sc x y + t.2)
    let gx := cur1.afterGapX
    let gy := nj.afterGapY
    let oe := sc.gapOpen + sc.gapExtend
    let pick (gxCost gyCost : Int) : Option (List Step × Int) :=
      Option.merge (maxOn fun item : List Step × Int => item.2)
        (Option.merge (maxOn fun item : List Step × Int => item.2)
          dCand
          (gx.map fun t => (Step.gapX :: t.1, gxCost + t.2)))
        (gy.map fun t => (Step.gapY :: t.1, gyCost + t.2))
    { neutral   := pick oe oe
    , afterGapX := pick sc.gapExtend oe
    , afterGapY := pick oe sc.gapExtend }
  else bCellNone

-- ── Cell builders compute the right cells ──

theorem bMkBase_spec (sc : Scoring) (lo hi : Int) :
    bMkBase lo hi = specBCell sc [] [] lo hi := by
  by_cases hg : lo ≤ 0 ∧ 0 ≤ hi <;>
    simp [bMkBase, specBCell, bBellman, bCellNone, hg]

theorem bMkGapXOnly_spec (sc : Scoring) (y : Char) (ys : List Char)
    (lo hi : Int) :
    bMkGapXOnly sc lo hi (specBCell sc [] ys (lo - 1) (hi - 1)) =
      specBCell sc [] (y :: ys) lo hi := by
  by_cases hg : lo ≤ 0 ∧ 0 ≤ hi <;>
    simp [bMkGapXOnly, specBCell, bBellman, gapXCost, bCellNone, hg]

theorem bMkGapYOnly_spec (sc : Scoring) (x : Char) (xs : List Char)
    (lo hi : Int) :
    bMkGapYOnly sc lo hi (specBCell sc xs [] (lo + 1) (hi + 1)) =
      specBCell sc (x :: xs) [] lo hi := by
  by_cases hg : lo ≤ 0 ∧ 0 ≤ hi <;>
    simp [bMkGapYOnly, specBCell, bBellman, gapYCost, bCellNone, hg]

theorem bMkMain_spec (sc : Scoring) (x y : Char) (xs ys : List Char)
    (lo hi : Int) :
    bMkMain sc x y lo hi
        (specBCell sc xs (y :: ys) (lo + 1) (hi + 1))
        (specBCell sc xs ys lo hi)
        (specBCell sc (x :: xs) ys (lo - 1) (hi - 1)) =
      specBCell sc (x :: xs) (y :: ys) lo hi := by
  by_cases hg : lo ≤ 0 ∧ 0 ≤ hi <;>
    simp [bMkMain, specBCell, bBellman, gapXCost, gapYCost, bCellNone,
      bBellman_diag_eq_none_prev, hg]

-- ── Rows ──

/-- Proof-side row: the cell for every y-suffix, windows shifting one
step per consumed character, truncated once the window is dead. -/
def bSpecRow (sc : Scoring) (xs : List Char) :
    List Char → Int → Int → List BCell
  | ys, lo, hi =>
    if hi < 0 then []
    else
      match ys with
      | [] => [specBCell sc xs [] lo hi]
      | y :: ys' =>
          specBCell sc xs (y :: ys') lo hi ::
            bSpecRow sc xs ys' (lo - 1) (hi - 1)

theorem bCellHead_bSpecRow (sc : Scoring) (xs ys : List Char)
    (lo hi : Int) :
    bCellHead (bSpecRow sc xs ys lo hi) = specBCell sc xs ys lo hi := by
  by_cases hneg : hi < 0
  · rw [specBCell_none_of_neg sc xs ys lo hi hneg]
    cases ys <;> simp [bSpecRow, hneg, bCellHead]
  · cases ys <;> simp [bSpecRow, hneg, bCellHead_cons]

def bLastRow (sc : Scoring) : List Char → Int → Int → List BCell
  | ys, lo, hi =>
    if hi < 0 then []
    else
      match ys with
      | [] => [bMkBase lo hi]
      | _ :: ys' =>
          let rest := bLastRow sc ys' (lo - 1) (hi - 1)
          bMkGapXOnly sc lo hi (bCellHead rest) :: rest

def bRowUp (sc : Scoring) (x : Char) :
    List Char → List BCell → Int → Int → List BCell
  | ys, next, lo, hi =>
    if hi < 0 then []
    else
      match ys with
      | [] => [bMkGapYOnly sc lo hi (bCellHead next)]
      | y :: ys' =>
          let cur := bRowUp sc x ys' next.tail (lo - 1) (hi - 1)
          bMkMain sc x y lo hi (bCellHead next) (bCellHead next.tail)
            (bCellHead cur) :: cur

def bTable (sc : Scoring) : List Char → List Char → Int → Int → List BCell
  | [], ys, lo, hi => bLastRow sc ys lo hi
  | x :: xs, ys, lo, hi =>
      bRowUp sc x ys (bTable sc xs ys (lo + 1) (hi + 1)) lo hi

/-- The banded tabulated algorithm: build the table, read the corner. -/
def bandedRun (sc : Scoring) (xs ys : List Char) (lo hi : Int) :
    Option (List Step × Int) :=
  (bCellHead (bTable sc xs ys lo hi)).neutral

-- ── Row invariants ──

theorem bLastRow_eq (sc : Scoring) (ys : List Char) (lo hi : Int) :
    bLastRow sc ys lo hi = bSpecRow sc [] ys lo hi := by
  induction ys generalizing lo hi with
  | nil =>
      by_cases hneg : hi < 0 <;>
        simp [bLastRow, bSpecRow, hneg, bMkBase_spec sc lo hi]
  | cons y ys ih =>
      by_cases hneg : hi < 0
      · simp [bLastRow, bSpecRow, hneg]
      · rw [bLastRow, bSpecRow]
        simp only [if_neg hneg, ih, bCellHead_bSpecRow]
        rw [bMkGapXOnly_spec sc y ys lo hi]

theorem bRowUp_eq (sc : Scoring) (x : Char) (xs : List Char)
    (ys : List Char) (lo hi : Int) :
    bRowUp sc x ys (bSpecRow sc xs ys (lo + 1) (hi + 1)) lo hi =
      bSpecRow sc (x :: xs) ys lo hi := by
  induction ys generalizing lo hi with
  | nil =>
      by_cases hneg : hi < 0
      · simp [bRowUp, bSpecRow, hneg]
      · rw [bRowUp]
        rw [show bSpecRow sc (x :: xs) [] lo hi =
              [specBCell sc (x :: xs) [] lo hi] from by
          rw [bSpecRow]
          simp [if_neg hneg]]
        simp only [if_neg hneg, bCellHead_bSpecRow]
        rw [bMkGapYOnly_spec sc x xs lo hi]
  | cons y ys ih =>
      by_cases hneg : hi < 0
      · simp [bRowUp, bSpecRow, hneg]
      · have hneg1 : ¬ (hi + 1 < 0) := by omega
        rw [bRowUp]
        rw [show bSpecRow sc (x :: xs) (y :: ys) lo hi =
              specBCell sc (x :: xs) (y :: ys) lo hi ::
                bSpecRow sc (x :: xs) ys (lo - 1) (hi - 1) from by
          rw [bSpecRow]
          simp [if_neg hneg]]
        simp only [if_neg hneg]
        rw [show bSpecRow sc xs (y :: ys) (lo + 1) (hi + 1) =
              specBCell sc xs (y :: ys) (lo + 1) (hi + 1) ::
                bSpecRow sc xs ys (lo + 1 - 1) (hi + 1 - 1) from by
          rw [bSpecRow]
          simp [if_neg hneg1]]
        simp only [List.tail_cons, bCellHead_cons]
        have harith : lo + 1 - 1 = lo - 1 + 1 := by omega
        have harith2 : hi + 1 - 1 = hi - 1 + 1 := by omega
        rw [harith, harith2, ih]
        simp only [bCellHead_bSpecRow]
        have harith3 : lo - 1 + 1 = lo := by omega
        have harith4 : hi - 1 + 1 = hi := by omega
        rw [harith3, harith4, bMkMain_spec sc x y xs ys lo hi]

theorem bTable_eq (sc : Scoring) (xs ys : List Char) (lo hi : Int) :
    bTable sc xs ys lo hi = bSpecRow sc xs ys lo hi := by
  induction xs generalizing lo hi with
  | nil => exact bLastRow_eq sc ys lo hi
  | cons x xs ih =>
      rw [bTable, ih, bRowUp_eq]

/-- The tabulated banded algorithm computes exactly the banded Bellman
value at the corner. -/
theorem bandedRun_eq (sc : Scoring) (xs ys : List Char) (lo hi : Int) :
    bandedRun sc xs ys lo hi = bBellman sc xs ys none lo hi := by
  rw [bandedRun, bTable_eq, bCellHead_bSpecRow]
  rfl

-- ══════════════════════════════════════════════════════════════════
-- PART 5: certification — when the in-band optimum is the global one
-- ══════════════════════════════════════════════════════════════════

/-- Head congruence for the nonempty maximum, dodging the dependent
nonemptiness proof. -/
theorem maxOnHead {α : Type} (f : α → Int) (t : List α)
    {a a' : α} (h : a = a') :
    (a :: t).maxOn f (by simp) = (a' :: t).maxOn f (by simp) := by
  subst h
  rfl

/-- Exchanging the fold accumulator for one with a no-smaller value
that still lies strictly below the final maximum leaves the earliest
maximum unchanged. -/
theorem maxOn_acc_exchange {α : Type} (f : α → Int) (b : α)
    (t : List α) :
    ∀ (acc1 acc2 : α),
      (acc1 :: t).maxOn f (by simp) = b → f acc2 < f b →
      f acc1 ≤ f acc2 →
      (acc2 :: t).maxOn f (by simp) = b := by
  induction t with
  | nil =>
      intro acc1 acc2 hfold hlt hle
      have h1 : acc1 = b := hfold
      rw [h1] at hle
      omega
  | cons e t ih =>
      intro acc1 acc2 hfold hlt hle
      rw [List.maxOn_cons_cons] at hfold ⊢
      by_cases hsame : maxOn f acc1 e = maxOn f acc2 e
      · rw [maxOnHead f t hsame] at hfold
        exact hfold
      · by_cases h1 : f e ≤ f acc1
        · have h2 : f e ≤ f acc2 := by omega
          rw [maxOnHead f t (maxOn_eq_left h1)] at hfold
          rw [maxOnHead f t (maxOn_eq_left h2)]
          exact ih acc1 acc2 hfold hlt hle
        · by_cases h2 : f e ≤ f acc2
          · rw [maxOnHead f t (maxOn_eq_right h1)] at hfold
            rw [maxOnHead f t (maxOn_eq_left h2)]
            exact ih e acc2 hfold hlt (by omega)
          · exfalso
            apply hsame
            rw [maxOn_eq_right h1, maxOn_eq_right h2]

/-- Rejected elements strictly below the final maximum can be dropped
from the fold without changing the earliest maximum. -/
theorem maxOn_filter_fold {α : Type} (q : α → Bool) (f : α → Int)
    (b : α) (t : List α) :
    ∀ (acc : α),
      (acc :: t.filter q).maxOn f (by simp) = b →
      (∀ c ∈ t, q c = false → f c < f b) →
      (acc :: t).maxOn f (by simp) = b := by
  induction t with
  | nil =>
      intro acc hfold _
      simpa using hfold
  | cons c t ih =>
      intro acc hfold hout
      by_cases hqc : q c = true
      · rw [List.filter_cons_of_pos hqc, List.maxOn_cons_cons] at hfold
        rw [List.maxOn_cons_cons]
        exact ih (maxOn f acc c) hfold
          (fun d hd hqd => hout d (List.mem_cons_of_mem c hd) hqd)
      · have hqc' : q c = false := by
          cases hv : q c
          · rfl
          · exact absurd hv hqc
        rw [List.filter_cons_of_neg (by simp [hqc'])] at hfold
        have hacc := ih acc hfold
          (fun d hd hqd => hout d (List.mem_cons_of_mem c hd) hqd)
        rw [List.maxOn_cons_cons]
        by_cases hcase : f c ≤ f acc
        · rw [maxOnHead f t (maxOn_eq_left hcase)]
          exact hacc
        · rw [maxOnHead f t (maxOn_eq_right hcase)]
          exact maxOn_acc_exchange f b t acc c hacc
            (hout c (List.mem_cons_self) hqc') (by omega)

/-- If the earliest maximum of a filtered list strictly beats every
rejected element, it is the earliest maximum of the whole list.  (The
branch-and-bound transfer: the filter preserves relative order, and no
tie can hide among the rejected elements.) -/
theorem maxOn?_of_filter_maxOn? {α : Type} (q : α → Bool) (f : α → Int)
    (l : List α) (b : α)
    (hq : (l.filter q).maxOn? f = some b)
    (hout : ∀ a ∈ l, q a = false → f a < f b) :
    l.maxOn? f = some b := by
  cases l with
  | nil => simp at hq
  | cons a t =>
      by_cases hqa : q a = true
      · rw [List.filter_cons_of_pos hqa,
          List.maxOn?_cons_eq_some_maxOn] at hq
        rw [List.maxOn?_cons_eq_some_maxOn]
        simp only [Option.some.injEq] at hq ⊢
        exact maxOn_filter_fold q f b t a hq
          (fun c hc hqc => hout c (List.mem_cons_of_mem a hc) hqc)
      · have hqa' : q a = false := by
          cases hv : q a
          · rfl
          · exact absurd hv hqa
        rw [List.filter_cons_of_neg (by simp [hqa'])] at hq
        have hfa : f a < f b := hout a (List.mem_cons_self) hqa'
        have hfilterb := List.maxOn_eq_of_maxOn?_eq_some hq
        have h1 : (a :: t.filter q).maxOn f (by simp) = b := by
          rw [List.maxOn_cons]
          have hne : t.filter q ≠ [] := by
            intro hnil
            rw [hnil] at hq
            simp at hq
          rw [dif_neg hne, hfilterb]
          exact maxOn_eq_right (by omega)
        rw [List.maxOn?_cons_eq_some_maxOn]
        simp only [Option.some.injEq]
        exact maxOn_filter_fold q f b t a h1
          (fun c hc hqc => hout c (List.mem_cons_of_mem a hc) hqc)

-- ── The band geometry ──

def bandLo (m n : Nat) (w : Nat) : Int :=
  min 0 ((n : Int) - m) - w

def bandHi (m n : Nat) (w : Nat) : Int :=
  max 0 ((n : Int) - m) + w

/-- The certification bound: every valid walk that leaves the band has
twice its score at most this value (under a reasonable scoring). -/
def offBandBound (sc : Scoring) (m n : Nat) (w : Nat) : Int :=
  let G : Int := (((n : Int) - m).natAbs : Int) + 2 * (w + 1)
  sc.matchScore * ((m : Int) + n - G) + 2 * sc.gapExtend * G +
    2 * sc.gapOpen

/-- The closed integer inequality behind certification: the score of a
walk with `G` gap columns is bounded once `G` exceeds the forced
minimum, under the sign conditions of a reasonable scoring. -/
theorem bound_arith (M X E O mat mis G runs m n Gmin : Int)
    (hM : 0 ≤ M) (hX : X ≤ M) (hE : E ≤ 0) (hO : O ≤ 0)
    (hmat : 0 ≤ mat) (hmis : 0 ≤ mis) (hruns : 1 ≤ runs)
    (hcons : 2 * (mat + mis) = m + n - G)
    (hGmin : Gmin ≤ G) :
    2 * (M * mat + X * mis + E * G + O * runs) ≤
      M * (m + n - Gmin) + 2 * E * Gmin + 2 * O := by
  have h1 : X * mis ≤ M * mis := by
    have hnn := Int.mul_nonneg (show (0 : Int) ≤ M - X by omega) hmis
    simp only [Int.sub_mul] at hnn
    omega
  have h2 : O * runs ≤ O := by
    have hnn := Int.mul_nonneg (show (0 : Int) ≤ -O by omega)
      (show (0 : Int) ≤ runs - 1 by omega)
    simp only [Int.mul_sub, Int.neg_mul, Int.mul_one] at hnn
    omega
  have h3 : (0 : Int) ≤
      M * G - M * Gmin - (2 * (E * G) - 2 * (E * Gmin)) := by
    have hnn := Int.mul_nonneg
      (show (0 : Int) ≤ M - 2 * E by omega)
      (show (0 : Int) ≤ G - Gmin by omega)
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_assoc,
      Int.mul_assoc] at hnn
    exact hnn
  have h4 : M * (m + n - G) = M * m + M * n - M * G := by
    rw [Int.mul_sub, Int.mul_add]
  have e3 : M * (2 * (mat + mis)) = 2 * (M * mat + M * mis) := by
    rw [Int.mul_comm 2 (mat + mis), ← Int.mul_assoc,
      Int.mul_comm (M * (mat + mis)) 2, Int.mul_add]
  have h5 : 2 * (M * mat + M * mis) = M * m + M * n - M * G := by
    rw [← e3, ← h4]
    exact congrArg (fun t => M * t) hcons
  have e1 : M * (m + n - Gmin) = M * m + M * n - M * Gmin := by
    rw [Int.mul_sub, Int.mul_add]
  rw [e1, Int.mul_assoc 2 E Gmin]
  omega

theorem two_score_le_offBandBound (sc : Scoring) (p : List Step)
    (xs ys : List Char) (w : Nat)
    (hr : ReasonableScoring sc)
    (hvalid : IsMonotoneWalk p xs ys)
    (hnb : inBand (bandLo xs.length ys.length w)
      (bandHi xs.length ys.length w) p = false) :
    2 * scoreWalk sc p xs ys none ≤
      offBandBound sc xs.length ys.length w := by
  obtain ⟨hx, hy⟩ := hvalid
  rw [xConsumed_sum_eq_counts] at hx
  rw [yConsumed_sum_eq_counts] at hy
  obtain ⟨hmm, hgx, hgy⟩ := stats_eq_counts p xs ys none
    ⟨by rw [xConsumed_sum_eq_counts]; exact hx,
     by rw [yConsumed_sum_eq_counts]; exact hy⟩
  have hcnb := counts_of_not_inBand _ _ p hnb
  simp only [bandLo, bandHi] at hcnb
  -- at least one gap run is opened
  have hruns : 1 ≤ (walkStats p xs ys none).runCount := by
    rcases Nat.eq_zero_or_pos ((walkStats p xs ys none).runCount) with
      h0 | h0
    · exfalso
      have hz := gaps_eq_zero_of_runs_zero p xs ys none
        (by constructor <;> simp) h0
      rcases hcnb with hbad | hbad <;> omega
    · omega
  -- the minimal number of gap columns forced by leaving the band
  have hGmin :
      (((ys.length : Int) - xs.length).natAbs : Int) + 2 * (w + 1) ≤
        ((walkStats p xs ys none).gapXCount : Int) +
          ((walkStats p xs ys none).gapYCount : Int) := by
    rcases hcnb with hbad | hbad <;> omega
  -- expand the score and finish with pure integer arithmetic
  rw [scoreWalk_eq_stats, statsScore, offBandBound]
  exact bound_arith sc.matchScore sc.mismatchScore sc.gapExtend
    sc.gapOpen
    ((walkStats p xs ys none).matchCount : Int)
    ((walkStats p xs ys none).mismatchCount : Int)
    (((walkStats p xs ys none).gapXCount : Int) +
      ((walkStats p xs ys none).gapYCount : Int))
    ((walkStats p xs ys none).runCount : Int)
    (xs.length : Int) (ys.length : Int)
    ((((ys.length : Int) - xs.length).natAbs : Int) + 2 * (w + 1))
    hr.match_pos hr.match_best hr.extend_neg hr.open_neg
    (by omega) (by omega) (by omega) (by omega) hGmin

/-- The certified case: an in-band optimum whose doubled score strictly
beats the off-band bound is the global optimum, tie-break included. -/
theorem certified_global (sc : Scoring) (xs ys : List Char) (w : Nat)
    (hr : ReasonableScoring sc)
    (p : List Step) (s : Int)
    (hband : bandedRun sc xs ys (bandLo xs.length ys.length w)
      (bandHi xs.length ys.length w) = some (p, s))
    (hcert : offBandBound sc xs.length ys.length w < 2 * s) :
    getBestAlignment sc xs ys = some (p, s) := by
  rw [bandedRun_eq, ← bandedBestAux_eq_bBellman] at hband
  rw [getBestAlignment_eq_bestAux, bestAux]
  rw [bandedBestAux] at hband
  -- move the filter to the pair level
  have hbridge :
      ((allPaths xs ys).filter
        (fun q => inBand (bandLo xs.length ys.length w)
          (bandHi xs.length ys.length w) q)).map
          (fun q => (q, scoreWalk sc q xs ys none)) =
        ((allPaths xs ys).map
          (fun q => (q, scoreWalk sc q xs ys none))).filter
          (fun item => inBand (bandLo xs.length ys.length w)
            (bandHi xs.length ys.length w) item.1) := by
    induction allPaths xs ys with
    | nil => rfl
    | cons a t ih =>
        by_cases ha : inBand (bandLo xs.length ys.length w)
            (bandHi xs.length ys.length w) a = true <;>
          simp [List.filter_cons, ha, ih]
  rw [hbridge] at hband
  apply maxOn?_of_filter_maxOn? _ _ _ _ hband
  intro item hitem hout
  obtain ⟨q, hqmem, rfl⟩ := List.mem_map.mp hitem
  simp only at hout ⊢
  have hqvalid := isMonotoneWalk_of_mem_allPaths xs ys q hqmem
  have hbound := two_score_le_offBandBound sc q xs ys w hr hqvalid hout
  omega

-- ══════════════════════════════════════════════════════════════════
-- PART 6: the band-doubling driver and the unconditional theorem
-- ══════════════════════════════════════════════════════════════════

/-- One doubling loop.  Fuel only bounds the recursion; correctness is
independent of it, because every exit path is proved exact: fuel
exhaustion and full-width bands fall back to the proved Gotoh
implementation, and early exits are certified. -/
def bandDoublingGo (sc : Scoring) (xs ys : List Char) : Nat → Nat →
    Option (List Step × Int)
  | 0, _ => gotohFusedAlign sc xs ys
  | fuel + 1, w =>
      if bandLo xs.length ys.length w ≤ -(xs.length : Int) ∧
          (ys.length : Int) ≤ bandHi xs.length ys.length w then
        gotohFusedAlign sc xs ys
      else
        match bandedRun sc xs ys (bandLo xs.length ys.length w)
            (bandHi xs.length ys.length w) with
        | some (p, s) =>
            if offBandBound sc xs.length ys.length w < 2 * s then
              some (p, s)
            else bandDoublingGo sc xs ys fuel (2 * w + 1)
        | none => bandDoublingGo sc xs ys fuel (2 * w + 1)

/-- The adaptive wavefront-style aligner: banded computation with
runtime-certified band doubling, exact for every scoring and input. -/
def bandDoublingAlign (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  if reasonableB sc then bandDoublingGo sc xs ys (xs.length + ys.length + 2) 2
  else gotohFusedAlign sc xs ys

theorem bandDoublingGo_eq (sc : Scoring) (xs ys : List Char)
    (hr : ReasonableScoring sc) :
    ∀ fuel w, bandDoublingGo sc xs ys fuel w = getBestAlignment sc xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro w
      rw [bandDoublingGo, gotohFusedAlign_equals_getBestAlignment]
  | succ fuel ih =>
      intro w
      rw [bandDoublingGo]
      split
      · rw [gotohFusedAlign_equals_getBestAlignment]
      · split
        · next p s heq =>
            split
            · next hcert =>
                exact (certified_global sc xs ys w hr p s heq hcert).symm
            · next hcert => exact ih (2 * w + 1)
        · next heq => exact ih (2 * w + 1)

/-- THE THEOREM: the adaptive aligner returns exactly the frozen spec's
answer — best path and score, tie-break included — for every scoring
(reasonable or not) and every pair of strings.  No hypotheses. -/
theorem bandDoublingAlign_equals_getBestAlignment (sc : Scoring)
    (xs ys : List Char) :
    bandDoublingAlign sc xs ys = getBestAlignment sc xs ys := by
  rw [bandDoublingAlign]
  by_cases h : reasonableB sc = true
  · rw [if_pos h]
    exact bandDoublingGo_eq sc xs ys ((reasonableB_iff sc).mp h) _ _
  · rw [if_neg h]
    exact gotohFusedAlign_equals_getBestAlignment sc xs ys

-- Compile-time smoke tests against the spec's own demo answers.
#guard bandDoublingAlign demoScoring ['A','B','C'] ['A','B','B','C']
  == getBestAlignment demoScoring ['A','B','C'] ['A','B','B','C']
#guard bandDoublingAlign demoScoring ['A','B','B','A'] ['A','A']
  == some ([.diag, .gapY, .gapY, .diag], -1)
#guard bandDoublingAlign demoScoring [] [] == some ([], 0)
#guard bandDoublingAlign demoScoring [] ['A','B'] == some ([.gapX, .gapX], -5)
#guard bandDoublingAlign demoScoring ['A','C','B'] ['A','C','B']
  == some ([.diag, .diag, .diag], 6)
-- An unreasonable scoring (positive gaps) must fall back and still
-- agree with the spec.
#guard
  (let weird : Scoring :=
    { matchScore := -2, mismatchScore := 3, gapOpen := 5, gapExtend := 1 }
   bandDoublingAlign weird ['A','B'] ['B','A'] ==
     getBestAlignment weird ['A','B'] ['B','A'])

end AlignmentSpec
