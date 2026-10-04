import AlignmentWavefront

/-!
The greedy match-extension lemma: on a matching head pair, the frozen
optimum takes the diagonal — WFA's "free extension" fact, proved for
the M state (previous step `none` or `diag`), which the pre-compact
brute-force probe showed is exactly the scope on which it holds (it
fails mid-gap: extending an open gap first can beat matching
immediately).

Everything is proved at the `bellmanAux` level — which IS the spec by
`bestAux_eq_bellmanAux` — so no walk surgery is needed.  The whole
argument reduces to:

  * swap bounds: changing the previous-step state moves the optimal
    value by at most one waived gap opening
    (`bellman_snd_none_le`, `bellman_snd_prev_le`);
  * branch bounds: the cons/cons optimum dominates each of its three
    candidates (`le_bellmanAux_cons_cons_*`);
  * two inductions (`gapX_defer_le_match` along ys,
    `gapY_defer_le_match` along xs) showing that opening a gap before
    the matching pair never beats matching now.

`ReasonableScoring` is a hypothesis of these lemmas only; the frozen
contract is untouched.
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- PART 1: value-level facts about the left-biased binary maximum
-- ══════════════════════════════════════════════════════════════════

private theorem maxOn_pair_eq_left {a b : List Step × Int} (h : b.2 ≤ a.2) :
    maxOn (fun item : List Step × Int => item.2) a b = a := by
  rw [maxOn_eq_if, if_pos h]

private theorem left_le_maxOn_snd (a b : List Step × Int) :
    a.2 ≤ (maxOn (fun item : List Step × Int => item.2) a b).2 := by
  rw [maxOn_eq_if]
  by_cases h : b.2 ≤ a.2
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

private theorem right_le_maxOn_snd (a b : List Step × Int) :
    b.2 ≤ (maxOn (fun item : List Step × Int => item.2) a b).2 := by
  rw [maxOn_eq_if]
  by_cases h : b.2 ≤ a.2
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

private theorem maxOn_snd_le {a b : List Step × Int} {c : Int}
    (h1 : a.2 ≤ c) (h2 : b.2 ≤ c) :
    (maxOn (fun item : List Step × Int => item.2) a b).2 ≤ c := by
  rw [maxOn_eq_if]
  by_cases h : b.2 ≤ a.2
  · rw [if_pos h]; exact h1
  · rw [if_neg h]; exact h2

private theorem maxOn3_snd_le (d gx gy : List Step × Int) {c : Int}
    (h1 : d.2 ≤ c) (h2 : gx.2 ≤ c) (h3 : gy.2 ≤ c) :
    (maxOn (fun item : List Step × Int => item.2)
      (maxOn (fun item : List Step × Int => item.2) d gx) gy).2 ≤ c :=
  maxOn_snd_le (maxOn_snd_le h1 h2) h3

private theorem maxOn3_pick_left (d gx gy : List Step × Int)
    (h1 : gx.2 ≤ d.2) (h2 : gy.2 ≤ d.2) :
    maxOn (fun item : List Step × Int => item.2)
      (maxOn (fun item : List Step × Int => item.2) d gx) gy = d := by
  rw [maxOn_pair_eq_left h1, maxOn_pair_eq_left h2]

-- ══════════════════════════════════════════════════════════════════
-- PART 2: candidate bounds at a cons/cons node of `bellmanAux`
-- ══════════════════════════════════════════════════════════════════

theorem bellmanAux_cons_cons_snd_le (sc : Scoring) (x : Char)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step)
    {c : Int}
    (h1 : diagCost sc x y + (bellmanAux sc xs ys (some .diag)).2 ≤ c)
    (h2 : gapXCost sc prev +
        (bellmanAux sc (x :: xs) ys (some .gapX)).2 ≤ c)
    (h3 : gapYCost sc prev +
        (bellmanAux sc xs (y :: ys) (some .gapY)).2 ≤ c) :
    (bellmanAux sc (x :: xs) (y :: ys) prev).2 ≤ c := by
  simp only [bellmanAux]
  exact maxOn3_snd_le _ _ _ h1 h2 h3

theorem le_bellmanAux_cons_cons_diag (sc : Scoring) (x : Char)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step) :
    diagCost sc x y + (bellmanAux sc xs ys (some .diag)).2 ≤
      (bellmanAux sc (x :: xs) (y :: ys) prev).2 := by
  simp only [bellmanAux]
  exact Int.le_trans (left_le_maxOn_snd _ _) (left_le_maxOn_snd _ _)

theorem le_bellmanAux_cons_cons_gapX (sc : Scoring) (x : Char)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step) :
    gapXCost sc prev + (bellmanAux sc (x :: xs) ys (some .gapX)).2 ≤
      (bellmanAux sc (x :: xs) (y :: ys) prev).2 := by
  simp only [bellmanAux]
  exact Int.le_trans (right_le_maxOn_snd _ _) (left_le_maxOn_snd _ _)

theorem le_bellmanAux_cons_cons_gapY (sc : Scoring) (x : Char)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step) :
    gapYCost sc prev + (bellmanAux sc xs (y :: ys) (some .gapY)).2 ≤
      (bellmanAux sc (x :: xs) (y :: ys) prev).2 := by
  simp only [bellmanAux]
  exact right_le_maxOn_snd _ _

/-- If both gap candidates stay at or below the diagonal candidate, the
left-biased maximum returns the diagonal candidate exactly (ties go to
the diagonal — the same direction as the spec's lexicographic policy). -/
theorem bellmanAux_cons_cons_eq_diag (sc : Scoring) (x : Char)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step)
    (h1 : gapXCost sc prev +
        (bellmanAux sc (x :: xs) ys (some .gapX)).2 ≤
      diagCost sc x y + (bellmanAux sc xs ys (some .diag)).2)
    (h2 : gapYCost sc prev +
        (bellmanAux sc xs (y :: ys) (some .gapY)).2 ≤
      diagCost sc x y + (bellmanAux sc xs ys (some .diag)).2) :
    bellmanAux sc (x :: xs) (y :: ys) prev =
      (.diag :: (bellmanAux sc xs ys (some .diag)).1,
       diagCost sc x y + (bellmanAux sc xs ys (some .diag)).2) := by
  simp only [bellmanAux]
  exact maxOn3_pick_left _ _ _ h1 h2

-- ══════════════════════════════════════════════════════════════════
-- PART 3: cost comparisons across previous-step states
-- ══════════════════════════════════════════════════════════════════

theorem gapXCost_none_eq (sc : Scoring) :
    gapXCost sc none = sc.gapOpen + sc.gapExtend := by
  simp [gapXCost]

theorem gapYCost_none_eq (sc : Scoring) :
    gapYCost sc none = sc.gapOpen + sc.gapExtend := by
  simp [gapYCost]

theorem gapXCost_gapX_eq (sc : Scoring) :
    gapXCost sc (some .gapX) = sc.gapExtend := by
  simp [gapXCost]

theorem gapYCost_gapY_eq (sc : Scoring) :
    gapYCost sc (some .gapY) = sc.gapExtend := by
  simp [gapYCost]

theorem gapXCost_gapY_eq (sc : Scoring) :
    gapXCost sc (some .gapY) = sc.gapOpen + sc.gapExtend := by
  simp [gapXCost]

theorem gapYCost_gapX_eq (sc : Scoring) :
    gapYCost sc (some .gapX) = sc.gapOpen + sc.gapExtend := by
  simp [gapYCost]

theorem gapXCost_none_le_prev (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (prev : Option Step) :
    gapXCost sc none ≤ gapXCost sc prev := by
  by_cases h : prev = some Step.gapX <;> simp [gapXCost, h] <;> omega

theorem gapYCost_none_le_prev (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (prev : Option Step) :
    gapYCost sc none ≤ gapYCost sc prev := by
  by_cases h : prev = some Step.gapY <;> simp [gapYCost, h] <;> omega

theorem gapXCost_prev_le_none_sub (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (prev : Option Step) :
    gapXCost sc prev ≤ gapXCost sc none - sc.gapOpen := by
  by_cases h : prev = some Step.gapX <;> simp [gapXCost, h] <;> omega

theorem gapYCost_prev_le_none_sub (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (prev : Option Step) :
    gapYCost sc prev ≤ gapYCost sc none - sc.gapOpen := by
  by_cases h : prev = some Step.gapY <;> simp [gapYCost, h] <;> omega

theorem diagCost_le_match (sc : Scoring) (hr : ReasonableScoring sc)
    (x y : Char) : diagCost sc x y ≤ sc.matchScore := by
  by_cases h : x = y
  · simp [diagCost, h]
  · simp [diagCost, h]; exact hr.match_best

-- ══════════════════════════════════════════════════════════════════
-- PART 4: swap bounds — the previous-step state moves the optimum by
-- at most one waived gap opening (the recursive calls of `bellmanAux`
-- have hard-coded previous states, so no induction is needed).
-- ══════════════════════════════════════════════════════════════════

/-- Starting mid-gap is never worse than starting fresh: the only
difference is a possible waived opening charge on the first column. -/
theorem bellman_snd_none_le (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (prev : Option Step) :
    (bellmanAux sc xs ys none).2 ≤ (bellmanAux sc xs ys prev).2 := by
  have hO := hr.open_neg
  cases xs with
  | nil =>
      cases ys with
      | nil => simp [bellmanAux]
      | cons y ys =>
          have h := gapXCost_none_le_prev sc hO prev
          simp [bellmanAux]
          omega
  | cons x xs =>
      cases ys with
      | nil =>
          have h := gapYCost_none_le_prev sc hO prev
          simp [bellmanAux]
          omega
      | cons y ys =>
          apply bellmanAux_cons_cons_snd_le
          · exact le_bellmanAux_cons_cons_diag sc x xs y ys prev
          · have h1 := gapXCost_none_le_prev sc hO prev
            have h2 := le_bellmanAux_cons_cons_gapX sc x xs y ys prev
            omega
          · have h1 := gapYCost_none_le_prev sc hO prev
            have h2 := le_bellmanAux_cons_cons_gapY sc x xs y ys prev
            omega

/-- Starting mid-gap gains at most one waived opening over starting
fresh. -/
theorem bellman_snd_prev_le (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (prev : Option Step) :
    (bellmanAux sc xs ys prev).2 ≤
      (bellmanAux sc xs ys none).2 - sc.gapOpen := by
  have hO := hr.open_neg
  cases xs with
  | nil =>
      cases ys with
      | nil => simp [bellmanAux]; omega
      | cons y ys =>
          have h := gapXCost_prev_le_none_sub sc hO prev
          simp [bellmanAux]
          omega
  | cons x xs =>
      cases ys with
      | nil =>
          have h := gapYCost_prev_le_none_sub sc hO prev
          simp [bellmanAux]
          omega
      | cons y ys =>
          apply bellmanAux_cons_cons_snd_le
          · have h := le_bellmanAux_cons_cons_diag sc x xs y ys none
            omega
          · have h1 := gapXCost_prev_le_none_sub sc hO prev
            have h2 := le_bellmanAux_cons_cons_gapX sc x xs y ys none
            omega
          · have h1 := gapYCost_prev_le_none_sub sc hO prev
            have h2 := le_bellmanAux_cons_cons_gapY sc x xs y ys none
            omega

-- ══════════════════════════════════════════════════════════════════
-- PART 5: branch bounds — the fresh-state optimum dominates each of
-- its own gap branches (equality on the degenerate shapes).
-- ══════════════════════════════════════════════════════════════════

theorem gapX_branch_le_bellman (sc : Scoring) (prev : Option Step)
    (xs : List Char) (z : Char) (zs : List Char) :
    gapXCost sc prev + (bellmanAux sc xs zs (some .gapX)).2 ≤
      (bellmanAux sc xs (z :: zs) prev).2 := by
  cases xs with
  | nil => simp [bellmanAux]
  | cons w ws => exact le_bellmanAux_cons_cons_gapX sc w ws z zs prev

theorem gapY_branch_le_bellman (sc : Scoring) (prev : Option Step)
    (w : Char) (ws ys : List Char) :
    gapYCost sc prev + (bellmanAux sc ws ys (some .gapY)).2 ≤
      (bellmanAux sc (w :: ws) ys prev).2 := by
  cases ys with
  | nil => simp [bellmanAux]
  | cons z zs => exact le_bellmanAux_cons_cons_gapY sc w ws z zs prev

-- ══════════════════════════════════════════════════════════════════
-- PART 6: the two exchange inductions.  Opening (or continuing) a gap
-- before dealing with the current position never beats taking the
-- diagonal now, when scores are reasonable.
-- ══════════════════════════════════════════════════════════════════

/-- The pure-extension exchange: extending an already-open gap-in-x
once more never beats taking the diagonal now, judged in the same
mid-gapX context on both sides.  This is the statement that carries
the induction — it charges only `gapExtend` per level, so no opening
charge leaks. -/
theorem gapX_extend_le_match (sc : Scoring) (hr : ReasonableScoring sc) :
    ∀ (ys xs : List Char) (x : Char),
      sc.gapExtend + (bellmanAux sc (x :: xs) ys (some .gapX)).2 ≤
        sc.matchScore + (bellmanAux sc xs ys (some .gapX)).2 := by
  intro ys
  induction ys with
  | nil =>
      intro xs x
      have hM := hr.match_pos
      have hE := hr.extend_neg
      have hO := hr.open_neg
      have hswu := bellman_snd_prev_le sc hr xs [] (some .gapY)
      have hsw := bellman_snd_none_le sc hr xs [] (some .gapX)
      have hgyx := gapYCost_gapX_eq sc
      simp [bellmanAux]
      omega
  | cons z zs ih =>
      intro xs x
      have hM := hr.match_pos
      have hE := hr.extend_neg
      have hO := hr.open_neg
      have hbrx := gapX_branch_le_bellman sc (some .gapX) xs z zs
      have hgxx := gapXCost_gapX_eq sc
      have hmain :
          (bellmanAux sc (x :: xs) (z :: zs) (some .gapX)).2 ≤
            sc.matchScore + (bellmanAux sc xs (z :: zs) (some .gapX)).2 -
              sc.gapExtend := by
        apply bellmanAux_cons_cons_snd_le
        · have hdm := diagCost_le_match sc hr x z
          have hdn : (bellmanAux sc xs zs (some .diag)).2 =
              (bellmanAux sc xs zs none).2 :=
            congrArg Prod.snd (bellmanAux_diag_eq_none sc xs zs)
          have hsw := bellman_snd_none_le sc hr xs zs (some .gapX)
          omega
        · have hihx := ih xs x
          omega
        · have hgyx := gapYCost_gapX_eq sc
          have hswu := bellman_snd_prev_le sc hr xs (z :: zs) (some .gapY)
          have hsw2 := bellman_snd_none_le sc hr xs (z :: zs) (some .gapX)
          omega
      omega

/-- Mirror image for gap-in-y extension. -/
theorem gapY_extend_le_match (sc : Scoring) (hr : ReasonableScoring sc) :
    ∀ (xs ys : List Char) (y : Char),
      sc.gapExtend + (bellmanAux sc xs (y :: ys) (some .gapY)).2 ≤
        sc.matchScore + (bellmanAux sc xs ys (some .gapY)).2 := by
  intro xs
  induction xs with
  | nil =>
      intro ys y
      have hM := hr.match_pos
      have hE := hr.extend_neg
      have hO := hr.open_neg
      have hswu := bellman_snd_prev_le sc hr [] ys (some .gapX)
      have hsw := bellman_snd_none_le sc hr [] ys (some .gapY)
      have hgxy := gapXCost_gapY_eq sc
      simp [bellmanAux]
      omega
  | cons w ws ih =>
      intro ys y
      have hM := hr.match_pos
      have hE := hr.extend_neg
      have hO := hr.open_neg
      have hbry := gapY_branch_le_bellman sc (some .gapY) w ws ys
      have hgyy := gapYCost_gapY_eq sc
      have hmain :
          (bellmanAux sc (w :: ws) (y :: ys) (some .gapY)).2 ≤
            sc.matchScore + (bellmanAux sc (w :: ws) ys (some .gapY)).2 -
              sc.gapExtend := by
        apply bellmanAux_cons_cons_snd_le
        · have hdm := diagCost_le_match sc hr w y
          have hdn : (bellmanAux sc ws ys (some .diag)).2 =
              (bellmanAux sc ws ys none).2 :=
            congrArg Prod.snd (bellmanAux_diag_eq_none sc ws ys)
          have hsw := bellman_snd_none_le sc hr ws ys (some .gapY)
          omega
        · have hgxy := gapXCost_gapY_eq sc
          have hswu := bellman_snd_prev_le sc hr (w :: ws) ys (some .gapX)
          have hsw2 := bellman_snd_none_le sc hr (w :: ws) ys (some .gapY)
          omega
        · have hihy := ih ys y
          omega
      omega

/-- Deferring via a gap-in-x: `M + best(xs, ys, fresh)` dominates
`(O+E) + best(x::xs, ys, mid-gapX)` for every extra character x.
Non-inductive corollary of the pure-extension exchange. -/
theorem gapX_defer_le_match (sc : Scoring) (hr : ReasonableScoring sc)
    (ys xs : List Char) (x : Char) :
    sc.gapOpen + sc.gapExtend +
        (bellmanAux sc (x :: xs) ys (some .gapX)).2 ≤
      sc.matchScore + (bellmanAux sc xs ys none).2 := by
  have hM := hr.match_pos
  have hE := hr.extend_neg
  have hO := hr.open_neg
  cases ys with
  | nil =>
      have hswap := bellman_snd_prev_le sc hr xs [] (some .gapY)
      have hgyx := gapYCost_gapX_eq sc
      simp [bellmanAux]
      omega
  | cons z zs =>
      have hmain :
          (bellmanAux sc (x :: xs) (z :: zs) (some .gapX)).2 ≤
            sc.matchScore + (bellmanAux sc xs (z :: zs) none).2 -
              (sc.gapOpen + sc.gapExtend) := by
        apply bellmanAux_cons_cons_snd_le
        · have hdm := diagCost_le_match sc hr x z
          have hdn : (bellmanAux sc xs zs (some .diag)).2 =
              (bellmanAux sc xs zs none).2 :=
            congrArg Prod.snd (bellmanAux_diag_eq_none sc xs zs)
          have hsw := bellman_snd_none_le sc hr xs zs (some .gapX)
          have hbr := gapX_branch_le_bellman sc none xs z zs
          have hgx := gapXCost_none_eq sc
          omega
        · have hgxx := gapXCost_gapX_eq sc
          have hext := gapX_extend_le_match sc hr zs xs x
          have hbr := gapX_branch_le_bellman sc none xs z zs
          have hgx := gapXCost_none_eq sc
          omega
        · have hgyx := gapYCost_gapX_eq sc
          have hswu := bellman_snd_prev_le sc hr xs (z :: zs) (some .gapY)
          omega
      omega

/-- Deferring via a gap-in-y, mirror image. -/
theorem gapY_defer_le_match (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (y : Char) :
    sc.gapOpen + sc.gapExtend +
        (bellmanAux sc xs (y :: ys) (some .gapY)).2 ≤
      sc.matchScore + (bellmanAux sc xs ys none).2 := by
  have hM := hr.match_pos
  have hE := hr.extend_neg
  have hO := hr.open_neg
  cases xs with
  | nil =>
      have hswap := bellman_snd_prev_le sc hr [] ys (some .gapX)
      have hgxy := gapXCost_gapY_eq sc
      simp [bellmanAux]
      omega
  | cons w ws =>
      have hmain :
          (bellmanAux sc (w :: ws) (y :: ys) (some .gapY)).2 ≤
            sc.matchScore + (bellmanAux sc (w :: ws) ys none).2 -
              (sc.gapOpen + sc.gapExtend) := by
        apply bellmanAux_cons_cons_snd_le
        · have hdm := diagCost_le_match sc hr w y
          have hdn : (bellmanAux sc ws ys (some .diag)).2 =
              (bellmanAux sc ws ys none).2 :=
            congrArg Prod.snd (bellmanAux_diag_eq_none sc ws ys)
          have hsw := bellman_snd_none_le sc hr ws ys (some .gapY)
          have hbr := gapY_branch_le_bellman sc none w ws ys
          have hgy := gapYCost_none_eq sc
          omega
        · have hgxy := gapXCost_gapY_eq sc
          have hswu := bellman_snd_prev_le sc hr (w :: ws) ys (some .gapX)
          omega
        · have hgyy := gapYCost_gapY_eq sc
          have hext := gapY_extend_le_match sc hr ws ys y
          have hbr := gapY_branch_le_bellman sc none w ws ys
          have hgy := gapYCost_none_eq sc
          omega
      omega

-- ══════════════════════════════════════════════════════════════════
-- PART 7: the greedy match-extension theorem
-- ══════════════════════════════════════════════════════════════════

/-- THE GREEDY MATCH-EXTENSION LEMMA.  On a matching head pair, the
frozen optimum from the fresh (M) state takes the diagonal, and its
tail is the optimum of the remainders — path, score, and tie-break all
included.  This is exactly WFA's free extension; the brute-force probe
showed the mid-gap states genuinely violate it, so this scope is
tight. -/
theorem bellmanAux_match_extend (sc : Scoring) (hr : ReasonableScoring sc)
    (x y : Char) (xs ys : List Char) (hxy : x = y) :
    bellmanAux sc (x :: xs) (y :: ys) none =
      (.diag :: (bellmanAux sc xs ys (some .diag)).1,
       sc.matchScore + (bellmanAux sc xs ys (some .diag)).2) := by
  have hdc : diagCost sc x y = sc.matchScore := by simp [diagCost, hxy]
  have hA := gapX_defer_le_match sc hr ys xs x
  have hB := gapY_defer_le_match sc hr xs ys y
  have hdn : (bellmanAux sc xs ys (some .diag)).2 =
      (bellmanAux sc xs ys none).2 :=
    congrArg Prod.snd (bellmanAux_diag_eq_none sc xs ys)
  rw [← hdc]
  apply bellmanAux_cons_cons_eq_diag
  · have hgx := gapXCost_none_eq sc
    omega
  · have hgy := gapYCost_none_eq sc
    omega

/-- The same statement with the tail's previous state written as
`none` (the two are equal by `bellmanAux_diag_eq_none`). -/
theorem bellmanAux_match_extend_none (sc : Scoring)
    (hr : ReasonableScoring sc) (x y : Char) (xs ys : List Char)
    (hxy : x = y) :
    bellmanAux sc (x :: xs) (y :: ys) none =
      (.diag :: (bellmanAux sc xs ys none).1,
       sc.matchScore + (bellmanAux sc xs ys none).2) := by
  rw [bellmanAux_match_extend sc hr x y xs ys hxy,
    bellmanAux_diag_eq_none]

/-- Spec-level corollary: the frozen `getBestAlignment` strips a
matching head pair as a free diagonal. -/
theorem getBestAlignment_match_extend (sc : Scoring)
    (hr : ReasonableScoring sc) (x y : Char) (xs ys : List Char)
    (hxy : x = y) :
    getBestAlignment sc (x :: xs) (y :: ys) =
      (getBestAlignment sc xs ys).map
        (fun r => (.diag :: r.1, sc.matchScore + r.2)) := by
  rw [getBestAlignment_eq_bestAux, bestAux_eq_bellmanAux,
    getBestAlignment_eq_bestAux, bestAux_eq_bellmanAux]
  simp [bellmanAux_match_extend_none sc hr x y xs ys hxy]

-- ── Compile-time witnesses ──

#guard reasonableB demoScoring
#guard bellmanAux demoScoring ['A','G','G'] ['A','G','C'] none ==
  (.diag :: (bellmanAux demoScoring ['G','G'] ['G','C'] none).1,
   2 + (bellmanAux demoScoring ['G','G'] ['G','C'] none).2)
#guard (bellmanAux demoScoring ['T','A'] ['T','A','A'] none).1.head? ==
  some .diag

end AlignmentSpec
