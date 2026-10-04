import ReadWindowTrimmer.Incremental

namespace ReadWindow


/-
`bestPrefixSummary baseScore scores` returns two numbers:

* `.1` is the length of the best nonempty prefix of `scores`.
* `.2` is that prefix's score.

When two prefixes have the same score, it keeps the shorter prefix.  That is
exactly the tie rule used by the frozen exhaustive implementation for windows
that have the same start index.

The empty-list value `(0, 0)` is only a convenient value for the recursive
definition.  It is never emitted as a candidate window.
-/
def extendPrefixSummary
    (baseScore : Int → Int)
    (firstScore : Int)
    (laterBest : Nat × Int)
    : Nat × Int :=
  if 0 < laterBest.2 then
    (laterBest.1 + 1, baseScore firstScore + laterBest.2)
  else
    (1, baseScore firstScore)


def bestPrefixSummary
    (baseScore : Int → Int)
    : List Int → Nat × Int
  | [] =>
      (0, 0)
  | firstScore :: laterScores =>
      let laterBest : Nat × Int := bestPrefixSummary baseScore laterScores
      extendPrefixSummary baseScore firstScore laterBest


/-
This computes `bestPrefixSummary` for every nonempty suffix in one right-to-left
pass.  The first element describes the whole input; the second describes the
input without its first element; and so on.
-/
def bestPrefixSummaries
    (baseScore : Int → Int)
    : List Int → List (Nat × Int)
  | [] =>
      []
  | firstScore :: laterScores =>
      let laterSummaries : List (Nat × Int) :=
        bestPrefixSummaries baseScore laterScores
      let laterBest : Nat × Int := laterSummaries.headD (0, 0)
      let currentBest : Nat × Int :=
        extendPrefixSummary baseScore firstScore laterBest
      currentBest :: laterSummaries


def attachStartIndices
    : Nat → List (Nat × Int) → List (Window × Int)
  | _, [] =>
      []
  | startIndex, (windowLength, windowScore) :: laterSummaries =>
      (((startIndex, startIndex + windowLength), windowScore) ::
        attachStartIndices (startIndex + 1) laterSummaries)


def scoredWindowsLinear
    (scores : List Int)
    (baseScore : Int → Int)
    : List (Window × Int) :=
  attachStartIndices 0 (bestPrefixSummaries baseScore scores)


def getBestWindowLinear
    (scores : List Int)
    (baseScore : Int → Int)
    : Option Window :=
  ((scoredWindowsLinear scores baseScore).maxOn? fun item => item.2).map fun item =>
    item.1


/-
A deliberately simple specification list.  Unlike `bestPrefixSummaries`, this
recomputes `bestPrefixSummary` separately for every suffix.  We use it only in
proofs, never in the benchmarked linear algorithm.
-/
def bestPrefixSummariesSpecification
    (baseScore : Int → Int)
    : List Int → List (Nat × Int)
  | [] =>
      []
  | allScores@(_ :: laterScores) =>
      bestPrefixSummary baseScore allScores ::
        bestPrefixSummariesSpecification baseScore laterScores


theorem bestPrefixSummaries_headD
    (scores : List Int)
    (baseScore : Int → Int)
    :
    (bestPrefixSummaries baseScore scores).headD (0, 0) =
      bestPrefixSummary baseScore scores := by
  induction scores with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [bestPrefixSummaries, List.headD_cons, bestPrefixSummary]
      simp only [inductionHypothesis]


theorem bestPrefixSummaries_equals_specification
    (scores : List Int)
    (baseScore : Int → Int)
    :
    bestPrefixSummaries baseScore scores =
      bestPrefixSummariesSpecification baseScore scores := by
  induction scores with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [bestPrefixSummaries, bestPrefixSummariesSpecification]
      simp only [bestPrefixSummaries_headD]
      rw [inductionHypothesis]
      rfl


/-
This theorem says that `bestPrefixSummary` really is the result of running
`List.maxOn?` over every nonempty window beginning at one fixed start index.
-/
theorem scoreWindowsStartingAt_maxOn?_equals_bestPrefixSummary
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    (currentEndIndex : Nat)
    (runningScore : Int)
    :
    (scoreWindowsStartingAt
        baseScore
        startIndex
        currentEndIndex
        runningScore
        scores).maxOn? (fun item => item.2) =
      match scores with
      | [] =>
          none
      | _ :: _ =>
          some
            ( ( (startIndex,
                  currentEndIndex + (bestPrefixSummary baseScore scores).1),
                runningScore + (bestPrefixSummary baseScore scores).2 ) ) := by
  induction scores generalizing currentEndIndex runningScore with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      rw [scoreWindowsStartingAt]
      rw [List.maxOn?_cons]
      rw [inductionHypothesis]
      rw [show
        bestPrefixSummary baseScore (firstScore :: laterScores) =
          extendPrefixSummary
            baseScore
            firstScore
            (bestPrefixSummary baseScore laterScores) from rfl]
      cases laterScores with
      | nil =>
          simp [bestPrefixSummary, extendPrefixSummary]
      | cons secondScore remainingScores =>
          simp only [Option.elim_some]
          by_cases comparison :
              0 < (bestPrefixSummary baseScore (secondScore :: remainingScores)).2
          · rw [extendPrefixSummary, if_pos comparison]
            rw [maxOn_eq_right_of_lt]
            · apply congrArg some
              apply Prod.ext
              · apply Prod.ext
                · rfl
                · change
                    currentEndIndex + 1 +
                        (bestPrefixSummary
                          baseScore
                          (secondScore :: remainingScores)).1 =
                      currentEndIndex +
                        ((bestPrefixSummary
                          baseScore
                          (secondScore :: remainingScores)).1 + 1)
                  omega
              · change
                  runningScore + baseScore firstScore +
                      (bestPrefixSummary
                        baseScore
                        (secondScore :: remainingScores)).2 =
                    runningScore +
                      (baseScore firstScore +
                        (bestPrefixSummary
                          baseScore
                          (secondScore :: remainingScores)).2)
                omega
            · omega
          · rw [extendPrefixSummary, if_neg comparison]
            rw [maxOn_eq_left (by omega)]


def scoredWindowsBySuffix
    (baseScore : Int → Int)
    : Nat → List Int → List (Window × Int)
  | _, [] =>
      []
  | startIndex, allScores@(_ :: laterScores) =>
      scoreWindowsStartingAt baseScore startIndex startIndex 0 allScores ++
        scoredWindowsBySuffix baseScore (startIndex + 1) laterScores


def bestCandidatesSpecification
    (baseScore : Int → Int)
    : Nat → List Int → List (Window × Int)
  | _, [] =>
      []
  | startIndex, allScores@(_ :: laterScores) =>
      let summary : Nat × Int := bestPrefixSummary baseScore allScores
      (((startIndex, startIndex + summary.1), summary.2) ::
        bestCandidatesSpecification baseScore (startIndex + 1) laterScores)


theorem attachStartIndices_specification
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    :
    attachStartIndices
        startIndex
        (bestPrefixSummariesSpecification baseScore scores) =
      bestCandidatesSpecification baseScore startIndex scores := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp [bestPrefixSummariesSpecification, bestCandidatesSpecification,
        attachStartIndices, inductionHypothesis]


theorem scoredWindowsBySuffix_maxOn?_equals_bestCandidates
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    :
    (scoredWindowsBySuffix baseScore startIndex scores).maxOn?
        (fun item => item.2) =
      (bestCandidatesSpecification baseScore startIndex scores).maxOn?
        (fun item => item.2) := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [scoredWindowsBySuffix, bestCandidatesSpecification,
        List.maxOn?_append]
      rw [scoreWindowsStartingAt_maxOn?_equals_bestPrefixSummary]
      rw [inductionHypothesis]
      rw [List.maxOn?_cons]
      simp only [Int.zero_add]
      cases (bestCandidatesSpecification baseScore (startIndex + 1) laterScores).maxOn?
          (fun item => item.2) <;> rfl


def scoredWindowsIncrementalFrom
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    : List (Window × Int) :=
  (List.range scores.length).flatMap fun offset =>
    scoreWindowsStartingAt
      baseScore
      (startIndex + offset)
      (startIndex + offset)
      0
      (scores.drop offset)


theorem flatMap_congr_explicit
    (items : List α)
    (firstFunction secondFunction : α → List β)
    (functionsAgree : ∀ item ∈ items, firstFunction item = secondFunction item)
    :
    items.flatMap firstFunction = items.flatMap secondFunction := by
  induction items with
  | nil =>
      rfl
  | cons firstItem laterItems inductionHypothesis =>
      simp only [List.flatMap_cons]
      rw [functionsAgree firstItem (by simp)]
      rw [inductionHypothesis]
      intro item itemIsInLaterItems
      exact functionsAgree item (by simp [itemIsInLaterItems])


theorem scoredWindowsBySuffix_equals_incrementalFrom
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    :
    scoredWindowsBySuffix baseScore startIndex scores =
      scoredWindowsIncrementalFrom scores baseScore startIndex := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [scoredWindowsBySuffix, scoredWindowsIncrementalFrom,
        List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
        List.drop_zero, Nat.add_zero, List.flatMap_map]
      rw [inductionHypothesis]
      rw [scoredWindowsIncrementalFrom]
      apply congrArg (fun remainingWindows =>
        scoreWindowsStartingAt
            baseScore
            startIndex
            startIndex
            0
            (firstScore :: laterScores) ++ remainingWindows)
      apply flatMap_congr_explicit
      intro offset offsetIsInRange
      simp only [List.drop_succ_cons]
      rw [show startIndex + 1 + offset = startIndex + offset.succ by omega]


theorem scoredWindowsBySuffix_zero_equals_incremental
    (scores : List Int)
    (baseScore : Int → Int)
    :
    scoredWindowsBySuffix baseScore 0 scores =
      scoredWindowsIncremental scores baseScore := by
  rw [scoredWindowsBySuffix_equals_incrementalFrom]
  simp [scoredWindowsIncrementalFrom, scoredWindowsIncremental]


theorem scoredWindowsLinear_maxOn?_equals_incremental
    (scores : List Int)
    (baseScore : Int → Int)
    :
    (scoredWindowsLinear scores baseScore).maxOn? (fun item => item.2) =
      (scoredWindowsIncremental scores baseScore).maxOn? (fun item => item.2) := by
  rw [scoredWindowsLinear, bestPrefixSummaries_equals_specification,
    attachStartIndices_specification]
  rw [← scoredWindowsBySuffix_maxOn?_equals_bestCandidates]
  rw [scoredWindowsBySuffix_zero_equals_incremental]


theorem getBestWindowLinear_equals_incremental
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowLinear scores baseScore =
      getBestWindowIncremental scores baseScore := by
  simp only [getBestWindowLinear, getBestWindowIncremental]
  rw [scoredWindowsLinear_maxOn?_equals_incremental]


theorem getBestWindowLinear_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowLinear scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore) := by
  rw [getBestWindowLinear_equals_incremental]
  exact getBestWindowIncremental_equals_frozen_get_best_window
    nucleotides
    scores
    baseScore

end ReadWindow
