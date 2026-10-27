import ReadWindowTrimmer.Linear

namespace ReadWindow


/-
`FusedResult` contains only the two facts needed while the recursion returns
from the right-hand end of the score list:

* `bestPrefix` is the shortest, highest-scoring prefix at the current start.
* `bestCandidate` is the best window at the current start or any later start.

Unlike `getBestWindowLinear`, the fused implementation does not first allocate
a list containing one candidate for every start index.
-/
structure FusedResult where
  bestPrefix : Nat × Int
  bestCandidate : Window × Int
deriving Repr, DecidableEq


def fuseBestWindowsFrom
    (baseScore : Int → Int)
    : Nat → List Int → Option FusedResult
  | _, [] =>
      none
  | startIndex, firstScore :: laterScores =>
      match fuseBestWindowsFrom baseScore (startIndex + 1) laterScores with
      | none =>
          let currentPrefix : Nat × Int :=
            extendPrefixSummary baseScore firstScore (0, 0)
          let currentCandidate : Window × Int :=
            ((startIndex, startIndex + currentPrefix.1), currentPrefix.2)
          some
            { bestPrefix := currentPrefix
              bestCandidate := currentCandidate }
      | some laterResult =>
          let currentPrefix : Nat × Int :=
            extendPrefixSummary baseScore firstScore laterResult.bestPrefix
          let currentCandidate : Window × Int :=
            ((startIndex, startIndex + currentPrefix.1), currentPrefix.2)
          let bestCandidate : Window × Int :=
            maxOn (fun candidate => candidate.2)
              currentCandidate
              laterResult.bestCandidate
          some
            { bestPrefix := currentPrefix
              bestCandidate := bestCandidate }


def getBestWindowFused
    (scores : List Int)
    (baseScore : Int → Int)
    : Option Window :=
  (fuseBestWindowsFrom baseScore 0 scores).map fun result =>
    result.bestCandidate.1


def fusedSpecification
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    : Option FusedResult :=
  ((bestCandidatesSpecification baseScore startIndex scores).maxOn?
      (fun candidate => candidate.2)).map fun bestCandidate =>
    { bestPrefix := bestPrefixSummary baseScore scores
      bestCandidate := bestCandidate }


theorem fuseBestWindowsFrom_equals_specification
    (scores : List Int)
    (baseScore : Int → Int)
    (startIndex : Nat)
    :
    fuseBestWindowsFrom baseScore startIndex scores =
      fusedSpecification scores baseScore startIndex := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      cases laterScores with
      | nil =>
          simp [fuseBestWindowsFrom, fusedSpecification,
            bestCandidatesSpecification, bestPrefixSummary,
            extendPrefixSummary]
      | cons secondScore remainingScores =>
          rw [fuseBestWindowsFrom]
          rw [inductionHypothesis]
          simp only [fusedSpecification, bestCandidatesSpecification,
            List.maxOn?_cons, Option.map_some]
          rfl


theorem scoredWindowsLinear_equals_bestCandidatesSpecification
    (scores : List Int)
    (baseScore : Int → Int)
    :
    scoredWindowsLinear scores baseScore =
      bestCandidatesSpecification baseScore 0 scores := by
  rw [scoredWindowsLinear, bestPrefixSummaries_equals_specification,
    attachStartIndices_specification]


theorem getBestWindowFused_equals_linear
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowFused scores baseScore =
      getBestWindowLinear scores baseScore := by
  rw [getBestWindowFused, fuseBestWindowsFrom_equals_specification]
  rw [getBestWindowLinear, scoredWindowsLinear_equals_bestCandidatesSpecification]
  simp only [fusedSpecification]
  cases (bestCandidatesSpecification baseScore 0 scores).maxOn?
      (fun candidate => candidate.2) <;> rfl


theorem getBestWindowFused_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowFused scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore) := by
  rw [getBestWindowFused_equals_linear]
  exact getBestWindowLinear_equals_frozen_get_best_window
    nucleotides
    scores
    baseScore

end ReadWindow
