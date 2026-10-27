import ReadWindowTrimmer.Reference

namespace ReadWindow


def scoreWindowsStartingAt
    (baseScore : Int → Int)
    (startIndex : Nat)
    (currentEndIndex : Nat)
    (runningScore : Int)
    (remainingScores : List Int)
    : List (Window × Int) :=
  match remainingScores with
  | [] =>
      []
  | firstScore :: laterScores =>
      let nextRunningScore : Int := runningScore + baseScore firstScore
      let nextEndIndex : Nat := currentEndIndex + 1
      ((startIndex, nextEndIndex), nextRunningScore) ::
        scoreWindowsStartingAt
          baseScore
          startIndex
          nextEndIndex
          nextRunningScore
          laterScores


def scoredWindowsIncremental
    (scores : List Int)
    (baseScore : Int → Int)
    : List (Window × Int) :=
  (List.range scores.length).flatMap fun startIndex =>
    scoreWindowsStartingAt
      baseScore
      startIndex
      startIndex
      0
      (scores.drop startIndex)


def getBestWindowIncremental
    (scores : List Int)
    (baseScore : Int → Int)
    : Option Window :=
  ((scoredWindowsIncremental scores baseScore).maxOn? fun item => item.2).map fun item =>
    item.1


theorem scoreWindowsStartingAt_eq_range_map
    (baseScore : Int → Int)
    (startIndex : Nat)
    (currentEndIndex : Nat)
    (runningScore : Int)
    (remainingScores : List Int)
    :
    scoreWindowsStartingAt
        baseScore
        startIndex
        currentEndIndex
        runningScore
        remainingScores =
      (List.range remainingScores.length).map fun offset =>
        ( (startIndex, currentEndIndex + offset + 1),
          runningScore +
            (((remainingScores.take (offset + 1)).map baseScore).sum) ) := by
  induction remainingScores generalizing currentEndIndex runningScore with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp [scoreWindowsStartingAt, List.range_succ_eq_map, List.map_map,
        inductionHypothesis, Int.add_assoc, Nat.add_assoc]
      omega


theorem scoredWindowsIncremental_equals_exhaustive
    (scores : List Int)
    (baseScore : Int → Int)
    :
    scoredWindowsIncremental scores baseScore =
      scoredWindowsExhaustive scores baseScore := by
  simp only [scoredWindowsIncremental, scoredWindowsExhaustive, allWindows,
    List.map_flatMap]
  congr 1
  funext startIndex
  rw [scoreWindowsStartingAt_eq_range_map]
  simp only [List.map_map, List.length_drop]
  apply List.map_congr_left
  intro offset offsetIsInRange
  simp only [scoreWindow, getWindow]
  simp [Nat.add_assoc, Int.zero_add]


theorem getBestWindowIncremental_equals_exhaustive
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowIncremental scores baseScore =
      getBestWindowExhaustive scores baseScore := by
  rw [getBestWindowIncremental, getBestWindowExhaustive,
    scoredWindowsIncremental_equals_exhaustive]


theorem getBestWindowIncremental_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowIncremental scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore) := by
  rw [getBestWindowIncremental_equals_exhaustive]
  exact getBestWindowExhaustive_equals_frozen_get_best_window
    nucleotides
    scores
    baseScore

end ReadWindow
