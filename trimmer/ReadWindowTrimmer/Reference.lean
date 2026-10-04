import ReadWindowTrimmer.Contract

namespace ReadWindow

abbrev Window := Nat × Nat


def allWindows (length : Nat) : List Window :=
  (List.range length).flatMap fun startIndex =>
    (List.range (length - startIndex)).map fun offset =>
      (startIndex, startIndex + offset + 1)


def getWindow (window : Window) (scores : List Int) : List Int :=
  let startIndex : Nat := window.1
  let endIndex : Nat := window.2
  (scores.drop startIndex).take (endIndex - startIndex)


def scoreWindow
    (scores : List Int)
    (baseScore : Int → Int)
    (window : Window)
    : Int :=
  ((getWindow window scores).map baseScore).sum


def scoredWindowsExhaustive
    (scores : List Int)
    (baseScore : Int → Int)
    : List (Window × Int) :=
  (allWindows scores.length).map fun window =>
    (window, scoreWindow scores baseScore window)


def getBestWindowExhaustive
    (scores : List Int)
    (baseScore : Int → Int)
    : Option Window :=
  ((scoredWindowsExhaustive scores baseScore).maxOn? fun item => item.2).map fun item =>
    item.1


theorem zip_map_same_list
    (items : List α)
    (function : α → β)
    :
    items.zip (items.map function) =
      items.map (fun item => (item, function item)) := by
  induction items with
  | nil =>
      rfl
  | cons firstItem remainingItems inductionHypothesis =>
      simp [inductionHypothesis]


theorem getBestWindowExhaustive_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowExhaustive scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore) := by
  simp only [getBestWindowExhaustive, scoredWindowsExhaustive]
  rw [← zip_map_same_list]
  rfl


theorem quality_score_greater10_equals_map_baseScore
    (scores : List Int)
    :
    quality_score_greater10 scores = scores.map baseScore := by
  induction scores with
  | nil =>
      rfl
  | cons firstScore remainingScores inductionHypothesis =>
      simp [quality_score_greater10, inductionHypothesis]

end ReadWindow
