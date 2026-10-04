import Init.Data.List.MinMaxOn
def baseScore (score : Int) : Int :=
  score-10

def quality_score_greater10 (scores : List Int) : List Int :=
  match scores with
  | [] =>
      []
  | x :: xs =>
      ( baseScore x ) :: quality_score_greater10 xs


#eval quality_score_greater10 [11, 11, 11, 9, 8, 7, 6]


def get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (scoring_map : List Int → List Int)
    : Option (Nat × Nat) :=

  let n : Nat := scores.length
  let start : Nat := 0

  let window_list :=
    (List.range n).flatMap fun start =>
      (List.range (n - start)).map fun offset =>
        (start, start + offset + 1)

  let get_window
      (indexes : Nat × Nat)
      (scorelist : List Int)
      : List Int :=

    let startindex := indexes.1
    let endindex := indexes.2
    (scorelist.drop startindex).take (endindex - startindex)

  let quality_sums : List Int :=
    List.map
      (fun indexes =>
        (scoring_map (get_window indexes scores)).sum)
      window_list

  let max_window : Option (Nat × Nat) :=
    ((window_list.zip quality_sums).maxOn? fun item => item.2).map fun item =>
      item.1

  max_window


#eval get_best_window
  [11, 11, 11, 0, 0, 0, 0]
  [11, 11, 11, 9, 8, 7, 6]
  quality_score_greater10


-- Give a name to the calculation used to score one window.
--
-- The window is represented by:
--
--   (starting index, exclusive ending index)
--
-- For example, the window (1, 3) selects indices 1 and 2.
def window_score
    (scores : List Int)
    (scoring_map : List Int → List Int)
    (window : Nat × Nat)
    : Int :=

  let startIndex : Nat := window.1
  let endIndex : Nat := window.2
  let selectedScores : List Int :=
    (scores.drop startIndex).take (endIndex - startIndex)

  (scoring_map selectedScores).sum


-- The first theorem prevents the function from being an implementation
-- that always returns `none`.
--
-- It says that whenever `scores` is nonempty, there really is some
-- `bestWindow` that the function returns.
theorem get_best_window_returns_some_when_scores_nonempty
    (nucleotides : List Nat)
    (scores : List Int)
    (scoring_map : List Int → List Int)
    (scoresNonempty : 0 < scores.length)
    :
    ∃ bestWindow : Nat × Nat,
      get_best_window nucleotides scores scoring_map = some bestWindow := by
  apply Option.isSome_iff_exists.mp
  simp [get_best_window]
  exact ⟨0, scoresNonempty, by simpa using Nat.ne_of_gt scoresNonempty⟩


-- The second theorem says that any window returned by the function is
-- actually a valid, nonempty window inside `scores`.
theorem get_best_window_returns_a_valid_window
    (nucleotides : List Nat)
    (scores : List Int)
    (scoring_map : List Int → List Int)
    (bestWindow : Nat × Nat)
    (functionReturnedBestWindow :
      get_best_window nucleotides scores scoring_map = some bestWindow)
    :
    bestWindow.1 < bestWindow.2 ∧
    bestWindow.2 ≤ scores.length := by
  simp [get_best_window] at functionReturnedBestWindow
  obtain ⟨bestScore, maximumWasReturned⟩ := functionReturnedBestWindow
  have bestPairIsInZippedList := List.maxOn?_mem maximumWasReturned
  have bestWindowIsInWindowList := (List.of_mem_zip bestPairIsInZippedList).1
  simp at bestWindowIsInWindowList
  obtain ⟨startIndex, startIsInRange, offset, offsetIsInRange, windowEquation⟩ :=
    bestWindowIsInWindowList
  rw [← windowEquation]
  constructor
  · simpa [Nat.add_assoc] using
      (Nat.lt_add_of_pos_right (Nat.zero_lt_succ offset) :
        startIndex < startIndex + (offset + 1))
  · have endMinusOneIsInside : startIndex + offset < scores.length :=
      Nat.add_lt_of_lt_sub' offsetIsInRange
    exact Nat.add_one_le_of_lt endMinusOneIsInside


-- The third theorem says that the returned window scores at least as highly
-- as every valid candidate window.
theorem get_best_window_returns_a_maximum_score
    (nucleotides : List Nat)
    (scores : List Int)
    (scoring_map : List Int → List Int)
    (bestWindow : Nat × Nat)
    (candidateWindow : Nat × Nat)
    (functionReturnedBestWindow :
      get_best_window nucleotides scores scoring_map = some bestWindow)
    (candidateHasPositiveWidth :
      candidateWindow.1 < candidateWindow.2)
    (candidateEndsInsideScores :
      candidateWindow.2 ≤ scores.length)
    :
    window_score scores scoring_map candidateWindow ≤
    window_score scores scoring_map bestWindow := by
  simp [get_best_window] at functionReturnedBestWindow
  let windows : List (Nat × Nat) :=
    (List.range scores.length).flatMap fun start =>
      (List.range (scores.length - start)).map fun offset =>
        (start, start + offset + 1)
  let score : Nat × Nat → Int := fun window =>
    window_score scores scoring_map window
  change
    ∃ bestScore,
      (windows.zip (List.map score windows)).maxOn? (fun item => item.2) =
        some (bestWindow, bestScore)
    at functionReturnedBestWindow
  change score candidateWindow ≤ score bestWindow
  obtain ⟨bestScore, maximumWasReturned⟩ := functionReturnedBestWindow
  have candidateIsInWindowList : candidateWindow ∈ windows := by
    simp [windows]
    refine ⟨candidateWindow.1, ?_, candidateWindow.2 - candidateWindow.1 - 1, ?_, ?_⟩
    · exact Nat.lt_of_lt_of_le candidateHasPositiveWidth candidateEndsInsideScores
    · omega
    · apply Prod.ext
      · rfl
      · simp
        omega
  have zippedWindowsEquation :
      windows.zip (List.map score windows) =
        List.map (fun window => (window, score window)) windows := by
    induction windows with
    | nil =>
        rfl
    | cons firstWindow remainingWindows inductionHypothesis =>
        simp [inductionHypothesis]
  have candidatePairIsInZippedList :
      (candidateWindow, score candidateWindow) ∈
        windows.zip (List.map score windows) := by
    rw [zippedWindowsEquation]
    exact List.mem_map.mpr ⟨candidateWindow, candidateIsInWindowList, rfl⟩
  have bestPairIsInZippedList := List.maxOn?_mem maximumWasReturned
  have bestScoreEquation : score bestWindow = bestScore := by
    rw [zippedWindowsEquation] at bestPairIsInZippedList
    obtain ⟨originalWindow, originalWindowIsInList, pairEquation⟩ :=
      List.mem_map.mp bestPairIsInZippedList
    have originalWindowEqualsBestWindow : originalWindow = bestWindow :=
      congrArg Prod.fst pairEquation
    have originalScoreEqualsBestScore : score originalWindow = bestScore :=
      congrArg Prod.snd pairEquation
    rw [originalWindowEqualsBestWindow] at originalScoreEqualsBestScore
    exact originalScoreEqualsBestScore
  have selectedPairEquation :=
    List.maxOn_eq_of_maxOn?_eq_some maximumWasReturned
  have candidateScoreIsAtMostMaximum :=
    List.le_apply_maxOn_of_mem
      (f := fun item : (Nat × Nat) × Int => item.2)
      candidatePairIsInZippedList
  rw [selectedPairEquation] at candidateScoreIsAtMostMaximum
  rw [bestScoreEquation]
  exact candidateScoreIsAtMostMaximum
