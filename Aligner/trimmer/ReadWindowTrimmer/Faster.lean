import Init.Data.List.Impl
import ReadWindowTrimmer.Fused

namespace ReadWindow


/-
This structure stores the same mathematical information as `FusedResult`, but
without nested pairs.  The five scalar fields are friendlier to Lean's compiler
and reference-counting runtime.
-/
structure FlatResult where
  prefixLength : Nat
  prefixScore : Int
  bestStart : Nat
  bestEnd : Nat
  bestScore : Int
deriving Repr, DecidableEq


def FlatResult.toFusedResult (result : FlatResult) : FusedResult :=
  { bestPrefix := (result.prefixLength, result.prefixScore)
    bestCandidate :=
      ((result.bestStart, result.bestEnd), result.bestScore) }


@[inline]
def prependFlatResult
    (perBaseScore : Int → Int)
    (startIndex : Nat)
    (firstScore : Int)
    (laterResult : Option FlatResult)
    : Option FlatResult :=
  let firstBaseScore : Int := perBaseScore firstScore
  match laterResult with
  | none =>
      some
        { prefixLength := 1
          prefixScore := firstBaseScore
          bestStart := startIndex
          bestEnd := startIndex + 1
          bestScore := firstBaseScore }
  | some later =>
      if 0 < later.prefixScore then
        let currentLength : Nat := later.prefixLength + 1
        let currentScore : Int := firstBaseScore + later.prefixScore
        if later.bestScore ≤ currentScore then
          some
            { prefixLength := currentLength
              prefixScore := currentScore
              bestStart := startIndex
              bestEnd := startIndex + currentLength
              bestScore := currentScore }
        else
          some
            { prefixLength := currentLength
              prefixScore := currentScore
              bestStart := later.bestStart
              bestEnd := later.bestEnd
              bestScore := later.bestScore }
      else
        if later.bestScore ≤ firstBaseScore then
          some
            { prefixLength := 1
              prefixScore := firstBaseScore
              bestStart := startIndex
              bestEnd := startIndex + 1
              bestScore := firstBaseScore }
        else
          some
            { prefixLength := 1
              prefixScore := firstBaseScore
              bestStart := later.bestStart
              bestEnd := later.bestEnd
              bestScore := later.bestScore }


def fuseFlatFrom
    (perBaseScore : Int → Int)
    : Nat → List Int → Option FlatResult
  | _, [] =>
      none
  | startIndex, firstScore :: laterScores =>
      prependFlatResult
        perBaseScore
        startIndex
        firstScore
        (fuseFlatFrom perBaseScore (startIndex + 1) laterScores)


def getBestWindowFlat
    (scores : List Int)
    (perBaseScore : Int → Int)
    : Option Window :=
  (fuseFlatFrom perBaseScore 0 scores).map fun result =>
    (result.bestStart, result.bestEnd)


theorem fuseFlatFrom_maps_to_fused
    (scores : List Int)
    (perBaseScore : Int → Int)
    (startIndex : Nat)
    :
    (fuseFlatFrom perBaseScore startIndex scores).map
        FlatResult.toFusedResult =
      fuseBestWindowsFrom perBaseScore startIndex scores := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      rw [fuseFlatFrom, fuseBestWindowsFrom]
      cases flatEquation :
          fuseFlatFrom perBaseScore (startIndex + 1) laterScores with
      | none =>
          have fusedEquation :
              fuseBestWindowsFrom
                  perBaseScore
                  (startIndex + 1)
                laterScores = none := by
            symm
            simpa [flatEquation] using inductionHypothesis (startIndex + 1)
          rw [fusedEquation]
          simp [prependFlatResult, FlatResult.toFusedResult,
            extendPrefixSummary]
      | some laterResult =>
          have fusedEquation :
              fuseBestWindowsFrom
                  perBaseScore
                  (startIndex + 1)
                  laterScores =
                some laterResult.toFusedResult := by
            symm
            simpa [flatEquation] using inductionHypothesis (startIndex + 1)
          rw [fusedEquation]
          simp only [prependFlatResult, FlatResult.toFusedResult]
          by_cases prefixIsPositive : 0 < laterResult.prefixScore
          · rw [if_pos prefixIsPositive]
            by_cases currentIsBest :
                laterResult.bestScore ≤
                  perBaseScore firstScore + laterResult.prefixScore
            · rw [if_pos currentIsBest]
              simp only [extendPrefixSummary, prefixIsPositive, if_pos]
              rw [maxOn_eq_left currentIsBest]
              rfl
            · rw [if_neg currentIsBest]
              simp only [extendPrefixSummary, prefixIsPositive, if_pos]
              rw [maxOn_eq_right currentIsBest]
              rfl
          · rw [if_neg prefixIsPositive]
            by_cases currentIsBest :
                laterResult.bestScore ≤ perBaseScore firstScore
            · rw [if_pos currentIsBest]
              simp only [extendPrefixSummary, prefixIsPositive]
              rw [maxOn_eq_left currentIsBest]
              rfl
            · rw [if_neg currentIsBest]
              simp only [extendPrefixSummary, prefixIsPositive]
              rw [maxOn_eq_right currentIsBest]
              rfl


theorem getBestWindowFlat_equals_fused
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowFlat scores perBaseScore =
      getBestWindowFused scores perBaseScore := by
  rw [getBestWindowFlat, getBestWindowFused]
  rw [← fuseFlatFrom_maps_to_fused scores perBaseScore 0]
  cases fuseFlatFrom perBaseScore 0 scores <;> rfl


theorem getBestWindowFlat_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowFlat scores perBaseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map perBaseScore) := by
  rw [getBestWindowFlat_equals_fused]
  exact getBestWindowFused_equals_frozen_get_best_window
    nucleotides
    scores
    perBaseScore


/-
Lean's core library replaces `List.foldr` in compiled code with a tail-recursive
array-backed implementation through a proved `@[csimp]` theorem.  The following
state lets us use that implementation without changing the logical definition
we prove about.
-/
structure FlatFoldState where
  nextStart : Nat
  result : Option FlatResult
deriving Repr, DecidableEq


@[inline]
def flatFoldStep
    (perBaseScore : Int → Int)
    (score : Int)
    (state : FlatFoldState)
    : FlatFoldState :=
  let currentStart : Nat := state.nextStart - 1
  { nextStart := currentStart
    result :=
      prependFlatResult
        perBaseScore
        currentStart
        score
        state.result }


def fuseFoldrFrom
    (scores : List Int)
    (perBaseScore : Int → Int)
    (startIndex : Nat)
    : Option FlatResult :=
  let initialState : FlatFoldState :=
    { nextStart := startIndex + scores.length
      result := none }
  let finalState : FlatFoldState :=
    scores.foldr (flatFoldStep perBaseScore) initialState
  finalState.result


def getBestWindowFoldr
    (scores : List Int)
    (perBaseScore : Int → Int)
    : Option Window :=
  (fuseFoldrFrom scores perBaseScore 0).map fun result =>
    (result.bestStart, result.bestEnd)


theorem foldr_flat_state_equals_recursive
    (scores : List Int)
    (perBaseScore : Int → Int)
    (startIndex : Nat)
    :
    scores.foldr
        (flatFoldStep perBaseScore)
        { nextStart := startIndex + scores.length
          result := none } =
      { nextStart := startIndex
        result := fuseFlatFrom perBaseScore startIndex scores } := by
  induction scores generalizing startIndex with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [List.length_cons, List.foldr_cons]
      have startingIndexEquality :
          startIndex + (laterScores.length + 1) =
            (startIndex + 1) + laterScores.length := by
        omega
      rw [startingIndexEquality]
      rw [inductionHypothesis (startIndex + 1)]
      simp [flatFoldStep, fuseFlatFrom]


theorem fuseFoldrFrom_equals_flat
    (scores : List Int)
    (perBaseScore : Int → Int)
    (startIndex : Nat)
    :
    fuseFoldrFrom scores perBaseScore startIndex =
      fuseFlatFrom perBaseScore startIndex scores := by
  rw [fuseFoldrFrom]
  rw [foldr_flat_state_equals_recursive]


theorem getBestWindowFoldr_equals_flat
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowFoldr scores perBaseScore =
      getBestWindowFlat scores perBaseScore := by
  rw [getBestWindowFoldr, getBestWindowFlat, fuseFoldrFrom_equals_flat]


theorem getBestWindowFoldr_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowFoldr scores perBaseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map perBaseScore) := by
  rw [getBestWindowFoldr_equals_flat]
  exact getBestWindowFlat_equals_frozen_get_best_window
    nucleotides
    scores
    perBaseScore


/-
This packed accumulator removes the `Option FlatResult` allocation from each
fold step.  `hasResult = false` represents the empty suffix.  Once a score has
been processed, all five scalar result fields are meaningful.
-/
structure PackedFoldState where
  nextStart : Nat
  hasResult : Bool
  prefixLength : Nat
  prefixScore : Int
  bestStart : Nat
  bestEnd : Nat
  bestScore : Int
deriving Repr, DecidableEq


def PackedFoldState.result (state : PackedFoldState) : Option FlatResult :=
  match state.hasResult with
  | false =>
      none
  | true =>
      some
        { prefixLength := state.prefixLength
          prefixScore := state.prefixScore
          bestStart := state.bestStart
          bestEnd := state.bestEnd
          bestScore := state.bestScore }


def PackedFoldState.toFlatFoldState
    (state : PackedFoldState)
    : FlatFoldState :=
  { nextStart := state.nextStart
    result := state.result }


@[inline]
def packedFoldStep
    (perBaseScore : Int → Int)
    (score : Int)
    (state : PackedFoldState)
    : PackedFoldState :=
  let currentStart : Nat := state.nextStart - 1
  let firstBaseScore : Int := perBaseScore score
  match state.hasResult with
  | false =>
      { nextStart := currentStart
        hasResult := true
        prefixLength := 1
        prefixScore := firstBaseScore
        bestStart := currentStart
        bestEnd := currentStart + 1
        bestScore := firstBaseScore }
  | true =>
      if 0 < state.prefixScore then
        let currentLength : Nat := state.prefixLength + 1
        let currentScore : Int := firstBaseScore + state.prefixScore
        if state.bestScore ≤ currentScore then
          { nextStart := currentStart
            hasResult := true
            prefixLength := currentLength
            prefixScore := currentScore
            bestStart := currentStart
            bestEnd := currentStart + currentLength
            bestScore := currentScore }
        else
          { nextStart := currentStart
            hasResult := true
            prefixLength := currentLength
            prefixScore := currentScore
            bestStart := state.bestStart
            bestEnd := state.bestEnd
            bestScore := state.bestScore }
      else
        if state.bestScore ≤ firstBaseScore then
          { nextStart := currentStart
            hasResult := true
            prefixLength := 1
            prefixScore := firstBaseScore
            bestStart := currentStart
            bestEnd := currentStart + 1
            bestScore := firstBaseScore }
        else
          { nextStart := currentStart
            hasResult := true
            prefixLength := 1
            prefixScore := firstBaseScore
            bestStart := state.bestStart
            bestEnd := state.bestEnd
            bestScore := state.bestScore }


def initialPackedFoldState (nextStart : Nat) : PackedFoldState :=
  { nextStart := nextStart
    hasResult := false
    prefixLength := 0
    prefixScore := 0
    bestStart := 0
    bestEnd := 0
    bestScore := 0 }


def getBestWindowPacked
    (scores : List Int)
    (perBaseScore : Int → Int)
    : Option Window :=
  let initialState : PackedFoldState :=
    initialPackedFoldState scores.length
  let finalState : PackedFoldState :=
    scores.foldr (packedFoldStep perBaseScore) initialState
  finalState.result.map fun result =>
    (result.bestStart, result.bestEnd)


theorem packedFoldStep_conversion
    (perBaseScore : Int → Int)
    (score : Int)
    (state : PackedFoldState)
    :
    (packedFoldStep perBaseScore score state).toFlatFoldState =
      flatFoldStep perBaseScore score state.toFlatFoldState := by
  cases state with
  | mk nextStart hasResult prefixLength prefixScore
      bestStart bestEnd bestScore =>
      cases hasResult <;>
        simp only [packedFoldStep, PackedFoldState.toFlatFoldState,
          PackedFoldState.result, flatFoldStep, prependFlatResult]
      all_goals
        split <;> rename_i prefixComparison
        all_goals
          split <;> rename_i bestComparison <;> rfl


theorem packed_foldr_conversion
    (scores : List Int)
    (perBaseScore : Int → Int)
    (initialState : PackedFoldState)
    :
    (scores.foldr
        (packedFoldStep perBaseScore)
        initialState).toFlatFoldState =
      scores.foldr
        (flatFoldStep perBaseScore)
        initialState.toFlatFoldState := by
  induction scores with
  | nil =>
      rfl
  | cons firstScore laterScores inductionHypothesis =>
      simp only [List.foldr_cons]
      rw [packedFoldStep_conversion]
      rw [inductionHypothesis]


theorem getBestWindowPacked_equals_foldr
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowPacked scores perBaseScore =
      getBestWindowFoldr scores perBaseScore := by
  rw [getBestWindowPacked, getBestWindowFoldr, fuseFoldrFrom]
  have conversion :=
    packed_foldr_conversion
      scores
      perBaseScore
      (initialPackedFoldState scores.length)
  have resultEquality := congrArg FlatFoldState.result conversion
  simpa [PackedFoldState.toFlatFoldState, initialPackedFoldState,
    PackedFoldState.result] using
      congrArg
        (fun optionalResult =>
          optionalResult.map fun result =>
            (result.bestStart, result.bestEnd))
        resultEquality


theorem getBestWindowPacked_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowPacked scores perBaseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map perBaseScore) := by
  rw [getBestWindowPacked_equals_foldr]
  exact getBestWindowFoldr_equals_frozen_get_best_window
    nucleotides
    scores
    perBaseScore

end ReadWindow
