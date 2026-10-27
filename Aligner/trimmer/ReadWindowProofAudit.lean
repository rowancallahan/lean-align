import ReadWindowTrimmer

open ReadWindow


/-
These examples are small, readable checks of the exact tie behavior.
The universal theorems printed below are the actual proof of equivalence.
-/

-- Same start and same score: choose the shorter window `(0, 1)`.
example :
    getBestWindowLinear [11, 10] baseScore = some (0, 1) := by
  native_decide


-- Same score at different starts: choose the leftmost window `(0, 1)`.
example :
    getBestWindowLinear [11, 0, 11] baseScore = some (0, 1) := by
  native_decide


-- An empty score list has no nonempty window.
example :
    getBestWindowLinear [] baseScore = none := by
  native_decide


-- The fused implementation has exactly the same leftmost/shortest behavior.
example :
    getBestWindowFused [11, 10] baseScore = some (0, 1) := by
  native_decide


/-
Running this file asks Lean to report the axioms used by the final
equivalence theorems. In particular, any remaining `sorry` would appear as
`sorryAx` in this output.
-/
#print axioms ReadWindow.getBestWindowIncremental_equals_frozen_get_best_window
#print axioms ReadWindow.getBestWindowLinear_equals_frozen_get_best_window
#print axioms ReadWindow.getBestWindowFused_equals_frozen_get_best_window
#print axioms ReadWindow.getBestWindowFlat_equals_frozen_get_best_window
#print axioms ReadWindow.getBestWindowFoldr_equals_frozen_get_best_window
#print axioms ReadWindow.getBestWindowPacked_equals_frozen_get_best_window
