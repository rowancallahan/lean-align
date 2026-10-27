import ReadWindowTrimmer.Faster

open ReadWindow


/-!
# The contract theorem for the fastest current trimmer

This is intentionally the first declaration in this file so that it is easy
to find and check.

The theorem quantifies over:

* every nucleotide list;
* every integer quality-score list, including the empty list; and
* every per-base scoring function from `Int` to `Int`.

Its conclusion is equality of the complete returned value.  Therefore the
packed implementation returns `none` exactly when the frozen function does,
and otherwise returns exactly the same start and end indexes.  This includes
the frozen function's current leftmost-then-shortest tie behavior.
-/
theorem packed_function_is_identical_to_frozen_contract
    (nucleotides : List Nat)
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowPacked scores perBaseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map perBaseScore) := by
  calc
    -- Step 1: removing the `Option FlatResult` allocation changes no output.
    getBestWindowPacked scores perBaseScore =
        getBestWindowFoldr scores perBaseScore := by
      exact getBestWindowPacked_equals_foldr scores perBaseScore

    -- Step 2: compiled `foldr` and the direct flat recursion agree exactly.
    _ = getBestWindowFlat scores perBaseScore := by
      exact getBestWindowFoldr_equals_flat scores perBaseScore

    -- Step 3: the flat state and the earlier fused state store the same facts.
    _ = getBestWindowFused scores perBaseScore := by
      exact getBestWindowFlat_equals_fused scores perBaseScore

    -- Step 4: the fused result is already proved equal to the frozen contract.
    _ = get_best_window
          nucleotides
          scores
          (fun windowScores => windowScores.map perBaseScore) := by
      exact
        getBestWindowFused_equals_frozen_get_best_window
          nucleotides
          scores
          perBaseScore


/-!
The first command prints the theorem's type and proof term.

The second command prints every axiom used anywhere in the proof chain.  An
unfinished `sorry` would cause `sorryAx` to appear in the second output.
-/
#print packed_function_is_identical_to_frozen_contract
#print axioms packed_function_is_identical_to_frozen_contract
