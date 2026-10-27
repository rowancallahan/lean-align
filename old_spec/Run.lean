import LeanAlign.Run

/-!
# What is proved about the computation

`alignPair` is the proved kernel `wfaAlignU3`.  For every pair of sequences:
a result is always returned, its score is the optimum of the frozen
specification `getBestAlignment`, and its CIGAR is a valid alignment of the
two sequences with exactly that score.

Check with `lake env lean spec/Run.lean`.
-/

namespace LeanAlign

open AlignmentSpec

theorem alignPair_isSome (sc : Scoring) (a b : Array Char) : (alignPair sc a b).isSome :=
  wfaAlignU3_isSome sc a b

theorem alignPair_score (sc : Scoring) (a b : Array Char) :
    (match alignPair sc a b with
     | some result => some result.2
     | none => none) =
    (match getBestAlignment sc a.toList b.toList with
     | some result => some result.2
     | none => none) :=
  wfaAlignU3_score sc a b

theorem alignPair_sound (sc : Scoring) (a b : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : alignPair sc a b = some (c, s)) :
    IsMonotoneWalk (expandCigar c) a.toList b.toList ∧
    walkScore sc a.toList b.toList (expandCigar c) = s :=
  wfaAlignU3_sound sc a b c s h

/-- `alignLines` never fails, and gives one line per pair, each the text of
that pair's kernel result. -/
theorem alignLines_eq (sc : Scoring) (pairs : List (Array Char × Array Char)) :
    ∃ lines, alignLines sc pairs = .ok lines ∧
      lines.map some = pairs.map (fun p => (alignPair sc p.1 p.2).map resultLine) := by
  induction pairs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨ls, hls, hmap⟩ := ih
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (alignPair_isSome sc a b)
    refine ⟨resultLine r :: ls, ?_, ?_⟩
    · simp only [alignLines, hr, hls]
    · simp only [List.map_cons, hr, Option.map_some, hmap]

#print axioms alignPair_isSome
#print axioms alignPair_score
#print axioms alignPair_sound
#print axioms alignLines_eq

end LeanAlign
