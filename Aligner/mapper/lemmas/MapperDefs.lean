import MapSpec
import Std.Data.HashMap

/-! Shared definitions for the seed-and-index mapper. -/

namespace MapSpec

open AlignmentSpec

/-- Scoring for which every non-match column costs something. -/
def ValidScoring (sc : Scoring) : Prop :=
  sc.matchScore ≤ 0 ∧ sc.mismatchScore < 0 ∧ sc.gapOpen ≤ 0 ∧ sc.gapExtend < 0

/-- The most non-match columns an alignment scoring at least `T` can have. -/
def errBound (sc : Scoring) (T : Int) : Nat :=
  ((-T) / min (-sc.mismatchScore) (-sc.gapExtend)).toNat

/-- All `(word, place)` pairs of one chromosome. -/
def wordsOf (l0 : Nat) (c : Nat) (seq : List Char) : List (List Char × (Nat × Nat)) :=
  (List.range (seq.length + 1 - l0)).map fun p => ((seq.drop p).take l0, (c, p))

def buildTable (items : List (List Char × (Nat × Nat))) : Std.HashMap (List Char) (List (Nat × Nat)) :=
  items.foldl (fun m (key, place) => m.insert key (place :: m.getD key [])) ∅

end MapSpec
