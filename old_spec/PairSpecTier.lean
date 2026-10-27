import PairSpec

/-!
# Tier-1 mapping: the cap from the read length (DRAFT, for Rowan to review/rewrite; not frozen)

Built on `MapSpec` / `PairSpec` without changing them.

The tier-1 cap of a read is the strongest one its length supports with the 25-letter
seed index: a window within penalty `P` spoils at most `sbound P` disjoint seeds, so
`25 · (sbound P + 1)` letters are needed (`sbound 16 = 5`, `sbound 12 = 3`):

* `n ≥ 150`: `T = −16`;
* `100 ≤ n < 150`: `T = −12`;
* `n < 100`: not mapped ("too short"; TODO: shorter seeds, e.g. the batched genome
  scan of `codecs/FastGenBatch.lean`, as a tier-2 option).  Reads shorter than 30
  letters are outside the mapper's domain in every tier (Rowan, 2026-10-05).

A read maps as `mapSpecBoth` at its own cap.  A pair is reported when both mates map
(each at its own cap) and form a proper pair.
-/

namespace MapSpec

open AlignmentSpec

/-- The tier-1 penalty cap of a read of `n` letters; `none` = too short. -/
def capOf (n : Nat) : Option Nat :=
  if 150 ≤ n then some 16 else if 100 ≤ n then some 12 else none

/-- Where a read maps in tier 1 (both strands, its own cap); `none` = unmapped or too short. -/
def mapSpecTier1 (sc : Scoring) (g : Genome) (read : List Char) : Option (Placement × Int) :=
  match capOf read.length with
  | some P => mapSpecBoth sc (-(P : Int)) g read
  | none => none

/-- Where a pair maps in tier 1 when only proper pairs are kept; `none` = not reported. -/
def pairSpecTier1 (sc : Scoring) (lo hi : Nat) (g : Genome) (mate1 mate2 : List Char) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapSpecTier1 sc g mate1, mapSpecTier1 sc g mate2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

end MapSpec
