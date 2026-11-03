import MapSpec                    -- the mapping specification (spec/, draft)
import MapperSeedsAmong           -- pool: clean seed among any chosen seeds
import MapperGapless              -- pool: selectUnique lemmas
import SeedMapper2                -- mapWithK and its theorem
import LowErrorMapper             -- mem_allWindows_of_score

/-!
# Codec `mapEarly`: seed lookups in any order, stopping early

The seeds of `mapWithK` are looked up one at a time, in a caller-chosen order
(any permutation of the seed indices).  After each lookup, let `B` be the best
score among the hits found so far.  A window that ties or beats `B` spoils at
most `seedBound sc B` seeds (default scoring: `P / 4` for penalty `P = −B`),
so once more than `seedBound sc B` seeds have been looked up, every window
that can tie or beat `B` is already a candidate: stop and answer.

General facts used (any candidate list `C`, scorer = `windowScore`):

    selectUnique_cover_all    C has every window scoring ≥ T → answer = mapSpec
    selectUnique_cover_above  T ≤ S, C has every window scoring ≥ S and one
                              window scoring ≥ S → answer = mapSpec
    mem_seedCands_among       a window scoring ≥ S is a candidate of any
                              `seedBound sc S + 1` distinct seeds
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Windows from seed `j` alone (one term of `seedCandidatesK`). -/
def seedCands (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (read : List Char) (k d d2 : Nat) (j : Nat) : List Window :=
  ((lookup (((read.drop (j * (read.length / (k + 1)))).take (read.length / (k + 1))).take l0)).filter
      (keep ((read.drop (j * (read.length / (k + 1)))).take (read.length / (k + 1))))).flatMap
    fun place =>
      (shapes d d2).filterMap fun st =>
        if ((j * (read.length / (k + 1)) : Nat) : Int) + st.1 ≤ place.2 ∧
            0 ≤ (read.length : Int) + st.1 + st.2 then
          some { chr := place.1, start := ((place.2 : Int) - (j * (read.length / (k + 1)) : Nat) - st.1).toNat,
                 len := ((read.length : Int) + st.1 + st.2).toNat }
        else none

/-! ## The theorem

    order ~ List.range (seedBound sc T + 1) →
      mapEarly keep lookup score (seedBound sc) l0 T
        (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read order
      = mapSpec sc T g read                                                (mapEarly_eq_mapSpec)

given `ValidScoring sc`, `LookupComplete g l0 lookup`, `KeepComplete g keep`
and a scorer equal to `windowScore`. -/

/-! ## Proof -/

theorem shapeOk_mono (d d2 D D2 : Nat) (s t : Int) (h : shapeOk d d2 s t) (hd : d ≤ D) (hd2 : d2 ≤ D2) :
    shapeOk D D2 s t := by
  unfold shapeOk at *; omega

end MapSpec

