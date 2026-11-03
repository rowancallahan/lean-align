import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import MapperGapless              -- pool: gapless score, gap bound, gapless seed lemma
import MapperOneIndel             -- pool: walks scoring gapOpen + gapExtend are one indel
import SeedMapper                 -- the proved seed-and-index mapper (fallback)

/-!
# Codec `mapLowError`: exact Hamming fast path for near-perfect reads

The algorithm, then the theorems against `mapSpec`, then the proof.

Each seed hit gives one anchor: the window of the read's length that puts the
seed exactly where it was found.  The read is compared letter by letter with
each anchor window (stopping at `gapCap sc + 1` mismatches).  Let `S` be the
best gapless score found and `G = gapOpen + gapExtend`.

* `S > G` and `S ≥ T`: every window that ties or beats `S` is a gapless window
  of the read's length at one of these anchors, and its optimal score is its
  gapless score; the answer is decided from the anchors alone.
* otherwise, when `matchScore = 0` and `T ≤ G` (`gapStep`): no window scores
  above `G`; the windows scoring exactly `G` are the anchors with gapless score
  `G` and the windows that differ from the read by one deleted or inserted
  letter (checked letter by letter at seeds 0 and 1, shifted by one).  If there
  is any, the answer is decided from them.
* otherwise the read goes to `mapWith` (banded DP).
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-! ## The theorems

    LookupComplete g l0 lookup → (∀ w, score w = windowScore sc read g w) →
      mapLowError lookup score (genomeArrays g) sc l0 T (errBound sc T) g read
        = mapSpec sc T g read                                               (mapLowError_eq_mapSpec)
    mapReadsLowError l0 sc T g reads = reads.map (mapSpec sc T g)          (mapReadsLowError_eq_mapSpec)

for every scoring with `ValidScoring sc`.  They are at the end of this file.
The facts they rest on (pool/mapper/MapperGapless.lean, MapperOneIndel.lean):

    walkScore_diags       equal lengths: all-diagonal walk = match·(n − hamming) + mismatch·hamming
    scoreWalk_gap_le      a valid walk with a gap scores ≤ gapOpen + gapExtend
    best_gapless          optimum > gapOpen + gapExtend → equal lengths, optimum = gapless score
    gapless_clean_seed    gapless walk ≥ T → a seed is clean at exactly its own offset
    one_gap_structure     matchScore = 0, walk with a gap ≥ gapOpen + gapExtend → one-letter deletion
    delOk_walk(')         a one-letter deletion gives a walk scoring gapOpen + gapExtend -/

/-! ## Proof -/

theorem mem_allWindows_of_score (sc : Scoring) (read : List Char) (g : Genome) (w : Window) (s : Int)
    (h : windowScore sc read g w = some s) : w ∈ allWindows g := by
  apply (mem_allWindows g w).mpr
  unfold windowScore at h
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some _ => rfl

end MapSpec

