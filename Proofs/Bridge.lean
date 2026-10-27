import Proofs.Answer
import TierOpt
import Proofs.Hits

/-! # Bridge: the existing router proofs (old spec: windows, hits, thresholds) → the new spec.

`tierPair_sound` (mapper/TierOpt.lean) proves `TierOk` for every routed pair, stated over the old
spec (`MapSpec`: windows, `hitsBoth`, `properPairU`, `pairSpecUT`). This file translates. Each
`sorry` below is one self-contained task; `Proofs/Aligner.lean` proves `alignPairs_correct` from
them, so the composition is already checked by Lean.

Milestones:
* M1 (this file as written): `answerOf` reports only proved bounds (`found := none`,
  `uniqueness := .unknown`). Needs B1–B4, B6.
* M2 (next): report the found pair with its CIGAR and `unique` / `multimapper` (needs a proved
  CIGAR for each reported mate, see notes/NEW_SPEC_ADAPTERS.txt R1, R2). Change `answerOf` and
  extend `answerOf_correct`.

Names from the old code are written in full (`MapSpec.…`, `MapSpec.Fast.…`, `AlignmentSpec.…`)
so they never clash with the new spec's `Spec.…`. -/

namespace Spec.Bridge

/-! ## Translating the old spec's types -/

def oldGenome (genome : Genome) : MapSpec.Genome :=
  genome.map fun chromosome => ⟨chromosome.name, chromosome.seq⟩

def oldStrand : Strand → MapSpec.Strand
  | .forward => .fwd
  | .reverse => .rev

def newStrand : MapSpec.Strand → Strand
  | .fwd => .forward
  | .rev => .reverse

def oldStep : Step → AlignmentSpec.Step
  | .diag => .diag
  | .gapX => .gapX
  | .gapY => .gapY

-- old placements are (window: chromosome, start, length) × strand
def oldPlacement (placement : Placement) : MapSpec.Placement :=
  (⟨placement.chromosome, placement.start, placement.stop - placement.start⟩, oldStrand placement.strand)

def newPlacement (placement : MapSpec.Placement) : Placement :=
  ⟨placement.1.chr, placement.1.start, placement.1.start + placement.1.len, newStrand placement.2⟩

-- `defaultScoring` in the old spec's Scoring type (the old code calls it `sc0`)
abbrev oldDefaultScoring : AlignmentSpec.Scoring := MapSpec.sc0

/-! ## B1. Paths are the old monotone walks, with the same score -/

theorem walk_of_path {query reference : Read} (path : Path query reference) :
    AlignmentSpec.IsMonotoneWalk (path.steps.map oldStep) query reference := by
  sorry

theorem score_eq_walkScore {query reference : Read} (path : Path query reference) :
    path.score defaultScoring = AlignmentSpec.walkScore oldDefaultScoring query reference (path.steps.map oldStep) := by
  sorry

/-! ## B2. Hits are the placements' best alignments -/

-- every alignment at or above `T` is covered by a hit at its placement, scoring at least as much
theorem hit_of_alignment {genome : Genome} {read : Read} (alignment : GenomicAlignment genome read)
    (T : Int) (hT : T ≤ alignment.score) :
    ∃ s, alignment.score ≤ s ∧
      (oldPlacement alignment.placement, s) ∈ MapSpec.hitsBoth oldDefaultScoring T (oldGenome genome) read := by
  obtain ⟨hle, hseq⟩ := (Hits.reference_iff genome alignment.placement alignment.reference).1 alignment.fits
  have hs := score_eq_walkScore alignment.path
  obtain ⟨s, h1, h2⟩ := Hits.hit_of_walk genome read T alignment.placement.strand _ alignment.reference hseq
    _ (walk_of_path alignment.path) (by rw [← hs]; exact hT)
  have e : oldStrand = Hits.oldStrandOf := by funext x; cases x <;> rfl
  exact ⟨s, by rw [GenomicAlignment.score, hs]; exact h1, by simp only [oldPlacement, e]; exact h2⟩

-- a hit's score is reached by an alignment at that placement (needed for M2)
theorem alignment_of_hit {genome : Genome} {read : Read} {T : Int} {hit : MapSpec.Placement × Int}
    (h : hit ∈ MapSpec.hitsBoth oldDefaultScoring T (oldGenome genome) read) :
    ∃ alignment : GenomicAlignment genome read,
      alignment.placement = newPlacement hit.1 ∧ alignment.score = hit.2 := by
  obtain ⟨a, h1, h2⟩ := Hits.alignment_of_hit_aux h
  obtain ⟨⟨w, st⟩, s⟩ := hit
  exact ⟨a, by cases st <;> exact h1, h2⟩

/-! ## B3. Proper pairs are the same -/

theorem isProper_iff {genome : Genome} {mate1 mate2 : Read} (pair : PairAlignment genome mate1 mate2)
    (range : Nat × Nat) (dovetailSlack : Nat) :
    pair.IsProper range dovetailSlack ↔
      MapSpec.properPairU dovetailSlack range.1 range.2
        (oldPlacement pair.first.placement) (oldPlacement pair.second.placement) = true := by
  sorry

/-! ## B4. Bytes -/

theorem encodes_decodeRead (bytes : ByteArray) : MapSpec.Encodes bytes (decodeRead bytes) := by
  sorry

/-! ## The answer from the router's output (M1: bounds only) -/

def tierOf : MapSpec.Fast.Tag → Tier
  | .t1   => .eachMateUnique
  | .t1g  => .quickSearchUnique
  | .t1u  => .deepSearchUnique
  | .t1gm => .quickSearchTie
  | .t1um => .deepSearchTie
  | .t2b  => .bestUnchecked
  | .t2   => .stoppedEarly
  | .t3   => .boundsOnly
  | .t0   => .boundsOnly

-- the best possible pair score each tag proves (0 always holds: every score is ≤ 0)
def boundOf (t : MapSpec.Fast.TierOut) : Int :=
  match t.tag with
  | .t1 | .t1g | .t1u | .t2b =>
      match t.m1.pl, t.m2.pl with
      | some x, some y => x.2 + y.2
      | _, _ => 0
  | .t2 | .t3 =>
      let floors : Int := -((t.m1.cd + t.m2.cd : Nat) : Int)
      match t.pf with
      | some G0 => min floors (-(G0 : Int) - 1)
      | none => floors
  | _ => 0

def answerOf (t : MapSpec.Fast.TierOut) : PairAnswer :=
  { found := none, bestPossibleScore := boundOf t, uniqueness := .unknown, tier := tierOf t.tag }

/-! ## B6. What each tag proves gives a correct answer -/

theorem answerOf_correct (insertSettings : InsertSettings) (genome : Genome) (mate1 mate2 : Read)
    (bytes1 bytes2 : ByteArray) (t : MapSpec.Fast.TierOut)
    (hok : MapSpec.Fast.TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (oldGenome genome) mate1 mate2 (some bytes1) (some bytes2) t) :
    (answerOf t).Correct insertSettings genome mate1 mate2 := by
  sorry

end Spec.Bridge
