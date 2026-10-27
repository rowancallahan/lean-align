import Proofs.Answer
import TierOpt

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

def oldScoring (scoring : Scoring) : AlignmentSpec.Scoring :=
  ⟨scoring.matchScore, scoring.mismatchScore, scoring.gapOpen, scoring.gapExtend⟩

theorem scoreWalk_eq (scoring : Scoring) :
    ∀ (steps : List Step) (query reference : Read) (previous : Option Step),
      scoreWalk scoring steps query reference previous =
        AlignmentSpec.scoreWalk (oldScoring scoring) (steps.map oldStep) query reference
          (previous.map oldStep) := by
  intro steps
  induction steps with
  | nil => intros; simp [scoreWalk, AlignmentSpec.scoreWalk]
  | cons step rest ih =>
    intro query reference previous
    cases step <;> cases query <;> cases reference <;>
      rcases previous with _ | (_ | _ | _) <;>
      simp_all [scoreWalk, AlignmentSpec.scoreWalk, oldStep, oldScoring, Option.map]

theorem sum_xConsumed (steps : List Step) :
    ((steps.map oldStep).map AlignmentSpec.xConsumed).sum = steps.count .diag + steps.count .gapY := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp_all [oldStep, AlignmentSpec.xConsumed] <;> omega

theorem sum_yConsumed (steps : List Step) :
    ((steps.map oldStep).map AlignmentSpec.yConsumed).sum = steps.count .diag + steps.count .gapX := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp_all [oldStep, AlignmentSpec.yConsumed] <;> omega

theorem walk_of_path {query reference : Read} (path : Path query reference) :
    AlignmentSpec.IsMonotoneWalk (path.steps.map oldStep) query reference :=
  ⟨(sum_xConsumed path.steps).trans path.usesQuery, (sum_yConsumed path.steps).trans path.usesReference⟩

theorem score_eq_walkScore {query reference : Read} (path : Path query reference) :
    path.score defaultScoring = AlignmentSpec.walkScore oldDefaultScoring query reference (path.steps.map oldStep) := by
  unfold Path.score AlignmentSpec.walkScore
  rw [scoreWalk_eq]
  rfl

/-! ## B2. Hits are the placements' best alignments -/

-- every alignment at or above `T` is covered by a hit at its placement, scoring at least as much
theorem hit_of_alignment {genome : Genome} {read : Read} (alignment : GenomicAlignment genome read)
    (T : Int) (hT : T ≤ alignment.score) :
    ∃ s, alignment.score ≤ s ∧
      (oldPlacement alignment.placement, s) ∈ MapSpec.hitsBoth oldDefaultScoring T (oldGenome genome) read := by
  sorry

-- a hit's score is reached by an alignment at that placement (needed for M2)
theorem alignment_of_hit {genome : Genome} {read : Read} {T : Int} {hit : MapSpec.Placement × Int}
    (h : hit ∈ MapSpec.hitsBoth oldDefaultScoring T (oldGenome genome) read) :
    ∃ alignment : GenomicAlignment genome read,
      alignment.placement = newPlacement hit.1 ∧ alignment.score = hit.2 := by
  sorry

/-! ## B3. Proper pairs are the same -/

theorem isProper_iff {genome : Genome} {mate1 mate2 : Read} (pair : PairAlignment genome mate1 mate2)
    (range : Nat × Nat) (dovetailSlack : Nat) :
    pair.IsProper range dovetailSlack ↔
      MapSpec.properPairU dovetailSlack range.1 range.2
        (oldPlacement pair.first.placement) (oldPlacement pair.second.placement) = true := by
  sorry

/-! ## B4. Bytes -/

theorem byteArray_toList_loop (bs : ByteArray) :
    ∀ n i (r : List UInt8), bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    rw [ByteArray.toList.loop, if_neg (by omega)]
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_sub_eq_zero h
    rw [List.drop_eq_nil_of_le this]; simp
  | succ n ih =>
    intro i r h
    have hi' : i < bs.size := by omega
    rw [ByteArray.toList.loop, if_pos hi', ih (i+1) _ (by omega)]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi'
    rw [List.drop_eq_getElem_cons hi]
    have : bs.get! i = bs.data[i] := by
      rw [ByteArray.get!]; exact getElem!_pos bs.data i hi'
    rw [this]
    simp

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop bs _ 0 [] rfl]; simp

theorem toNat_ofNat_lt (n : Nat) (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  rw [Char.ofNat, dif_pos hv]
  simp [Char.toNat, Char.ofNatAux]

theorem encodes_decodeRead (bytes : ByteArray) : MapSpec.Encodes bytes (decodeRead bytes) := by
  have hlen : (decodeRead bytes).length = bytes.size := by
    unfold decodeRead
    rw [List.length_map, byteArray_toList, Array.length_toList]; rfl
  refine ⟨hlen.symm, fun i h => ?_⟩
  have hi : i < bytes.size := hlen ▸ h
  have hget : bytes.get! i = bytes[i] := by
    rw [ByteArray.get!]; exact getElem!_pos bytes.data i hi
  have hc : (decodeRead bytes)[i] = Char.ofNat bytes[i].toNat := by
    unfold decodeRead
    simp only [List.getElem_map, byteArray_toList, Array.getElem_toList]; rfl
  rw [hget, hc, toNat_ofNat_lt _ bytes[i].toNat_lt]

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
