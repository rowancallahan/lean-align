import Proofs.Answer
import Proofs.Tiers
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

theorem start_le_stop {genome : Genome} {read : Read} (alignment : GenomicAlignment genome read) :
    alignment.placement.start ≤ alignment.placement.stop := by
  have h := alignment.fits
  unfold Placement.reference at h
  split at h <;> simp_all

theorem isProper_iff {genome : Genome} {mate1 mate2 : Read} (pair : PairAlignment genome mate1 mate2)
    (range : Nat × Nat) (dovetailSlack : Nat) :
    pair.IsProper range dovetailSlack ↔
      MapSpec.properPairU dovetailSlack range.1 range.2
        (oldPlacement pair.first.placement) (oldPlacement pair.second.placement) = true := by
  have h1 := start_le_stop pair.first
  have h2 := start_le_stop pair.second
  obtain ⟨lo, hi⟩ := range
  unfold PairAlignment.IsProper
  generalize pair.first.placement = p at *
  generalize pair.second.placement = q at *
  obtain ⟨c1, s1, e1, t1⟩ := p
  obtain ⟨c2, s2, e2, t2⟩ := q
  cases t1 <;> cases t2 <;>
    simp [MapSpec.properPairU, MapSpec.properPair, MapSpec.fwdRev,
      oldPlacement, oldStrand] at * <;> omega

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
  -- an alignment gives a hit at its placement, at every threshold up to the hit's score
  have hit_at : ∀ {read : Read} (alignment : GenomicAlignment genome read),
      ∃ s, alignment.score ≤ s ∧ s ≤ 0 ∧ ∀ T, T ≤ s →
        (oldPlacement alignment.placement, s) ∈ MapSpec.hitsBoth MapSpec.sc0 T (oldGenome genome) read := by
    intro read alignment
    obtain ⟨s, hs, hm⟩ := hit_of_alignment alignment alignment.score (Int.le_refl _)
    refine ⟨s, hs, MapSpec.hitsBoth_nonpos _ _ _ _ hm, fun T hT => ?_⟩
    rw [MapSpec.Fast.mem_hitsBoth_T] at hm ⊢
    exact ⟨hm.1, hm.2.1, hT⟩
  refine ⟨fun _ h => by simp [answerOf] at h, fun pair hp => ?_, by simp [answerOf]⟩
  -- a proper pair gives a proper pair of hits, at all thresholds up to the hits' scores
  obtain ⟨s1, s2, hle, h1n, h2n, hmem⟩ : ∃ s1 s2, pair.score ≤ s1 + s2 ∧ s1 ≤ 0 ∧ s2 ≤ 0 ∧
      ∀ T1 T2, T1 ≤ s1 → T2 ≤ s2 →
        ((oldPlacement pair.first.placement, s1), (oldPlacement pair.second.placement, s2)) ∈
          MapSpec.properPairs insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
            (MapSpec.hitsBoth MapSpec.sc0 T1 (oldGenome genome) mate1)
            (MapSpec.hitsBoth MapSpec.sc0 T2 (oldGenome genome) mate2) := by
    obtain ⟨s1, h1, h1n, hm1⟩ := hit_at pair.first
    obtain ⟨s2, h2, h2n, hm2⟩ := hit_at pair.second
    refine ⟨s1, s2, by unfold PairAlignment.score; omega, h1n, h2n, fun T1 T2 hT1 hT2 => ?_⟩
    rw [MapSpec.mem_properPairs]
    exact ⟨hm1 T1 hT1, hm2 T2 hT2, (isProper_iff pair insertSettings.range insertSettings.dovetailSlack).mp hp⟩
  suffices hb : s1 + s2 ≤ boundOf t by simp only [answerOf]; omega
  have hm := hmem s1 s2 (Int.le_refl _) (Int.le_refl _)
  rw [MapSpec.mem_properPairs] at hm
  obtain ⟨hm1, hm2, -⟩ := hm
  unfold MapSpec.Fast.TierOk at hok
  unfold boundOf
  cases htag : t.tag <;> rw [htag] at hok <;> simp only []
  case t0 => simp at hok
  case t1 =>
    obtain ⟨x, y, hx, hy, hs⟩ := hok
    rw [hx, hy]
    unfold MapSpec.Fast.pairSpecT at hs
    cases h1 : MapSpec.mapSpecBoth MapSpec.sc0 (-(t.c1 : Int)) (oldGenome genome) mate1 <;>
      cases h2 : MapSpec.mapSpecBoth MapSpec.sc0 (-(t.c2 : Int)) (oldGenome genome) mate2 <;>
      rw [h1, h2] at hs <;> simp only [reduceCtorEq] at hs
    rename_i a b
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have := le_of_mapSpecBoth h1 hm1
      have := le_of_mapSpecBoth h2 hm2
      simp only at *; omega
    · cases hs
  case t1g =>
    obtain ⟨-, -, hall⟩ := hok
    obtain ⟨c1, c2⟩ := cap_le (g0 := t.g0) h1n
    obtain ⟨c3, c4⟩ := cap_le (g0 := t.g0) h2n
    obtain ⟨x, y, hx, hy, hs⟩ := hall _ _ c1 c3
    rw [hx, hy]
    exact le_of_pairSpecUT hs (hmem _ _ c2 c4)
  case t1u =>
    obtain ⟨-, hall⟩ := hok
    obtain ⟨c1, c2⟩ := cap_le (g0 := t.g0) h1n
    obtain ⟨c3, c4⟩ := cap_le (g0 := t.g0) h2n
    obtain ⟨x, y, hx, hy, hs⟩ := hall _ _ c1 c3
    rw [hx, hy]
    exact le_of_pairSpecUT hs (hmem _ _ c2 c4)
  case t2b =>
    obtain ⟨x, y, hx, hy, -, hall⟩ := hok
    rw [hx, hy]
    have := hall s1 s2 _ (hmem s1 s2 (Int.le_refl _) (Int.le_refl _))
    rw [pairScoreD_dcost0, pairScoreD_dcost0] at this
    exact this
  case t1gm => omega
  case t1um => omega
  case t2 =>
    replace hok := hok.1
    obtain ⟨f1, f2, hpf⟩ := hok
    have a1 := f1 s1 _ hm1
    have a2 := f2 s2 _ hm2
    simp only at a1 a2
    rcases hp : t.pf with _ | G0
    · simp only []; push_cast; omega
    · simp only []
      obtain ⟨c1, c2⟩ := cap_le (g0 := G0) h1n
      obtain ⟨c3, c4⟩ := cap_le (g0 := G0) h2n
      have := hpf G0 hp _ _ c1 c3 _ (hmem _ _ c2 c4)
      rw [pairScoreD_dcost0] at this
      simp only at this
      push_cast; omega
  case t3 =>
    obtain ⟨f1, f2, hpf⟩ := hok
    have a1 := f1 s1 _ hm1
    have a2 := f2 s2 _ hm2
    simp only at a1 a2
    rcases hp : t.pf with _ | G0
    · simp only []; push_cast; omega
    · simp only []
      obtain ⟨c1, c2⟩ := cap_le (g0 := G0) h1n
      obtain ⟨c3, c4⟩ := cap_le (g0 := G0) h2n
      have := hpf G0 hp _ _ c1 c3 _ (hmem _ _ c2 c4)
      rw [pairScoreD_dcost0] at this
      simp only at this
      push_cast; omega

end Spec.Bridge
