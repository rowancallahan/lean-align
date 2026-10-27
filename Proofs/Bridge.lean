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

-- an alignment gives a hit at its placement, at every threshold up to the hit's score
theorem hit_at {genome : Genome} {read : Read} (alignment : GenomicAlignment genome read) :
    ∃ s, alignment.score ≤ s ∧ s ≤ 0 ∧ ∀ T, T ≤ s →
      (oldPlacement alignment.placement, s) ∈ MapSpec.hitsBoth MapSpec.sc0 T (oldGenome genome) read := by
  obtain ⟨s, hs, hm⟩ := hit_of_alignment alignment alignment.score (Int.le_refl _)
  refine ⟨s, hs, MapSpec.hitsBoth_nonpos _ _ _ _ hm, fun T hT => ?_⟩
  rw [MapSpec.Fast.mem_hitsBoth_T] at hm ⊢
  exact ⟨hm.1, hm.2.1, hT⟩

-- a proper pair gives a proper pair of hits, at all thresholds up to the hits' scores
theorem hits_of_proper (insertSettings : InsertSettings) {genome : Genome} {mate1 mate2 : Read}
    (pair : PairAlignment genome mate1 mate2)
    (hp : pair.IsProper insertSettings.range insertSettings.dovetailSlack) :
    ∃ s1 s2, pair.score ≤ s1 + s2 ∧ s1 ≤ 0 ∧ s2 ≤ 0 ∧ ∀ T1 T2, T1 ≤ s1 → T2 ≤ s2 →
      ((oldPlacement pair.first.placement, s1), (oldPlacement pair.second.placement, s2)) ∈
        MapSpec.properPairs insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
          (MapSpec.hitsBoth MapSpec.sc0 T1 (oldGenome genome) mate1)
          (MapSpec.hitsBoth MapSpec.sc0 T2 (oldGenome genome) mate2) := by
  obtain ⟨s1, h1, h1n, hm1⟩ := hit_at pair.first
  obtain ⟨s2, h2, h2n, hm2⟩ := hit_at pair.second
  refine ⟨s1, s2, by unfold PairAlignment.score; omega, h1n, h2n, fun T1 T2 hT1 hT2 => ?_⟩
  rw [MapSpec.mem_properPairs]
  exact ⟨hm1 T1 hT1, hm2 T2 hT2, (isProper_iff pair insertSettings.range insertSettings.dovetailSlack).mp hp⟩

theorem pairScoreD_dcost0 (w : MapSpec.PairHit) : MapSpec.pairScoreD MapSpec.dcost0 w = w.1.2 + w.2.2 := by
  simp [MapSpec.pairScoreD, MapSpec.dcost0]

-- a cap at or below both `g0` and the score `s` (scores are ≤ 0)
theorem cap_le {g0 : Nat} {s : Int} (hs : s ≤ 0) :
    g0 ≤ max g0 (-s).toNat ∧ -((max g0 (-s).toNat : Nat) : Int) ≤ s := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  have h := Nat.le_max_right g0 (-s).toNat
  have e : (((-s).toNat : Nat) : Int) = -s := Int.toNat_of_nonneg (by omega)
  have : (((-s).toNat : Nat) : Int) ≤ ((max g0 (-s).toNat : Nat) : Int) := by exact_mod_cast h
  omega

-- the unique best pair at caps that include `w` scores at least `w`
theorem le_of_pairSpecUT {usl lo hi : Nat} {T1 T2 : Int} {g : MapSpec.Genome} {m1 m2 : List Char}
    {x y : MapSpec.Placement × Int} (h : MapSpec.pairSpecUT MapSpec.sc0 MapSpec.dcost0 usl lo hi T1 T2 g m1 m2 = some (x, y))
    {w : MapSpec.PairHit} (hw : w ∈ MapSpec.properPairs usl lo hi (MapSpec.hitsBoth MapSpec.sc0 T1 g m1)
      (MapSpec.hitsBoth MapSpec.sc0 T2 g m2)) :
    w.1.2 + w.2.2 ≤ x.2 + y.2 := by
  unfold MapSpec.pairSpecUT at h
  rw [MapSpec.bestPairD_iff _ _ _ _ _ _ (MapSpec.hitsBoth_scoreFun _ _ _ _)
    (MapSpec.hitsBoth_scoreFun _ _ _ _)] at h
  obtain ⟨hxy, hall⟩ := h
  rcases hall w hw with hlt | ⟨e1, e2⟩
  · rw [pairScoreD_dcost0, pairScoreD_dcost0] at hlt; simp only at hlt; omega
  · rw [MapSpec.mem_properPairs] at hw hxy
    have := MapSpec.hitsBoth_scoreFun _ _ _ _ _ hw.1 _ hxy.1 e1
    have := MapSpec.hitsBoth_scoreFun _ _ _ _ _ hw.2.1 _ hxy.2.1 e2
    simp only at *; omega

-- a mate's unique best (at any cap) is its best hit at every threshold
theorem le_of_mapSpecBoth {T0 T : Int} {g : MapSpec.Genome} {m : List Char} {x p : MapSpec.Placement × Int}
    (h : MapSpec.mapSpecBoth MapSpec.sc0 T0 g m = some x) (hp : p ∈ MapSpec.hitsBoth MapSpec.sc0 T g m) :
    p.2 ≤ x.2 := by
  have hf := MapSpec.Fast.mateFloor_best h T p hp
  have hx := MapSpec.hitsBoth_nonpos _ _ _ _ (MapSpec.Fast.mapSpecBoth_mem h)
  have e : (((-x.2).toNat : Nat) : Int) = -x.2 := Int.toNat_of_nonneg (by omega)
  omega

theorem answerOf_correct (insertSettings : InsertSettings) (genome : Genome) (mate1 mate2 : Read)
    (bytes1 bytes2 : ByteArray) (t : MapSpec.Fast.TierOut)
    (hok : MapSpec.Fast.TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (oldGenome genome) mate1 mate2 (some bytes1) (some bytes2) t) :
    (answerOf t).Correct insertSettings genome mate1 mate2 := by
  refine ⟨fun _ h => by simp [answerOf] at h, fun pair hp => ?_, by simp [answerOf]⟩
  obtain ⟨s1, s2, hle, h1n, h2n, hmem⟩ := hits_of_proper insertSettings pair hp
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
