import Proofs.Answer
import TierOpt

/-! # Helpers for B2 (hits ↔ alignments), independent of `Proofs/Bridge.lean`.
Old Spec names are written in full; `Proofs.Bridge` only unfolds these. -/

namespace Spec.Hits

def newStepOf : AlignmentSpec.Step → Step
  | .diag => .diag
  | .gapX => .gapX
  | .gapY => .gapY

/-- the old `oldStep` of `Proofs/Bridge.lean`, restated here -/
def oldStepOf : Step → AlignmentSpec.Step
  | .diag => .diag
  | .gapX => .gapX
  | .gapY => .gapY

/-! ## Old walk → new path -/

theorem consumed (ws : List AlignmentSpec.Step) :
    (ws.map AlignmentSpec.xConsumed).sum = (ws.map newStepOf).count .diag + (ws.map newStepOf).count .gapY ∧
    (ws.map AlignmentSpec.yConsumed).sum = (ws.map newStepOf).count .diag + (ws.map newStepOf).count .gapX := by
  induction ws with
  | nil => simp
  | cons s ws ih =>
    cases s <;> simp [newStepOf, AlignmentSpec.xConsumed, AlignmentSpec.yConsumed, List.count_cons] <;> omega

def pathOfWalk {xs ys : Read} {ws : List AlignmentSpec.Step}
    (h : AlignmentSpec.IsMonotoneWalk ws xs ys) : Path xs ys :=
  ⟨ws.map newStepOf, by have := (consumed ws).1; have := h.1; omega,
    by have := (consumed ws).2; have := h.2; omega⟩

theorem scoreWalk_map (ws : List AlignmentSpec.Step) (xs ys : Read) (prev : Option AlignmentSpec.Step) :
    scoreWalk defaultScoring (ws.map newStepOf) xs ys (prev.map newStepOf) =
      AlignmentSpec.scoreWalk MapSpec.sc0 ws xs ys prev := by
  have h1 : defaultScoring.matchScore = MapSpec.sc0.matchScore := rfl
  have h2 : defaultScoring.mismatchScore = MapSpec.sc0.mismatchScore := rfl
  have h3 : defaultScoring.gapOpen = MapSpec.sc0.gapOpen := rfl
  have h4 : defaultScoring.gapExtend = MapSpec.sc0.gapExtend := rfl
  induction ws generalizing xs ys prev with
  | nil => simp [scoreWalk, AlignmentSpec.scoreWalk]
  | cons s ws ih =>
    have ihd : ∀ xs ys, scoreWalk defaultScoring (ws.map newStepOf) xs ys (some .diag) =
        AlignmentSpec.scoreWalk MapSpec.sc0 ws xs ys (some .diag) := fun xs ys => ih xs ys (some .diag)
    have ihx : ∀ xs ys, scoreWalk defaultScoring (ws.map newStepOf) xs ys (some .gapX) =
        AlignmentSpec.scoreWalk MapSpec.sc0 ws xs ys (some .gapX) := fun xs ys => ih xs ys (some .gapX)
    have ihy : ∀ xs ys, scoreWalk defaultScoring (ws.map newStepOf) xs ys (some .gapY) =
        AlignmentSpec.scoreWalk MapSpec.sc0 ws xs ys (some .gapY) := fun xs ys => ih xs ys (some .gapY)
    cases s <;> cases xs <;> cases ys <;> rcases prev with _ | _ | _ | _ <;>
      simp [scoreWalk, AlignmentSpec.scoreWalk, newStepOf, ihd, ihx, ihy, h1, h2, h3, h4]

theorem score_pathOfWalk {xs ys : Read} {ws : List AlignmentSpec.Step}
    (h : AlignmentSpec.IsMonotoneWalk ws xs ys) :
    (pathOfWalk h).score defaultScoring = AlignmentSpec.walkScore MapSpec.sc0 xs ys ws := by
  have := scoreWalk_map ws xs ys none
  exact this

/-! ## Windows -/

theorem complement_eq : Spec.complement = MapSpec.complement := by
  funext c; unfold Spec.complement MapSpec.complement; split <;> (split <;> simp_all)

theorem orient_eq (strand : Strand) (read : Read) :
    strand.orient read = match strand with | .forward => read | .reverse => MapSpec.revComp read := by
  cases strand <;> simp [Strand.orient, reverseComplement, MapSpec.revComp, complement_eq]

def og (genome : Genome) : MapSpec.Genome := genome.map fun c => ⟨c.name, c.seq⟩

theorem reference_iff (genome : Genome) (p : Placement) (ref : Read) :
    p.reference genome = some ref ↔
      p.start ≤ p.stop ∧
        MapSpec.windowSeq (og genome) ⟨p.chromosome, p.start, p.stop - p.start⟩ = some ref := by
  unfold Placement.reference MapSpec.windowSeq og
  simp only [List.getElem?_map]
  cases genome[p.chromosome]? with
  | none => simp
  | some c =>
    simp only [Option.map_some]
    by_cases h : p.start ≤ p.stop ∧ p.stop ≤ c.seq.length
    · have : p.start + (p.stop - p.start) ≤ c.seq.length := by omega
      simp [h, this]
    · by_cases h2 : p.start ≤ p.stop
      · have : ¬ p.start + (p.stop - p.start) ≤ c.seq.length := by omega
        simp [h, this]
      · simp [h2]

theorem mem_hitsOf {score : MapSpec.Window → Option Int} {T : Int} {ws : List MapSpec.Window}
    {w : MapSpec.Window} {s : Int} :
    (w, s) ∈ MapSpec.hitsOf score T ws ↔ w ∈ ws ∧ score w = some s ∧ T ≤ s := by
  simp only [MapSpec.hitsOf, List.mem_filterMap]
  constructor
  · rintro ⟨w', hw', h⟩
    cases hs : score w' with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs] at h
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hw', hs, by assumption⟩
      · simp at h
  · rintro ⟨hw, hs, hT⟩
    exact ⟨w, hw, by simp [hs, hT]⟩

theorem mem_allWindows (g : MapSpec.Genome) (w : MapSpec.Window) (c : MapSpec.Chromosome)
    (hc : g[w.chr]? = some c) (h : w.start + w.len ≤ c.seq.length) : w ∈ MapSpec.allWindows g := by
  have hl : w.chr < g.length := (List.getElem?_eq_some_iff.mp hc).1
  simp [MapSpec.allWindows, List.mem_flatMap, List.mem_range, hc]
  refine ⟨w.chr, hl, w.start, ?_, w.len, ?_, rfl⟩ <;> simp [hc] <;> omega

theorem windowSeq_some {g : MapSpec.Genome} {w : MapSpec.Window} {ys : List Char}
    (h : MapSpec.windowSeq g w = some ys) :
    ∃ c, g[w.chr]? = some c ∧ w.start + w.len ≤ c.seq.length := by
  unfold MapSpec.windowSeq at h
  cases hc : g[w.chr]? with
  | none => simp [hc] at h
  | some c => simp only [hc] at h; split at h <;> simp_all

theorem windowScore_eq_some {sc : AlignmentSpec.Scoring} {read : List Char} {g : MapSpec.Genome}
    {w : MapSpec.Window} {s : Int} :
    MapSpec.windowScore sc read g w = some s ↔
      ∃ ys p, MapSpec.windowSeq g w = some ys ∧ AlignmentSpec.getBestAlignment sc read ys = some (p, s) := by
  unfold MapSpec.windowScore
  cases hw : MapSpec.windowSeq g w with
  | none => simp
  | some ys =>
    simp only
    cases hb : AlignmentSpec.getBestAlignment sc read ys with
    | none => simp [hb]
    | some b => obtain ⟨p, q⟩ := b; simp [hb]

end Spec.Hits
