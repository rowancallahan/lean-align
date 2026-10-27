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
    cases s <;> simp [newStepOf, AlignmentSpec.xConsumed, AlignmentSpec.yConsumed] <;> omega

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

/-! ## Hits -/

def oldStrandOf : Strand → MapSpec.Strand
  | .forward => .fwd
  | .reverse => .rev

theorem reverseComplement_eq (read : Read) : reverseComplement read = MapSpec.revComp read := by
  simp [reverseComplement, MapSpec.revComp, complement_eq]

theorem mem_hitsBoth {sc : AlignmentSpec.Scoring} {T : Int} {g : MapSpec.Genome} {read : Read}
    {pl : MapSpec.Placement} {s : Int} :
    (pl, s) ∈ MapSpec.hitsBoth sc T g read ↔
      ∃ strand : Strand, pl.2 = oldStrandOf strand ∧
        (pl.1, s) ∈ MapSpec.hitsOf (MapSpec.windowScore sc (strand.orient read) g) T (MapSpec.allWindows g) := by
  obtain ⟨w, st⟩ := pl
  unfold MapSpec.hitsBoth
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨w', s'⟩, h, ⟨rfl, rfl⟩, rfl⟩ | ⟨⟨w', s'⟩, h, ⟨rfl, rfl⟩, rfl⟩)
    · exact ⟨.forward, rfl, h⟩
    · exact ⟨.reverse, rfl, by simpa [Strand.orient, reverseComplement_eq] using h⟩
  · rintro ⟨strand, hst, h⟩
    cases strand
    · exact Or.inl ⟨(w, s), h, by simp_all [oldStrandOf]⟩
    · exact Or.inr ⟨(w, s), by simpa [Strand.orient, reverseComplement_eq] using h, by simp_all [oldStrandOf]⟩

theorem hit_of_walk (genome : Genome) (read : Read) (T : Int) (strand : Strand) (w : MapSpec.Window)
    (ref : Read) (hseq : MapSpec.windowSeq (og genome) w = some ref) (ws : List AlignmentSpec.Step)
    (hw : AlignmentSpec.IsMonotoneWalk ws (strand.orient read) ref)
    (hT : T ≤ AlignmentSpec.walkScore MapSpec.sc0 (strand.orient read) ref ws) :
    ∃ s, AlignmentSpec.walkScore MapSpec.sc0 (strand.orient read) ref ws ≤ s ∧
      ((w, oldStrandOf strand), s) ∈ MapSpec.hitsBoth MapSpec.sc0 T (og genome) read := by
  obtain ⟨c, hc, hlen⟩ := windowSeq_some hseq
  obtain ⟨⟨path, s⟩, hbest⟩ := AlignmentSpec.getBestAlignment_returns_some MapSpec.sc0 (strand.orient read) ref
  have hle := AlignmentSpec.getBestAlignment_returns_a_maximum_score _ _ _ path s ws hbest hw
  refine ⟨s, hle, mem_hitsBoth.2 ⟨strand, rfl, mem_hitsOf.2 ⟨mem_allWindows _ w c hc hlen, ?_, Int.le_trans hT hle⟩⟩⟩
  exact windowScore_eq_some.2 ⟨ref, path, hseq, hbest⟩

theorem alignment_of_hit_aux {genome : Genome} {read : Read} {T : Int} {pl : MapSpec.Placement} {s : Int}
    (h : (pl, s) ∈ MapSpec.hitsBoth MapSpec.sc0 T (og genome) read) :
    ∃ a : GenomicAlignment genome read,
      a.placement = ⟨pl.1.chr, pl.1.start, pl.1.start + pl.1.len,
        match pl.2 with | .fwd => .forward | .rev => .reverse⟩ ∧ a.score = s := by
  obtain ⟨strand, hst, hin⟩ := mem_hitsBoth.1 h
  obtain ⟨hwin, hscore, -⟩ := mem_hitsOf.1 hin
  obtain ⟨ys, bp, hseq, hbest⟩ := windowScore_eq_some.1 hscore
  obtain ⟨hwalk, hsc⟩ := AlignmentSpec.getBestAlignment_returns_a_valid_walk _ _ _ _ _ hbest
  have hfit : (⟨pl.1.chr, pl.1.start, pl.1.start + pl.1.len, strand⟩ : Placement).reference genome = some ys := by
    refine (reference_iff _ _ _).2 ⟨by simp, ?_⟩
    simpa using hseq
  refine ⟨⟨_, ys, hfit, pathOfWalk hwalk⟩, ?_, ?_⟩
  · cases strand <;> simp_all [oldStrandOf]
  · exact (score_pathOfWalk hwalk).trans hsc

end Spec.Hits
