import AlignmentTraceRuns

namespace AlignmentSpec

def certifiedRuns (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  if wfaGateB sc then
    match wfaRunArray sc xa ya with
    | none => none
    | some (L, hist) =>
      let runs := traceRuns xa.size ya.size (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist L
      match checkRuns sc xa ya runs ⟨0,0,none,0⟩ with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then
          some (runs.toArray,s)
        else none
  else none

theorem certifiedRuns_spec (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : certifiedRuns sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold certifiedRuns at h
  split at h
  · rename_i hg
    cases hrun : wfaRunArray sc xa ya with
    | none => simp [hrun] at h
    | some r =>
      obtain ⟨L,hist⟩ := r
      rw [hrun] at h
      dsimp only at h
      split at h
      · simp at h
      · rename_i score hcheck
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          obtain ⟨hv,hs⟩ := checkRuns_sound sc xa ya _ score hcheck
          refine ⟨hv,hs,?_⟩
          rw [← hs]
          apply offsets_certify_score sc xa.toList ya.toList hg L
          · rw [← wfaRunR_eq, ← wfaRunArray_eq, hrun]; rfl
          · simpa only [Array.length_toList, ← hs, beq_iff_eq] using hc
        · simp at h
  · simp at h

/-- Direct run traceback, plus the exact small-error shortcut and proved fallback. -/
def wfaAlignK (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none =>
    match certifiedRuns sc xa ya with
    | some r => some r
    | none => (wfaAlignCA sc xa ya).map fun (w,s) => (unitCigar w,s)

theorem wfaAlignK_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignK sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold wfaAlignK
  cases hc : compactSmall sc xa ya with
  | some r =>
    have h := wfaAlignHC_score sc xa ya
    simpa [wfaAlignHC,hc] using h
  | none =>
    cases hr : certifiedRuns sc xa ya with
    | some r => exact (certifiedRuns_spec sc xa ya r.1 r.2 hr).2.2
    | none => simpa [Option.map_map, Function.comp_def] using wfaAlignCA_score sc xa ya

theorem wfaAlignK_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignK sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  unfold wfaAlignK at h
  cases hc : compactSmall sc xa ya with
  | some r =>
    apply wfaAlignHC_sound sc xa ya c s
    simpa [wfaAlignHC,hc] using h
  | none =>
    rw [hc] at h
    cases hr : certifiedRuns sc xa ya with
    | some r =>
      rw [hr] at h
      cases h
      exact ⟨(certifiedRuns_spec sc xa ya c s hr).1, (certifiedRuns_spec sc xa ya c s hr).2.1⟩
    | none =>
      have hh : wfaAlignHC sc xa ya = some (c,s) := by simpa [wfaAlignHC,hc,hr] using h
      exact wfaAlignHC_sound sc xa ya c s hh

theorem wfaAlignK_isSome (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignK sc xa ya).isSome := by
  obtain ⟨best,hb⟩ := getBestAlignment_returns_some sc xa.toList ya.toList
  have h := wfaAlignK_score sc xa ya
  rw [hb] at h
  cases hw : wfaAlignK sc xa ya with
  | none => rw [hw] at h; simp at h
  | some _ => rfl

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignK_score
#print axioms AlignmentSpec.wfaAlignK_sound
#print axioms AlignmentSpec.wfaAlignK_isSome
