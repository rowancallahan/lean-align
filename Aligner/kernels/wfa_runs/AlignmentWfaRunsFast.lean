import AlignmentWfaRuns
import AlignmentCigarCheckFast

/-!
`wfaAlignKF`: the proven kernel `wfaAlignK` with its runtime run checker
replaced by `checkRunsFast3` (proven equal to `checkRuns` in
AlignmentCigarCheckFast.lean).  `wfaAlignKF_eq` shows the two kernels are
the same function, so every theorem of `wfaAlignK` transfers.
-/
namespace AlignmentSpec

def certifiedRunsF (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  if wfaGateB sc then
    match wfaRunArray sc xa ya with
    | none => none
    | some (L, hist) =>
      let runs := traceRuns xa.size ya.size (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist L
      match checkRunsFast3 sc xa ya runs ⟨0,0,none,0⟩ with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then
          some (runs.toArray,s)
        else none
  else none

theorem certifiedRunsF_eq (sc : Scoring) (xa ya : Array Char) :
    certifiedRunsF sc xa ya = certifiedRuns sc xa ya := by
  unfold certifiedRunsF certifiedRuns
  simp only [checkRunsFast3_eq]
  try rfl

def wfaAlignKF (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none =>
    match certifiedRunsF sc xa ya with
    | some r => some r
    | none => (wfaAlignCA sc xa ya).map fun (w,s) => (unitCigar w,s)

theorem wfaAlignKF_eq (sc : Scoring) (xa ya : Array Char) : wfaAlignKF sc xa ya = wfaAlignK sc xa ya := by
  unfold wfaAlignKF wfaAlignK
  rw [certifiedRunsF_eq]
  try rfl

theorem wfaAlignKF_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignKF sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignKF_eq]; exact wfaAlignK_score sc xa ya

theorem wfaAlignKF_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignKF sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  rw [wfaAlignKF_eq] at h; exact wfaAlignK_sound sc xa ya c s h

theorem wfaAlignKF_isSome (sc : Scoring) (xa ya : Array Char) : (wfaAlignKF sc xa ya).isSome := by
  rw [wfaAlignKF_eq]; exact wfaAlignK_isSome sc xa ya

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignKF_eq
#print axioms AlignmentSpec.wfaAlignKF_score
#print axioms AlignmentSpec.wfaAlignKF_sound
#print axioms AlignmentSpec.wfaAlignKF_isSome
