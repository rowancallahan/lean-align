import AlignmentSmallErrors

/-! Compact tracebacks. Expansion occurs in the theorem, not in the fast path.
Every compact result denotes the same valid optimal walk as `wfaAlignH`.
The low-error diagonal result occupies one run regardless of sequence length.
-/
namespace AlignmentSpec

def expandCigar (c : Array (Step × Nat)) : List Step :=
  c.toList.flatMap fun (s, n) => List.replicate n s

def unitCigar (w : List Step) : Array (Step × Nat) :=
  w.toArray.map fun s => (s, 1)

theorem expand_unitCigar (w : List Step) : expandCigar (unitCigar w) = w := by
  simp [expandCigar, unitCigar, List.flatMap_map, Function.comp_def]

def compactSmall (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  if sc.matchScore = 0 ∧ sc.mismatchScore = -1 ∧ sc.gapExtend = -1 ∧
      sc.gapOpen ≤ 0 ∧ xa.size = ya.size then
    match diagCheckA sc xa ya xa.size 0 0 with
    | none => none
    | some s => if -2 ≤ s then some (#[(Step.diag, xa.size)], s) else none
  else none

theorem compactSmall_refines (sc : Scoring) (xa ya : Array Char) :
    (compactSmall sc xa ya).map (fun (c,s) => (expandCigar c,s)) = smallDiag sc xa ya := by
  unfold compactSmall smallDiag
  split
  · dsimp only
    cases diagCheckA sc xa ya xa.size 0 0 with
    | none => rfl
    | some s => by_cases hs : -2 ≤ s <;> simp [hs, expandCigar]
  · rfl

def wfaAlignHC (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none => (wfaAlignCA sc xa ya).map fun (w,s) => (unitCigar w,s)

theorem wfaAlignHC_refines (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignHC sc xa ya).map (fun (c,s) => (expandCigar c,s)) = wfaAlignH sc xa ya := by
  have hr := compactSmall_refines sc xa ya
  unfold wfaAlignHC wfaAlignH
  cases h : compactSmall sc xa ya with
  | none =>
    simp only [h, Option.map_none] at hr
    rw [← hr]
    simp [Function.comp_def, expand_unitCigar]
  | some r =>
    simp only [h, Option.map_some] at hr
    rw [← hr]
    rfl

theorem wfaAlignHC_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignHC sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  have h := congrArg (fun r => r.map Prod.snd) (wfaAlignHC_refines sc xa ya)
  simpa [Option.map_map, Function.comp_def] using h.trans (wfaAlignH_score sc xa ya)

theorem wfaAlignHC_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignHC sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  have hr := wfaAlignHC_refines sc xa ya
  rw [h] at hr
  exact wfaAlignH_sound sc xa ya (expandCigar c) s hr.symm

theorem wfaAlignHC_isSome (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignHC sc xa ya).isSome := by
  have h := wfaAlignH_isSome sc xa ya
  rw [← wfaAlignHC_refines] at h
  simpa using h

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignHC_score
#print axioms AlignmentSpec.wfaAlignHC_sound
#print axioms AlignmentSpec.wfaAlignHC_isSome
