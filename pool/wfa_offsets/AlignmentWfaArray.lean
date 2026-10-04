import AlignmentWfaCertified

namespace AlignmentSpec

def wfaRunArray (sc : Scoring) (xa ya : Array Char) : Option (Nat × Array RLevel) :=
  let m := xa.size
  let n := ya.size
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv := seedR m (m + n + 1) xa ya
  if cornerR m n lv then some (0, #[lv])
  else wfaLoopR m n xa ya (m + n + 1) pe po px
    ((m + n + 2) * po + 1) [lv] 1 #[lv]

theorem wfaRunArray_eq (sc : Scoring) (xa ya : Array Char) :
    wfaRunArray sc xa ya = wfaRunR sc xa.toList ya.toList := by
  simp [wfaRunArray, wfaRunR]

def walkCheckA (sc : Scoring) (xa ya : Array Char) :
    List Step → Nat → Nat → Option Step → Int → Option Int
  | [], i, j, _, acc =>
    match xa[i]?, ya[j]? with
    | none, none => some acc
    | _, _ => none
  | .diag :: w, i, j, _, acc =>
    match xa[i]?, ya[j]? with
    | some x, some y => walkCheckA sc xa ya w (i+1) (j+1) (some .diag) (acc + diagCost sc x y)
    | _, _ => none
  | .gapX :: w, i, j, prev, acc =>
    match ya[j]? with
    | some _ => walkCheckA sc xa ya w i (j+1) (some .gapX) (acc + gapXCost sc prev)
    | none => none
  | .gapY :: w, i, j, prev, acc =>
    match xa[i]? with
    | some _ => walkCheckA sc xa ya w (i+1) j (some .gapY) (acc + gapYCost sc prev)
    | none => none

theorem walkCheckA_eq (sc : Scoring) (xa ya : Array Char) (w : List Step) :
    ∀ i j prev acc, walkCheckA sc xa ya w i j prev acc =
      walkCheck sc w (xa.toList.drop i) (ya.toList.drop j) prev acc := by
  induction w with
  | nil =>
    intro i j prev acc
    simp only [walkCheckA, ← Array.getElem?_toList, ← List.head?_drop]
    generalize xa.toList.drop i = xs
    generalize ya.toList.drop j = ys
    cases xs <;> cases ys <;> rfl
  | cons step w ih =>
    intro i j prev acc
    cases step <;>
      simp only [walkCheckA, ih, ← Array.getElem?_toList, ← List.head?_drop, ← List.tail_drop] <;>
      generalize xa.toList.drop i = xs <;>
      generalize ya.toList.drop j = ys <;>
      cases xs <;> cases ys <;> rfl

def certifiedArray (sc : Scoring) (xa ya : Array Char) : Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunArray sc xa ya with
    | none => none
    | some (L, hist) =>
      let w := traceR xa.size ya.size (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist L
      match walkCheckA sc xa ya w 0 0 none 0 with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then
          some (w, s)
        else none
  else none

theorem certifiedArray_eq (sc : Scoring) (xa ya : Array Char) :
    certifiedArray sc xa ya = certifiedTraceR sc xa.toList ya.toList := by
  simp only [certifiedArray, certifiedTraceR, wfaRunArray_eq, Array.length_toList,
    walkCheckA_eq, List.drop_zero]
  rfl

def wfaAlignCA (sc : Scoring) (xa ya : Array Char) : Option (List Step × Int) :=
  match certifiedArray sc xa ya with
  | some r => some r
  | none => wfaAlignL sc xa.toList ya.toList

theorem wfaAlignCA_eq (sc : Scoring) (xa ya : Array Char) :
    wfaAlignCA sc xa ya = wfaAlignC sc xa.toList ya.toList := by
  simp only [wfaAlignCA, wfaAlignC, certifiedArray_eq]
  rfl

theorem wfaAlignCA_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignCA sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignCA_eq]; exact wfaAlignC_score sc xa.toList ya.toList

theorem wfaAlignCA_sound (sc : Scoring) (xa ya : Array Char) (w : List Step) (s : Int)
    (h : wfaAlignCA sc xa ya = some (w, s)) :
    IsMonotoneWalk w xa.toList ya.toList ∧ walkScore sc xa.toList ya.toList w = s := by
  rw [wfaAlignCA_eq] at h; exact wfaAlignC_sound sc xa.toList ya.toList w s h

theorem wfaAlignCA_isSome (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignCA sc xa ya).isSome := by
  rw [wfaAlignCA_eq]; exact wfaAlignC_isSome sc xa.toList ya.toList

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignCA_score
#print axioms AlignmentSpec.wfaAlignCA_sound
#print axioms AlignmentSpec.wfaAlignCA_isSome
