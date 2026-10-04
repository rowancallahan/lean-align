import AlignmentCompact

namespace AlignmentSpec

structure WalkCursor where
  i : Nat
  j : Nat
  prev : Option Step
  score : Int

@[inline] def stepCursor (sc : Scoring) (xa ya : Array Char) (s : Step)
    (c : WalkCursor) : Option WalkCursor :=
  match s with
  | .diag =>
    match xa[c.i]?, ya[c.j]? with
    | some x, some y => some ⟨c.i+1, c.j+1, some .diag, c.score + diagCost sc x y⟩
    | _, _ => none
  | .gapX =>
    match ya[c.j]? with
    | some _ => some ⟨c.i, c.j+1, some .gapX, c.score + gapXCost sc c.prev⟩
    | none => none
  | .gapY =>
    match xa[c.i]? with
    | some _ => some ⟨c.i+1, c.j, some .gapY, c.score + gapYCost sc c.prev⟩
    | none => none

def checkRepeat (sc : Scoring) (xa ya : Array Char) (s : Step) : Nat → WalkCursor → Option WalkCursor
  | 0, c => some c
  | n+1, c => (stepCursor sc xa ya s c).bind (checkRepeat sc xa ya s n)

theorem stepCursor_check (sc : Scoring) (xa ya : Array Char) (s : Step)
    (c : WalkCursor) (w : List Step) :
    (stepCursor sc xa ya s c).bind (fun c => walkCheckA sc xa ya w c.i c.j c.prev c.score) =
    walkCheckA sc xa ya (s :: w) c.i c.j c.prev c.score := by
  cases s <;> cases hx : xa[c.i]? <;> cases hy : ya[c.j]? <;>
    simp [stepCursor, walkCheckA, hx, hy]

theorem checkRepeat_check (sc : Scoring) (xa ya : Array Char) (s : Step) (n : Nat) :
    ∀ c w, (checkRepeat sc xa ya s n c).bind
        (fun c => walkCheckA sc xa ya w c.i c.j c.prev c.score) =
      walkCheckA sc xa ya (List.replicate n s ++ w) c.i c.j c.prev c.score := by
  induction n with
  | zero => intro c w; rfl
  | succ n ih =>
    intro c w
    simp only [checkRepeat, Option.bind_assoc, ih, List.replicate_succ, List.cons_append]
    exact stepCursor_check sc xa ya s c (List.replicate n s ++ w)

def checkRepeatFast (sc : Scoring) (xa ya : Array Char) (s : Step) :
    Nat → Nat → Nat → Option Step → Int → Option WalkCursor
  | 0, i, j, prev, acc => some ⟨i,j,prev,acc⟩
  | n+1, i, j, prev, acc =>
    match s with
    | .diag =>
      match xa[i]?, ya[j]? with
      | some x, some y => checkRepeatFast sc xa ya s n (i+1) (j+1) (some .diag) (acc + diagCost sc x y)
      | _, _ => none
    | .gapX =>
      match ya[j]? with
      | some _ => checkRepeatFast sc xa ya s n i (j+1) (some .gapX) (acc + gapXCost sc prev)
      | none => none
    | .gapY =>
      match xa[i]? with
      | some _ => checkRepeatFast sc xa ya s n (i+1) j (some .gapY) (acc + gapYCost sc prev)
      | none => none

theorem checkRepeatFast_eq (sc : Scoring) (xa ya : Array Char) (s : Step) (n : Nat) :
    ∀ i j prev acc, checkRepeatFast sc xa ya s n i j prev acc =
      checkRepeat sc xa ya s n ⟨i,j,prev,acc⟩ := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i j prev acc
    cases s <;> cases hx : xa[i]? <;> cases hy : ya[j]? <;>
      simp [checkRepeatFast, checkRepeat, stepCursor, hx, hy, ih]

def checkRuns (sc : Scoring) (xa ya : Array Char) : List (Step × Nat) → WalkCursor → Option Int
  | [], c => walkCheckA sc xa ya [] c.i c.j c.prev c.score
  | (s,n) :: rest, c =>
    (checkRepeatFast sc xa ya s n c.i c.j c.prev c.score).bind (checkRuns sc xa ya rest)

theorem checkRuns_check (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat)) :
    ∀ c, checkRuns sc xa ya runs c =
      walkCheckA sc xa ya (runs.flatMap fun (s,n) => List.replicate n s) c.i c.j c.prev c.score := by
  induction runs with
  | nil => intro c; rfl
  | cons sn rest ih =>
    intro c
    obtain ⟨s,n⟩ := sn
    have hf := funext ih
    simp only [checkRuns, checkRepeatFast_eq, List.flatMap_cons, hf]
    exact checkRepeat_check sc xa ya s n c _

theorem checkRuns_sound (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat)) (score : Int)
    (h : checkRuns sc xa ya runs ⟨0,0,none,0⟩ = some score) :
    IsMonotoneWalk (expandCigar runs.toArray) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar runs.toArray) = score := by
  rw [checkRuns_check, walkCheckA_eq] at h
  simp only [List.drop_zero] at h
  have hs := walkCheck_sound sc _ xa.toList ya.toList none 0 score h
  simpa [expandCigar, walkScore] using hs

end AlignmentSpec
#print axioms AlignmentSpec.checkRuns_sound
