import AlignmentWfa

/-!
Lazy candidate selection for the gap fronts.

`betterCell (stepWith pushGapX xs ys a) (stepWith pushGapX xs ys b)`
allocates two pushed cells and drops one.  When neither push demotes
(the y-suffix is non-empty) a gap-in-x push keeps `off`, so the winner
is decided by the SOURCE offsets and only the winner is pushed.  Same
for gap-in-y with `off + 1` on both sides.  The lemmas below are plain
equalities with the two-push form.
-/

namespace AlignmentSpec

@[inline] def stepPairX (xs ys : List Char) :
    Option WCell → Option WCell → Option WCell
  | some a, some b =>
      match a.ysRem, b.ysRem with
      | _ :: _, _ :: _ =>
          if b.off ≤ a.off then pushGapX a else pushGapX b
      | _, _ =>
          betterCell (stepWith pushGapX xs ys (some a))
            (stepWith pushGapX xs ys (some b))
  | a, b => betterCell (stepWith pushGapX xs ys a) (stepWith pushGapX xs ys b)

theorem stepPairX_eq (xs ys : List Char) (a b : Option WCell) :
    stepPairX xs ys a b =
      betterCell (stepWith pushGapX xs ys a) (stepWith pushGapX xs ys b) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      cases hya : a.ysRem with
      | nil => simp [stepPairX, hya]
      | cons y yr =>
        cases hyb : b.ysRem with
        | nil => simp [stepPairX, hya, hyb]
        | cons y' yr' =>
          simp only [stepPairX, hya, hyb, stepWith, pushGapX, betterCell]

@[inline] def stepPairY (xs ys : List Char) :
    Option WCell → Option WCell → Option WCell
  | some a, some b =>
      match a.xsRem, b.xsRem with
      | _ :: _, _ :: _ =>
          if b.off ≤ a.off then pushGapY a else pushGapY b
      | _, _ =>
          betterCell (stepWith pushGapY xs ys (some a))
            (stepWith pushGapY xs ys (some b))
  | a, b => betterCell (stepWith pushGapY xs ys a) (stepWith pushGapY xs ys b)

theorem stepPairY_eq (xs ys : List Char) (a b : Option WCell) :
    stepPairY xs ys a b =
      betterCell (stepWith pushGapY xs ys a) (stepWith pushGapY xs ys b) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      cases hxa : a.xsRem with
      | nil => simp [stepPairY, hxa]
      | cons x xr =>
        cases hxb : b.xsRem with
        | nil => simp [stepPairY, hxa, hxb]
        | cons x' xr' =>
          simp only [stepPairY, hxa, hxb, stepWith, pushGapY, betterCell]
          simp

/-- Diagonal candidate against an already-stored cell: the push has
`off + 1`, so it is materialised only when it wins. -/
@[inline] def stepDiag2 (xs ys : List Char) :
    Option WCell → Option WCell → Option WCell
  | some c, some x =>
      match c.xsRem, c.ysRem with
      | _ :: _, _ :: _ =>
          if x.off ≤ c.off + 1 then pushDiag c else some x
      | _, _ => betterCell (stepWith pushDiag xs ys (some c)) (some x)
  | m, x => betterCell (stepWith pushDiag xs ys m) x

theorem stepDiag2_eq (xs ys : List Char) (m x : Option WCell) :
    stepDiag2 xs ys m x = betterCell (stepWith pushDiag xs ys m) x := by
  cases m with
  | none => rfl
  | some c =>
    cases x with
    | none => rfl
    | some x =>
      cases hxc : c.xsRem with
      | nil => simp [stepDiag2, hxc]
      | cons a ar =>
        cases hyc : c.ysRem with
        | nil => simp [stepDiag2, hxc, hyc]
        | cons b br =>
          simp only [stepDiag2, hxc, hyc, stepWith, pushDiag, betterCell]

#print axioms stepDiag2_eq

#print axioms stepPairX_eq
#print axioms stepPairY_eq

end AlignmentSpec
