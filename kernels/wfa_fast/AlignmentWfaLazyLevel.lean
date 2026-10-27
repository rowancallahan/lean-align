import AlignmentWfaFused
import AlignmentWfaLazy

/-!
The fused level (`nextLevelF`) with the overlap combine made a
parameter `c`, so the gap fronts can use `stepPairX` / `stepPairY`
(one push instead of two) and the diagonal candidate `stepDiag2`
(pushed only when it wins).  Every `…C` helper is the corresponding
`AlignmentWfaFused` helper with `c x y` in place of
`betterCell (g x) (h y)`; each equality lemma assumes exactly that
`c x y = betterCell (g x) (h y)` and is the same induction.
`nextLevelL_eq` then follows from `nextLevelF_eq`.
-/

namespace AlignmentSpec

abbrev Comb := Option WCell → Option WCell → Option WCell

@[specialize] def zipMapExtC (g h : Option WCell → Option WCell) (c : Comb) :
    List (Option WCell) → List (Option WCell) → List (Option WCell)
  | [], b => b.map h
  | a, [] => a.map g
  | x :: a, y :: b => c x y :: zipMapExtC g h c a b

theorem zipMapExtC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (a b : List (Option WCell)),
      zipMapExtC g h c a b = zipMapExt g h id a b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [zipMapExtC, zipMapExt]
  | cons x a ih =>
      intro b
      cases b with
      | nil => simp [zipMapExtC, zipMapExt]
      | cons y b => simp only [zipMapExtC, zipMapExt, hc, id, ih]

@[specialize] def zipPadLC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → List (Option WCell) → List (Option WCell) → List (Option WCell)
  | 0, a, b => zipMapExtC g h c a b
  | dp + 1, a, [] => padMap g id (dp + 1) a
  | dp + 1, a, y :: b => h y :: zipPadLC g h c dp a b

theorem zipPadLC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (dp : Nat) (a b : List (Option WCell)),
      zipPadLC g h c dp a b = zipPadL g h id dp a b := by
  intro dp
  induction dp with
  | zero => intro a b; simp only [zipPadLC, zipPadL, zipMapExtC_eq g h c hc]
  | succ dp ih =>
      intro a b
      cases b with
      | nil => rfl
      | cons y b => simp only [zipPadLC, zipPadL, ih, id]

@[specialize] def zipPadRC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → List (Option WCell) → List (Option WCell) → List (Option WCell)
  | 0, a, b => zipMapExtC g h c a b
  | dq + 1, [], b => padMap h id (dq + 1) b
  | dq + 1, x :: a, b => g x :: zipPadRC g h c dq a b

theorem zipPadRC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (dq : Nat) (a b : List (Option WCell)),
      zipPadRC g h c dq a b = zipPadR g h id dq a b := by
  intro dq
  induction dq with
  | zero => intro a b; simp only [zipPadRC, zipPadR, zipMapExtC_eq g h c hc]
  | succ dq ih =>
      intro a b
      cases a with
      | nil => rfl
      | cons x a => simp only [zipPadRC, zipPadR, ih, id]

@[inline] def zipPadTC (g h : Option WCell → Option WCell) (c : Comb)
    (p : Nat) (a : List (Option WCell)) (q : Nat)
    (b : List (Option WCell)) : TFront :=
  if p ≤ q then ⟨p, zipPadRC g h c (q - p) a b⟩
  else ⟨q, zipPadLC g h c (p - q) a b⟩

theorem zipPadTC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y))
    (p : Nat) (a : List (Option WCell)) (q : Nat) (b : List (Option WCell)) :
    zipPadTC g h c p a q b = zipPadT g h id p a q b := by
  unfold zipPadTC zipPadT
  split <;> simp only [zipPadRC_eq g h c hc, zipPadLC_eq g h c hc]

@[inline] def zipMapTC (g h : Option WCell → Option WCell) (c : Comb) :
    TFront → TFront → TFront
  | ⟨_, []⟩, ⟨q, b⟩ => ⟨q, b.map h⟩
  | ⟨p, a⟩, ⟨_, []⟩ => ⟨p, a.map g⟩
  | ⟨p, a⟩, ⟨q, b⟩ => zipPadTC g h c p a q b

theorem zipMapTC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) (f f' : TFront) :
    zipMapTC g h c f f' = zipMapT g h f f' := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [zipMapTC, zipMapT, zipPadTC_eq g h c hc]

@[inline] def zipMapLTC (g : Option WCell → Option WCell) (c : Comb) :
    TFront → TFront → TFront
  | ⟨_, []⟩, f' => f'
  | ⟨p, a⟩, ⟨_, []⟩ => ⟨p, a.map g⟩
  | ⟨p, a⟩, ⟨q, b⟩ => zipPadTC g id c p a q b

theorem zipMapLTC_eq (g : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) y) (f f' : TFront) :
    zipMapLTC g c f f' = zipMapLT g f f' := by
  have hc' : ∀ x y, c x y = betterCell (g x) (id y) := hc
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [zipMapLTC, zipMapLT, zipPadTC_eq g id c hc']

-- ── fuel-bounded (take-fused) variants ──

@[specialize] def zipMapExtKC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, _, k', b => mapTake h k' b
  | _ + 1, [], k', b => mapTake h k' b
  | k + 1, x :: a, 0, _ => mapTake g (k + 1) (x :: a)
  | k + 1, x :: a, _ + 1, [] => mapTake g (k + 1) (x :: a)
  | k + 1, x :: a, k' + 1, y :: b =>
      c x y :: zipMapExtKC g h c k a k' b

theorem zipMapExtKC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (k : Nat) (a : List (Option WCell)) (k' : Nat) (b : List (Option WCell)),
      zipMapExtKC g h c k a k' b = zipMapExtK g h k a k' b := by
  intro k a
  induction a generalizing k with
  | nil => intro k' b; cases k <;> rfl
  | cons x a ih =>
      intro k' b
      cases k with
      | zero => rfl
      | succ k =>
          cases k' with
          | zero => rfl
          | succ k' =>
              cases b with
              | nil => rfl
              | cons y b => simp only [zipMapExtKC, zipMapExtK, hc, ih]

@[specialize] def zipPadLKC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, k, a, k', b => zipMapExtKC g h c k a k' b
  | dp + 1, k, a, 0, _ => padMapK g (dp + 1) k a
  | dp + 1, k, a, _ + 1, [] => padMapK g (dp + 1) k a
  | dp + 1, k, a, k' + 1, y :: b => h y :: zipPadLKC g h c dp k a k' b

theorem zipPadLKC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (dp k : Nat) (a : List (Option WCell)) (k' : Nat) (b : List (Option WCell)),
      zipPadLKC g h c dp k a k' b = zipPadLK g h dp k a k' b := by
  intro dp
  induction dp with
  | zero => intro k a k' b; simp only [zipPadLKC, zipPadLK, zipMapExtKC_eq g h c hc]
  | succ dp ih =>
      intro k a k' b
      cases k' with
      | zero => rfl
      | succ k' =>
          cases b with
          | nil => rfl
          | cons y b => simp only [zipPadLKC, zipPadLK, ih]

@[specialize] def zipPadRKC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, k, a, k', b => zipMapExtKC g h c k a k' b
  | dq + 1, 0, _, k', b => padMapK h (dq + 1) k' b
  | dq + 1, _ + 1, [], k', b => padMapK h (dq + 1) k' b
  | dq + 1, k + 1, x :: a, k', b => g x :: zipPadRKC g h c dq k a k' b

theorem zipPadRKC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) :
    ∀ (dq k : Nat) (a : List (Option WCell)) (k' : Nat) (b : List (Option WCell)),
      zipPadRKC g h c dq k a k' b = zipPadRK g h dq k a k' b := by
  intro dq
  induction dq with
  | zero => intro k a k' b; simp only [zipPadRKC, zipPadRK, zipMapExtKC_eq g h c hc]
  | succ dq ih =>
      intro k a k' b
      cases k with
      | zero => rfl
      | succ k =>
          cases a with
          | nil => rfl
          | cons x a => simp only [zipPadRKC, zipPadRK, ih]

@[inline] def zipPadTKC (g h : Option WCell → Option WCell) (c : Comb)
    (p k : Nat) (a : List (Option WCell)) (q k' : Nat)
    (b : List (Option WCell)) : TFront :=
  if p ≤ q then ⟨p, zipPadRKC g h c (q - p) k a k' b⟩
  else ⟨q, zipPadLKC g h c (p - q) k a k' b⟩

theorem zipPadTKC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y))
    (p k : Nat) (a : List (Option WCell)) (q k' : Nat) (b : List (Option WCell)) :
    zipPadTKC g h c p k a q k' b = zipPadTK g h p k a q k' b := by
  unfold zipPadTKC zipPadTK
  split <;> simp only [zipPadRKC_eq g h c hc, zipPadLKC_eq g h c hc]

@[inline] def zipMapTKC (g h : Option WCell → Option WCell) (c : Comb) :
    Nat → TFront → Nat → TFront → TFront
  | 0, _, k', ⟨q, b⟩ => ⟨q, mapTake h k' b⟩
  | _ + 1, ⟨_, []⟩, k', ⟨q, b⟩ => ⟨q, mapTake h k' b⟩
  | k + 1, ⟨p, x :: a⟩, 0, _ => ⟨p, mapTake g (k + 1) (x :: a)⟩
  | k + 1, ⟨p, x :: a⟩, _ + 1, ⟨_, []⟩ => ⟨p, mapTake g (k + 1) (x :: a)⟩
  | k + 1, ⟨p, x :: a⟩, k' + 1, ⟨q, y :: b⟩ =>
      zipPadTKC g h c p (k + 1) (x :: a) q (k' + 1) (y :: b)

theorem zipMapTKC_eq (g h : Option WCell → Option WCell) (c : Comb)
    (hc : ∀ x y, c x y = betterCell (g x) (h y)) (k : Nat) (f : TFront)
    (k' : Nat) (f' : TFront) :
    zipMapTKC g h c k f k' f' = zipMapTK g h k f k' f' := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩ <;>
    cases k <;> cases k' <;>
    simp only [zipMapTKC, zipMapTK, zipPadTKC_eq g h c hc]

-- ── inline copies of the per-cell helpers (bodies identical; `rfl`) ──

@[inline] def pushGapXL (c : WCell) : Option WCell :=
  match c.ysRem with
  | _ :: yr => some ⟨c.off, c.joff + 1, c.xsRem, yr, .gapX :: c.walk⟩
  | [] => none

theorem pushGapXL_eq : @pushGapXL = @pushGapX := rfl

@[inline] def pushGapYL (c : WCell) : Option WCell :=
  match c.xsRem with
  | _ :: xr => some ⟨c.off + 1, c.joff, xr, c.ysRem, .gapY :: c.walk⟩
  | [] => none

theorem pushGapYL_eq : @pushGapYL = @pushGapY := rfl

@[inline] def pushDiagL (c : WCell) : Option WCell :=
  match c.xsRem, c.ysRem with
  | _ :: xr, _ :: yr =>
      some ⟨c.off + 1, c.joff + 1, xr, yr, .diag :: c.walk⟩
  | _, _ => none

theorem pushDiagL_eq : @pushDiagL = @pushDiag := rfl

@[inline] def stepWithL (push : WCell → Option WCell) (xs ys : List Char) :
    Option WCell → Option WCell
  | some c =>
      match push c with
      | some r => some r
      | none => (demoteCell xs ys c).bind push
  | none => none

theorem stepWithL_eq : @stepWithL = @stepWith := rfl

/-- `extendCell` without allocating a fresh cell when nothing extends. -/
@[inline] def extendCellL (c : WCell) : WCell :=
  match c.xsRem, c.ysRem with
  | x :: xr, y :: yr =>
      if x = y then extendGo (c.off + 1) (c.joff + 1) (.diag :: c.walk) xr yr
      else c
  | _, _ => c

theorem extendCellL_eq : @extendCellL = @extendCell := by
  funext c
  rcases c with ⟨i, j, xs, ys, w⟩
  cases xs with
  | nil => cases ys <;> rfl
  | cons x xr =>
    cases ys with
    | nil => rfl
    | cons y yr =>
      simp only [extendCellL, extendCell, extendGo]

/-- `Option.map extendCellL` that returns the SAME option when nothing
extends (no fresh `some` box). -/
@[inline] def extOpt : Option WCell → Option WCell
  | none => none
  | o@(some c) =>
      match c.xsRem, c.ysRem with
      | x :: xr, y :: yr =>
          if x = y then
            some (extendGo (c.off + 1) (c.joff + 1) (.diag :: c.walk) xr yr)
          else o
      | _, _ => o

theorem extOpt_eq : @extOpt = Option.map extendCell := by
  funext o
  cases o with
  | none => rfl
  | some c =>
    rcases c with ⟨i, j, xs, ys, w⟩
    cases xs with
    | nil => cases ys <;> rfl
    | cons x xr =>
      cases ys with
      | nil => rfl
      | cons y yr =>
        simp only [extOpt, Option.map, extendCell, extendGo]
        split <;> rfl

-- ── the level ──

def nextLevelL (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List TLevel) : TLevel :=
  let gx := stepWithL pushGapXL xs ys
  let gy := stepWithL pushGapYL xs ys
  let gd := stepWithL pushDiagL xs ys
  let xf := zipMapTC gx gx (stepPairX xs ys)
    (shiftUpT (frontAtT hist pe (·.xf)))
    (shiftUpT (frontAtT hist po (·.mf)))
  let se := shiftDownK len (frontAtT hist pe (·.yf))
  let so := shiftDownK len (frontAtT hist po (·.mf))
  let yf := zipMapTKC gy gy (stepPairY xs ys) se.1 se.2 so.1 so.2
  ⟨zipTE extOpt
      (zipMapLTC gd (stepDiag2 xs ys) (frontAtT hist px (·.mf)) xf) yf,
    xf, yf⟩

theorem nextLevelL_eq (xs ys : List Char) (len pe po px : Nat)
    (hist : List TLevel) :
    nextLevelL xs ys len pe po px hist = nextLevelT xs ys len pe po px hist := by
  rw [← nextLevelF_eq]
  simp only [nextLevelL, nextLevelF, stepWithL_eq, pushGapXL_eq, pushGapYL_eq,
    pushDiagL_eq, extendCellL_eq, extOpt_eq,
    zipMapTC_eq _ _ _ (stepPairX_eq xs ys),
    zipMapTKC_eq _ _ _ (stepPairY_eq xs ys),
    zipMapLTC_eq _ _ (stepDiag2_eq xs ys)]

#print axioms nextLevelL_eq

end AlignmentSpec
