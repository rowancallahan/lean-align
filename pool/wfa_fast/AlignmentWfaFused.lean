import AlignmentWfa

/-!
Fused banded wavefront step.

`nextLevelT` builds each front through several intermediate lists
(`mapT`, then `zipT`, which materialises `List.replicate` padding and
zips with `zipExt`, then a final `mapT` for extension).  `nextLevelF`
below computes the SAME `TLevel` (`nextLevelF_eq`, plain structural
equality) in one recursive pass per front: the maps are applied inside
the zip (`g`/`h` on the inputs, `e` on each emitted cell), and the pad
difference is walked by a counter instead of being allocated.
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- Fused list helpers
-- ══════════════════════════════════════════════════════════════════

/-- `(List.replicate n none ++ a.map g).map e`, built in one pass. -/
@[specialize] def padMap (g e : Option WCell → Option WCell) :
    Nat → List (Option WCell) → List (Option WCell)
  | 0, a => a.map (fun x => e (g x))
  | n + 1, a => e none :: padMap g e n a

/-- `(zipExt (a.map g) (b.map h)).map e` without allocating the mapped
lists. -/
@[specialize] def zipMapExt (g h e : Option WCell → Option WCell) :
    List (Option WCell) → List (Option WCell) → List (Option WCell)
  | [], b => b.map (fun y => e (h y))
  | a, [] => a.map (fun x => e (g x))
  | x :: a, y :: b => e (betterCell (g x) (h y)) :: zipMapExt g h e a b

/-- `(zipExt (replicate dp none ++ a.map g) (b.map h)).map e`: walk the
left padding against `b`'s head cells (a `none` on the left just yields
the right cell). -/
@[specialize] def zipPadL (g h e : Option WCell → Option WCell) :
    Nat → List (Option WCell) → List (Option WCell) → List (Option WCell)
  | 0, a, b => zipMapExt g h e a b
  | dp + 1, a, [] => padMap g e (dp + 1) a
  | dp + 1, a, y :: b => e (h y) :: zipPadL g h e dp a b

/-- `(zipExt (a.map g) (replicate dq none ++ b.map h)).map e`. -/
@[specialize] def zipPadR (g h e : Option WCell → Option WCell) :
    Nat → List (Option WCell) → List (Option WCell) → List (Option WCell)
  | 0, a, b => zipMapExt g h e a b
  | dq + 1, [], b => padMap h e (dq + 1) b
  | dq + 1, x :: a, b => e (g x) :: zipPadR g h e dq a b

/-- The general (both bands non-empty) case of `mapT e (zipT (mapT g f)
(mapT h f'))`, without the replicate padding. -/
@[inline] def zipPadT (g h e : Option WCell → Option WCell)
    (p : Nat) (a : List (Option WCell)) (q : Nat)
    (b : List (Option WCell)) : TFront :=
  if p ≤ q then ⟨p, zipPadR g h e (q - p) a b⟩
  else ⟨q, zipPadL g h e (p - q) a b⟩

/-- `zipT (mapT g f) (mapT h f')`, fused. -/
@[inline] def zipMapT (g h : Option WCell → Option WCell) :
    TFront → TFront → TFront
  | ⟨_, []⟩, ⟨q, b⟩ => ⟨q, b.map h⟩
  | ⟨p, a⟩, ⟨_, []⟩ => ⟨p, a.map g⟩
  | ⟨p, a⟩, ⟨q, b⟩ => zipPadT g h id p a q b

/-- `zipT (mapT g f) f'`, fused (the right band is used as is). -/
@[inline] def zipMapLT (g : Option WCell → Option WCell) :
    TFront → TFront → TFront
  | ⟨_, []⟩, f' => f'
  | ⟨p, a⟩, ⟨_, []⟩ => ⟨p, a.map g⟩
  | ⟨p, a⟩, ⟨q, b⟩ => zipPadT g id id p a q b

/-- `mapT e (zipT f f')`, fused: the post-map is applied in the same
pass that builds the zipped body. -/
@[inline] def zipTE (e : Option WCell → Option WCell) :
    TFront → TFront → TFront
  | ⟨_, []⟩, ⟨q, b⟩ => ⟨q, b.map e⟩
  | ⟨p, a⟩, ⟨_, []⟩ => ⟨p, a.map e⟩
  | ⟨p, a⟩, ⟨q, b⟩ => zipPadT id id e p a q b

-- ── Fuel-bounded variants: `List.take k` folded into the zip ──────

/-- `(a.take k).map g` in one pass. -/
@[specialize] def mapTake (g : Option WCell → Option WCell) :
    Nat → List (Option WCell) → List (Option WCell)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, x :: a => g x :: mapTake g k a

/-- `List.replicate n none ++ (a.take k).map g`. -/
@[specialize] def padMapK (g : Option WCell → Option WCell) :
    Nat → Nat → List (Option WCell) → List (Option WCell)
  | 0, k, a => mapTake g k a
  | n + 1, k, a => none :: padMapK g n k a

/-- `zipExt ((a.take k).map g) ((b.take k').map h)`. -/
@[specialize] def zipMapExtK (g h : Option WCell → Option WCell) :
    Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, _, k', b => mapTake h k' b
  | _ + 1, [], k', b => mapTake h k' b
  | k + 1, x :: a, 0, _ => mapTake g (k + 1) (x :: a)
  | k + 1, x :: a, _ + 1, [] => mapTake g (k + 1) (x :: a)
  | k + 1, x :: a, k' + 1, y :: b =>
      betterCell (g x) (h y) :: zipMapExtK g h k a k' b

/-- `zipExt (replicate dp none ++ (a.take k).map g) ((b.take k').map h)`. -/
@[specialize] def zipPadLK (g h : Option WCell → Option WCell) :
    Nat → Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, k, a, k', b => zipMapExtK g h k a k' b
  | dp + 1, k, a, 0, _ => padMapK g (dp + 1) k a
  | dp + 1, k, a, _ + 1, [] => padMapK g (dp + 1) k a
  | dp + 1, k, a, k' + 1, y :: b => h y :: zipPadLK g h dp k a k' b

/-- `zipExt ((a.take k).map g) (replicate dq none ++ (b.take k').map h)`. -/
@[specialize] def zipPadRK (g h : Option WCell → Option WCell) :
    Nat → Nat → List (Option WCell) → Nat → List (Option WCell) →
    List (Option WCell)
  | 0, k, a, k', b => zipMapExtK g h k a k' b
  | dq + 1, 0, _, k', b => padMapK h (dq + 1) k' b
  | dq + 1, _ + 1, [], k', b => padMapK h (dq + 1) k' b
  | dq + 1, k + 1, x :: a, k', b => g x :: zipPadRK g h dq k a k' b

/-- `zipPadT g h id p (a.take k) q (b.take k')`. -/
@[inline] def zipPadTK (g h : Option WCell → Option WCell)
    (p k : Nat) (a : List (Option WCell)) (q k' : Nat)
    (b : List (Option WCell)) : TFront :=
  if p ≤ q then ⟨p, zipPadRK g h (q - p) k a k' b⟩
  else ⟨q, zipPadLK g h (p - q) k a k' b⟩

/-- `zipMapT g h ⟨f.pad, f.body.take k⟩ ⟨f'.pad, f'.body.take k'⟩`: the
`take`s are fuel counters, not list passes.  A band is empty when its
fuel or its body is. -/
@[inline] def zipMapTK (g h : Option WCell → Option WCell) :
    Nat → TFront → Nat → TFront → TFront
  | 0, _, k', ⟨q, b⟩ => ⟨q, mapTake h k' b⟩
  | _ + 1, ⟨_, []⟩, k', ⟨q, b⟩ => ⟨q, mapTake h k' b⟩
  | k + 1, ⟨p, x :: a⟩, 0, _ => ⟨p, mapTake g (k + 1) (x :: a)⟩
  | k + 1, ⟨p, x :: a⟩, _ + 1, ⟨_, []⟩ => ⟨p, mapTake g (k + 1) (x :: a)⟩
  | k + 1, ⟨p, x :: a⟩, k' + 1, ⟨q, y :: b⟩ =>
      zipPadTK g h p (k + 1) (x :: a) q (k' + 1) (y :: b)

/-- `shiftDownT` with the `take` deferred: returns the take bound and
the un-truncated shifted band (`drop 1` is a constant-time tail). -/
@[inline] def shiftDownK (len : Nat) (f : TFront) : Nat × TFront :=
  match f.pad with
  | p + 1 => (len - (p + 1), ⟨p, f.body⟩)
  | 0 => (len - 1, ⟨0, f.body.drop 1⟩)

/-- One banded wavefront step, fused — equal to `nextLevelT`
(`nextLevelF_eq`). -/
def nextLevelF (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List TLevel) : TLevel :=
  let gx := stepWith pushGapX xs ys
  let gy := stepWith pushGapY xs ys
  let gd := stepWith pushDiag xs ys
  let xf := zipMapT gx gx
    (shiftUpT (frontAtT hist pe (·.xf)))
    (shiftUpT (frontAtT hist po (·.mf)))
  let se := shiftDownK len (frontAtT hist pe (·.yf))
  let so := shiftDownK len (frontAtT hist po (·.mf))
  let yf := zipMapTK gy gy se.1 se.2 so.1 so.2
  ⟨zipTE (Option.map extendCell) (zipMapLT gd (frontAtT hist px (·.mf)) xf) yf,
    xf, yf⟩

-- ══════════════════════════════════════════════════════════════════
-- Proofs
-- ══════════════════════════════════════════════════════════════════

theorem betterCell_none_left (x : Option WCell) :
    betterCell none x = x := rfl

theorem padMap_eq (g e : Option WCell → Option WCell) :
    ∀ (n : Nat) (a : List (Option WCell)),
      padMap g e n a = (List.replicate n none ++ a.map g).map e := by
  intro n
  induction n with
  | zero => intro a; simp only [padMap, List.replicate_zero, List.nil_append,
      List.map_map, Function.comp_def]
  | succ n ih =>
      intro a
      simp only [padMap, ih, List.replicate_succ, List.cons_append,
        List.map_cons]

theorem zipMapExt_eq (g h e : Option WCell → Option WCell) :
    ∀ (a b : List (Option WCell)),
      zipMapExt g h e a b = (zipExt (a.map g) (b.map h)).map e := by
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp only [zipMapExt, List.map_nil, List.map_cons, zipExt,
        List.map_map, Function.comp_def]
  | cons x a ih =>
      intro b
      cases b with
      | nil => simp only [zipMapExt, List.map_nil, List.map_cons, zipExt,
          List.map_map, Function.comp_def]
      | cons y b => simp only [zipMapExt, List.map_cons, zipExt, ih]

theorem zipPadL_eq (g h e : Option WCell → Option WCell) :
    ∀ (dp : Nat) (a b : List (Option WCell)),
      zipPadL g h e dp a b =
        (zipExt (List.replicate dp none ++ a.map g) (b.map h)).map e := by
  intro dp
  induction dp with
  | zero => intro a b; simp only [zipPadL, zipMapExt_eq, List.replicate_zero,
      List.nil_append]
  | succ dp ih =>
      intro a b
      cases b with
      | nil => simp only [zipPadL, padMap_eq, List.map_nil, zipExt_nil_right]
      | cons y b =>
          simp only [zipPadL, ih, List.replicate_succ, List.cons_append,
            List.map_cons, zipExt, betterCell_none_left]

theorem zipPadR_eq (g h e : Option WCell → Option WCell) :
    ∀ (dq : Nat) (a b : List (Option WCell)),
      zipPadR g h e dq a b =
        (zipExt (a.map g) (List.replicate dq none ++ b.map h)).map e := by
  intro dq
  induction dq with
  | zero => intro a b; simp only [zipPadR, zipMapExt_eq, List.replicate_zero,
      List.nil_append]
  | succ dq ih =>
      intro a b
      cases a with
      | nil => simp only [zipPadR, padMap_eq, List.map_nil, zipExt]
      | cons x a =>
          simp only [zipPadR, ih, List.replicate_succ, List.cons_append,
            List.map_cons, zipExt, betterCell_none_right]

theorem zipPadT_eq (g h e : Option WCell → Option WCell)
    (p : Nat) (a : List (Option WCell)) (q : Nat)
    (b : List (Option WCell)) :
    zipPadT g h e p a q b =
      ⟨min p q, (zipExt (List.replicate (p - min p q) none ++ a.map g)
        (List.replicate (q - min p q) none ++ b.map h)).map e⟩ := by
  unfold zipPadT
  split
  · rename_i hpq
    rw [Nat.min_eq_left hpq, Nat.sub_self, List.replicate_zero,
      List.nil_append, zipPadR_eq]
  · rename_i hpq
    rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hpq)),
      Nat.sub_self, List.replicate_zero, List.nil_append, zipPadL_eq]

theorem zipMapT_eq (g h : Option WCell → Option WCell) (f f' : TFront) :
    zipMapT g h f f' = zipT (mapT g f) (mapT h f') := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [zipMapT, mapT, List.map_cons, zipT, zipPadT_eq,
      List.map_id_fun, id]

theorem zipMapLT_eq (g : Option WCell → Option WCell) (f f' : TFront) :
    zipMapLT g f f' = zipT (mapT g f) f' := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [zipMapLT, mapT, List.map_cons, zipT, zipPadT_eq,
      List.map_id_fun, id]

theorem zipTE_eq (e : Option WCell → Option WCell) (f f' : TFront) :
    zipTE e f f' = mapT e (zipT f f') := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [zipTE, mapT, zipT, zipPadT_eq, List.map_id_fun, id]

theorem mapT_shiftUpT (g : Option WCell → Option WCell) (f : TFront) :
    mapT g (shiftUpT f) = shiftUpT (mapT g f) := rfl

theorem mapT_shiftDownT (g : Option WCell → Option WCell) (len : Nat)
    (f : TFront) :
    mapT g (shiftDownT len f) = shiftDownT len (mapT g f) := by
  rcases f with ⟨_ | p, body⟩
  · simp only [mapT, shiftDownT, List.map_take, List.map_drop]
  · simp only [mapT, shiftDownT, List.map_take]

-- ── Fuel-bounded variants ──

theorem mapTake_eq (g : Option WCell → Option WCell) :
    ∀ (k : Nat) (a : List (Option WCell)),
      mapTake g k a = (a.take k).map g := by
  intro k a
  induction a generalizing k with
  | nil => cases k <;> rfl
  | cons x a ih =>
      cases k with
      | zero => rfl
      | succ k => simp only [mapTake, List.take_succ_cons, List.map_cons, ih]

theorem padMapK_eq (g : Option WCell → Option WCell) :
    ∀ (n k : Nat) (a : List (Option WCell)),
      padMapK g n k a = List.replicate n none ++ (a.take k).map g := by
  intro n
  induction n with
  | zero => intro k a; simp only [padMapK, mapTake_eq, List.replicate_zero,
      List.nil_append]
  | succ n ih =>
      intro k a
      simp only [padMapK, ih, List.replicate_succ, List.cons_append]

theorem zipMapExtK_eq (g h : Option WCell → Option WCell) :
    ∀ (k : Nat) (a : List (Option WCell)) (k' : Nat)
      (b : List (Option WCell)),
      zipMapExtK g h k a k' b = zipExt ((a.take k).map g) ((b.take k').map h) := by
  intro k a
  induction a generalizing k with
  | nil =>
      intro k' b
      cases k <;> simp only [zipMapExtK, mapTake_eq, List.take_nil,
        List.map_nil, zipExt]
  | cons x a ih =>
      intro k' b
      cases k with
      | zero => simp only [zipMapExtK, mapTake_eq, List.take_zero, List.map_nil,
          zipExt]
      | succ k =>
          cases k' with
          | zero => simp only [zipMapExtK, mapTake_eq, List.take_zero,
              List.map_nil, List.take_succ_cons, List.map_cons, zipExt]
          | succ k' =>
              cases b with
              | nil => simp only [zipMapExtK, mapTake_eq, List.take_nil,
                  List.map_nil, List.take_succ_cons, List.map_cons, zipExt]
              | cons y b => simp only [zipMapExtK, List.take_succ_cons,
                  List.map_cons, zipExt, ih]

theorem zipPadLK_eq (g h : Option WCell → Option WCell) :
    ∀ (dp k : Nat) (a : List (Option WCell)) (k' : Nat)
      (b : List (Option WCell)),
      zipPadLK g h dp k a k' b =
        zipExt (List.replicate dp none ++ (a.take k).map g)
          ((b.take k').map h) := by
  intro dp
  induction dp with
  | zero => intro k a k' b; simp only [zipPadLK, zipMapExtK_eq,
      List.replicate_zero, List.nil_append]
  | succ dp ih =>
      intro k a k' b
      cases k' with
      | zero => simp only [zipPadLK, padMapK_eq, List.take_zero, List.map_nil,
          zipExt_nil_right]
      | succ k' =>
          cases b with
          | nil => simp only [zipPadLK, padMapK_eq, List.take_nil, List.map_nil,
              zipExt_nil_right]
          | cons y b =>
              simp only [zipPadLK, ih, List.replicate_succ, List.cons_append,
                List.take_succ_cons, List.map_cons, zipExt, betterCell_none_left]

theorem zipPadRK_eq (g h : Option WCell → Option WCell) :
    ∀ (dq k : Nat) (a : List (Option WCell)) (k' : Nat)
      (b : List (Option WCell)),
      zipPadRK g h dq k a k' b =
        zipExt ((a.take k).map g)
          (List.replicate dq none ++ (b.take k').map h) := by
  intro dq
  induction dq with
  | zero => intro k a k' b; simp only [zipPadRK, zipMapExtK_eq,
      List.replicate_zero, List.nil_append]
  | succ dq ih =>
      intro k a k' b
      cases k with
      | zero => simp only [zipPadRK, padMapK_eq, List.take_zero, List.map_nil,
          zipExt]
      | succ k =>
          cases a with
          | nil => simp only [zipPadRK, padMapK_eq, List.take_nil, List.map_nil,
              zipExt]
          | cons x a =>
              simp only [zipPadRK, ih, List.replicate_succ, List.cons_append,
                List.take_succ_cons, List.map_cons, zipExt, betterCell_none_right]

theorem zipPadTK_eq (g h : Option WCell → Option WCell)
    (p k : Nat) (a : List (Option WCell)) (q k' : Nat)
    (b : List (Option WCell)) :
    zipPadTK g h p k a q k' b = zipPadT g h id p (a.take k) q (b.take k') := by
  unfold zipPadTK zipPadT
  split
  · rw [zipPadRK_eq, zipPadR_eq, List.map_id_fun, id]
  · rw [zipPadLK_eq, zipPadL_eq, List.map_id_fun, id]

theorem zipMapTK_eq (g h : Option WCell → Option WCell) (k : Nat) (f : TFront)
    (k' : Nat) (f' : TFront) :
    zipMapTK g h k f k' f' =
      zipMapT g h ⟨f.pad, f.body.take k⟩ ⟨f'.pad, f'.body.take k'⟩ := by
  rcases f with ⟨p, _ | ⟨x, a⟩⟩ <;> rcases f' with ⟨q, _ | ⟨y, b⟩⟩ <;>
    cases k <;> cases k' <;>
    simp only [zipMapTK, zipMapT, mapTake_eq, List.take_zero, List.take_nil,
      List.take_succ_cons, zipPadTK_eq]

theorem shiftDownK_eq (len : Nat) (f : TFront) :
    shiftDownT len f =
      ⟨(shiftDownK len f).2.pad,
        (shiftDownK len f).2.body.take (shiftDownK len f).1⟩ := by
  rcases f with ⟨_ | p, body⟩ <;> rfl

theorem nextLevelF_eq (xs ys : List Char) (len pe po px : Nat)
    (hist : List TLevel) :
    nextLevelF xs ys len pe po px hist = nextLevelT xs ys len pe po px hist := by
  simp only [nextLevelF, nextLevelT, zipMapTK_eq, ← shiftDownK_eq, zipMapT_eq,
    zipMapLT_eq, zipTE_eq, mapT_shiftUpT, mapT_shiftDownT]

#print axioms nextLevelF_eq

end AlignmentSpec
