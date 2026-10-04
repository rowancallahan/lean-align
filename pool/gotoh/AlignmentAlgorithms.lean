import AlignmentSpec

/-!
Fast implementations of the frozen alignment specification, each proved to
return exactly the same `Option (List Step × Int)` as `getBestAlignment`
for every input and every scoring.

The frozen spec is `AlignmentSpec.lean` (untouched by this file).  The
route to speed:

1. `bestAux` restates the spec objective with an explicit previous-step
   parameter, so subproblems can be named.
2. The Bellman lemmas (`bestAux_nil_nil` … `bestAux_cons_cons`) prove the
   principle of optimality: the spec objective satisfies the three-way
   alignment recurrence, including tie-breaking (the spec's earliest
   maximum corresponds to the left bias of binary `maxOn`).
3. `bellmanAlign` implements that recurrence directly (still exponential
   time, but no candidate lists are materialised).
4. `gotohAlign` tabulates the recurrence row by row (Gotoh's three-state
   scheme with full-path cells), giving O(m·n) time.
5. `gotohFusedAlign` is a constant-factor optimisation of the same table.
-/

namespace AlignmentSpec

/-- The spec objective, generalised over the previous step.  With
`prev = none` this is definitionally the body of `getBestAlignment`. -/
def bestAux (sc : Scoring) (xs ys : List Char) (prev : Option Step) :
    Option (List Step × Int) :=
  ((allPaths xs ys).map fun p => (p, scoreWalk sc p xs ys prev)).maxOn?
    fun item => item.2

theorem getBestAlignment_eq_bestAux (sc : Scoring) (xs ys : List Char) :
    getBestAlignment sc xs ys = bestAux sc xs ys none :=
  rfl

/-- Cost of one alignment column, split out of `scoreWalk` so the
recurrence can name it. -/
def diagCost (sc : Scoring) (x y : Char) : Int :=
  if x = y then sc.matchScore else sc.mismatchScore

def gapXCost (sc : Scoring) (prev : Option Step) : Int :=
  if prev = some .gapX then sc.gapExtend else sc.gapOpen + sc.gapExtend

def gapYCost (sc : Scoring) (prev : Option Step) : Int :=
  if prev = some .gapY then sc.gapExtend else sc.gapOpen + sc.gapExtend

theorem scoreWalk_diag_cons (sc : Scoring) (p : List Step)
    (x : Char) (xs : List Char) (y : Char) (ys : List Char)
    (prev : Option Step) :
    scoreWalk sc (.diag :: p) (x :: xs) (y :: ys) prev =
      diagCost sc x y + scoreWalk sc p xs ys (some .diag) :=
  rfl

theorem scoreWalk_gapX_cons (sc : Scoring) (p : List Step)
    (xs : List Char) (y : Char) (ys : List Char) (prev : Option Step) :
    scoreWalk sc (.gapX :: p) xs (y :: ys) prev =
      gapXCost sc prev + scoreWalk sc p xs ys (some .gapX) := by
  cases xs <;> rfl

theorem scoreWalk_gapY_cons (sc : Scoring) (p : List Step)
    (x : Char) (xs : List Char) (ys : List Char) (prev : Option Step) :
    scoreWalk sc (.gapY :: p) (x :: xs) ys prev =
      gapYCost sc prev + scoreWalk sc p xs ys (some .gapY) := by
  cases ys <;> rfl

-- Binary left-biased maximum on the score component commutes with
-- prepending a step and shifting the score by a constant.
theorem maxOn_snd_shift (s : Step) (c : Int)
    (p1 : List Step) (v1 : Int) (q : List Step × Int) :
    maxOn (fun r : List Step × Int => r.2)
      (s :: p1, c + v1) (s :: q.1, c + q.2) =
      (s :: (maxOn (fun r : List Step × Int => r.2) (p1, v1) q).1,
       c + (maxOn (fun r : List Step × Int => r.2) (p1, v1) q).2) := by
  simp only [maxOn_eq_if]
  by_cases h : q.2 ≤ v1
  · simp [h, show c + q.2 ≤ c + v1 by omega]
  · have h2 : ¬ (c + q.2 ≤ c + v1) := by omega
    simp [h, h2]

/-- Selecting the earliest maximum commutes with mapping every candidate
through "prepend a step, add a constant to the score". -/
theorem maxOn?_map_shift (L : List (List Step))
    (σ : List Step → Int) (s : Step) (c : Int) :
    ((L.map fun p => (s :: p, c + σ p)).maxOn?
        fun item : List Step × Int => item.2) =
      ((L.map fun p => (p, σ p)).maxOn?
          fun item : List Step × Int => item.2).map
        fun r => (s :: r.1, c + r.2) := by
  induction L with
  | nil => simp
  | cons p L ih =>
      rw [List.map_cons, List.map_cons, List.maxOn?_cons, List.maxOn?_cons, ih]
      cases hL : ((L.map fun p => (p, σ p)).maxOn?
          fun item : List Step × Int => item.2) with
      | none => simp
      | some q =>
          simp only [Option.map_some, Option.elim_some]
          rw [maxOn_snd_shift]

-- ── The Bellman lemmas: the spec objective satisfies the recurrence ──

theorem bestAux_nil_nil (sc : Scoring) (prev : Option Step) :
    bestAux sc [] [] prev = some ([], 0) := by
  simp [bestAux, allPaths, scoreWalk]

theorem bestAux_nil_cons (sc : Scoring) (y : Char) (ys : List Char)
    (prev : Option Step) :
    bestAux sc [] (y :: ys) prev =
      (bestAux sc [] ys (some .gapX)).map
        fun r => (.gapX :: r.1, gapXCost sc prev + r.2) := by
  rw [bestAux, bestAux]
  simp only [allPaths]
  rw [List.map_map]
  have :
      ((fun p => (p, scoreWalk sc p [] (y :: ys) prev)) ∘ (Step.gapX :: ·)) =
        fun p => (Step.gapX :: p,
          gapXCost sc prev + scoreWalk sc p [] ys (some .gapX)) := by
    funext p
    simp [Function.comp, scoreWalk_gapX_cons]
  rw [this, maxOn?_map_shift]

theorem bestAux_cons_nil (sc : Scoring) (x : Char) (xs : List Char)
    (prev : Option Step) :
    bestAux sc (x :: xs) [] prev =
      (bestAux sc xs [] (some .gapY)).map
        fun r => (.gapY :: r.1, gapYCost sc prev + r.2) := by
  rw [bestAux, bestAux]
  simp only [allPaths]
  rw [List.map_map]
  have :
      ((fun p => (p, scoreWalk sc p (x :: xs) [] prev)) ∘ (Step.gapY :: ·)) =
        fun p => (Step.gapY :: p,
          gapYCost sc prev + scoreWalk sc p xs [] (some .gapY)) := by
    funext p
    simp [Function.comp, scoreWalk_gapY_cons]
  rw [this, maxOn?_map_shift]

theorem bestAux_cons_cons (sc : Scoring) (x : Char) (xs : List Char)
    (y : Char) (ys : List Char) (prev : Option Step) :
    bestAux sc (x :: xs) (y :: ys) prev =
      Option.merge (maxOn fun item : List Step × Int => item.2)
        (Option.merge (maxOn fun item : List Step × Int => item.2)
          ((bestAux sc xs ys (some .diag)).map
            fun r => (.diag :: r.1, diagCost sc x y + r.2))
          ((bestAux sc (x :: xs) ys (some .gapX)).map
            fun r => (.gapX :: r.1, gapXCost sc prev + r.2)))
        ((bestAux sc xs (y :: ys) (some .gapY)).map
          fun r => (.gapY :: r.1, gapYCost sc prev + r.2)) := by
  rw [bestAux]
  simp only [allPaths]
  rw [List.map_append, List.map_append, List.maxOn?_append, List.maxOn?_append]
  rw [List.map_map, List.map_map, List.map_map]
  have hdiag :
      ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
          (Step.diag :: ·)) =
        fun p => (Step.diag :: p,
          diagCost sc x y + scoreWalk sc p xs ys (some .diag)) := by
    funext p
    simp [Function.comp, scoreWalk_diag_cons]
  have hgapX :
      ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
          (Step.gapX :: ·)) =
        fun p => (Step.gapX :: p,
          gapXCost sc prev + scoreWalk sc p (x :: xs) ys (some .gapX)) := by
    funext p
    simp [Function.comp, scoreWalk_gapX_cons]
  have hgapY :
      ((fun p => (p, scoreWalk sc p (x :: xs) (y :: ys) prev)) ∘
          (Step.gapY :: ·)) =
        fun p => (Step.gapY :: p,
          gapYCost sc prev + scoreWalk sc p xs (y :: ys) (some .gapY)) := by
    funext p
    simp [Function.comp, scoreWalk_gapY_cons]
  rw [hdiag, hgapX, hgapY,
    maxOn?_map_shift, maxOn?_map_shift, maxOn?_map_shift]
  rfl

-- ══════════════════════════════════════════════════════════════════
-- ALGORITHM 1: the direct Bellman recursion (exponential time, but no
-- candidate lists are ever built — pure structural recursion).
-- ══════════════════════════════════════════════════════════════════

def bellmanAux (sc : Scoring) : List Char → List Char → Option Step →
    List Step × Int
  | [], [], _ => ([], 0)
  | [], _ :: ys, prev =>
      let r := bellmanAux sc [] ys (some .gapX)
      (.gapX :: r.1, gapXCost sc prev + r.2)
  | _ :: xs, [], prev =>
      let r := bellmanAux sc xs [] (some .gapY)
      (.gapY :: r.1, gapYCost sc prev + r.2)
  | x :: xs, y :: ys, prev =>
      let d := bellmanAux sc xs ys (some .diag)
      let gx := bellmanAux sc (x :: xs) ys (some .gapX)
      let gy := bellmanAux sc xs (y :: ys) (some .gapY)
      maxOn (fun item : List Step × Int => item.2)
        (maxOn (fun item : List Step × Int => item.2)
          (.diag :: d.1, diagCost sc x y + d.2)
          (.gapX :: gx.1, gapXCost sc prev + gx.2))
        (.gapY :: gy.1, gapYCost sc prev + gy.2)

def bellmanAlign (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  some (bellmanAux sc xs ys none)

theorem bestAux_eq_bellmanAux (sc : Scoring) (xs ys : List Char)
    (prev : Option Step) :
    bestAux sc xs ys prev = some (bellmanAux sc xs ys prev) := by
  induction xs, ys, prev using bellmanAux.induct sc with
  | case1 prev =>
      rw [bestAux_nil_nil]
      simp [bellmanAux]
  | case2 y ys prev ih =>
      rw [bestAux_nil_cons, ih]
      simp [bellmanAux]
  | case3 x xs prev ih =>
      rw [bestAux_cons_nil, ih]
      simp [bellmanAux]
  | case4 x xs y ys prev ihDiag ihGapX ihGapY =>
      rw [bestAux_cons_cons, ihDiag, ihGapX, ihGapY]
      simp [bellmanAux]

/-- Frozen-contract equality for the Bellman recursion. -/
theorem bellmanAlign_equals_getBestAlignment
    (sc : Scoring) (xs ys : List Char) :
    bellmanAlign sc xs ys = getBestAlignment sc xs ys := by
  rw [getBestAlignment_eq_bestAux, bestAux_eq_bellmanAux]
  rfl

-- ══════════════════════════════════════════════════════════════════
-- ALGORITHM 2: Gotoh's three-state row tabulation, O(m·n) time.
-- One cell per (x-suffix, y-suffix) pair holding the best alignment
-- for each of the three relevant previous-step classes.  Paths are
-- shared cons-lists, so extending a cell costs O(1).
-- ══════════════════════════════════════════════════════════════════

structure Cell where
  neutral   : List Step × Int  -- previous step none or diag
  afterGapX : List Step × Int  -- previous step gapX
  afterGapY : List Step × Int  -- previous step gapY

/-- The value every table cell is supposed to hold (proof-side only). -/
def specCell (sc : Scoring) (xs ys : List Char) : Cell :=
  { neutral   := bellmanAux sc xs ys none
  , afterGapX := bellmanAux sc xs ys (some .gapX)
  , afterGapY := bellmanAux sc xs ys (some .gapY) }

/-- The previous step influences only the first column's gap-opening
charge, and a previous diagonal opens gaps exactly like no previous
step at all. -/
theorem bellmanAux_diag_eq_none (sc : Scoring) (xs ys : List Char) :
    bellmanAux sc xs ys (some .diag) = bellmanAux sc xs ys none := by
  cases xs <;> cases ys <;> simp [bellmanAux, gapXCost, gapYCost]

def mkCellGapXOnly (sc : Scoring) (next : Cell) : Cell :=
  let r := next.afterGapX
  let oe := sc.gapOpen + sc.gapExtend
  { neutral   := (.gapX :: r.1, oe + r.2)
  , afterGapX := (.gapX :: r.1, sc.gapExtend + r.2)
  , afterGapY := (.gapX :: r.1, oe + r.2) }

def mkCellGapYOnly (sc : Scoring) (next : Cell) : Cell :=
  let r := next.afterGapY
  let oe := sc.gapOpen + sc.gapExtend
  { neutral   := (.gapY :: r.1, oe + r.2)
  , afterGapX := (.gapY :: r.1, oe + r.2)
  , afterGapY := (.gapY :: r.1, sc.gapExtend + r.2) }

/-- The general cell.  `nj` is the cell one row down in the same
column (gap-in-y target), `nj1` one row down and one column right
(diagonal target), `cur1` the current row one column right
(gap-in-x target). -/
def mkCellMain (sc : Scoring) (x y : Char) (nj nj1 cur1 : Cell) : Cell :=
  let d := nj1.neutral
  let dCand : List Step × Int := (.diag :: d.1, diagCost sc x y + d.2)
  let gx := cur1.afterGapX
  let gy := nj.afterGapY
  let pick (gxCost gyCost : Int) : List Step × Int :=
    maxOn (fun item : List Step × Int => item.2)
      (maxOn (fun item : List Step × Int => item.2) dCand
        (.gapX :: gx.1, gxCost + gx.2))
      (.gapY :: gy.1, gyCost + gy.2)
  let oe := sc.gapOpen + sc.gapExtend
  { neutral   := pick oe oe
  , afterGapX := pick sc.gapExtend oe
  , afterGapY := pick oe sc.gapExtend }

theorem mkCellGapXOnly_spec (sc : Scoring) (y : Char) (ys : List Char) :
    mkCellGapXOnly sc (specCell sc [] ys) = specCell sc [] (y :: ys) := by
  simp [specCell, mkCellGapXOnly, bellmanAux, gapXCost]

theorem mkCellGapYOnly_spec (sc : Scoring) (x : Char) (xs : List Char) :
    mkCellGapYOnly sc (specCell sc xs []) = specCell sc (x :: xs) [] := by
  simp [specCell, mkCellGapYOnly, bellmanAux, gapYCost]

theorem mkCellMain_spec (sc : Scoring) (x y : Char) (xs ys : List Char) :
    mkCellMain sc x y (specCell sc xs (y :: ys)) (specCell sc xs ys)
        (specCell sc (x :: xs) ys) =
      specCell sc (x :: xs) (y :: ys) := by
  simp [specCell, mkCellMain, bellmanAux, gapXCost, gapYCost,
    bellmanAux_diag_eq_none]

/-- The row every implementation must produce for one x-suffix: the
cell for each y-suffix, longest suffix first (proof-side only). -/
def specRow (sc : Scoring) (xs : List Char) : List Char → List Cell
  | [] => [specCell sc xs []]
  | y :: ys => specCell sc xs (y :: ys) :: specRow sc xs ys

/-- The junk cell handed out when an unreachable row shape is
inspected; the invariant proofs show it is never consulted. -/
def cellDefault : Cell :=
  { neutral := ([], 0), afterGapX := ([], 0), afterGapY := ([], 0) }

def cellHead (row : List Cell) : Cell :=
  row.headD cellDefault

theorem cellHead_cons (c : Cell) (rest : List Cell) :
    cellHead (c :: rest) = c :=
  rfl

theorem cellHead_specRow (sc : Scoring) (xs ys : List Char) :
    cellHead (specRow sc xs ys) = specCell sc xs ys := by
  cases ys <;> simp [specRow, cellHead]

def lastRow (sc : Scoring) : List Char → List Cell
  | [] => [cellDefault]
  | _ :: ys =>
      let row := lastRow sc ys
      mkCellGapXOnly sc (cellHead row) :: row

def rowUp (sc : Scoring) (x : Char) : List Char → List Cell → List Cell
  | [], next => [mkCellGapYOnly sc (cellHead next)]
  | y :: ys, next =>
      let nrest := next.tail
      let cur := rowUp sc x ys nrest
      mkCellMain sc x y (cellHead next) (cellHead nrest) (cellHead cur)
        :: cur

def gotohTable (sc : Scoring) : List Char → List Char → List Cell
  | [], ys => lastRow sc ys
  | x :: xs, ys => rowUp sc x ys (gotohTable sc xs ys)

def gotohAlign (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  some (cellHead (gotohTable sc xs ys)).neutral

theorem lastRow_eq (sc : Scoring) (ys : List Char) :
    lastRow sc ys = specRow sc [] ys := by
  induction ys with
  | nil => simp [lastRow, specRow, specCell, bellmanAux, cellDefault]
  | cons y ys ih =>
      rw [lastRow, ih]
      simp only [cellHead_specRow]
      rw [mkCellGapXOnly_spec sc y ys]
      simp [specRow]

theorem rowUp_eq (sc : Scoring) (x : Char) (xs : List Char)
    (ys : List Char) :
    rowUp sc x ys (specRow sc xs ys) = specRow sc (x :: xs) ys := by
  induction ys with
  | nil =>
      simp only [specRow, rowUp, cellHead_cons]
      rw [mkCellGapYOnly_spec]
  | cons y ys ih =>
      rw [rowUp]
      simp only [specRow, List.tail_cons, ih, cellHead_specRow,
        cellHead_cons]
      rw [mkCellMain_spec]

theorem gotohTable_eq (sc : Scoring) (xs ys : List Char) :
    gotohTable sc xs ys = specRow sc xs ys := by
  induction xs with
  | nil => exact lastRow_eq sc ys
  | cons x xs ih =>
      rw [gotohTable, ih, rowUp_eq]

/-- Frozen-contract equality for the Gotoh row tabulation. -/
theorem gotohAlign_equals_getBestAlignment
    (sc : Scoring) (xs ys : List Char) :
    gotohAlign sc xs ys = getBestAlignment sc xs ys := by
  rw [getBestAlignment_eq_bestAux, bestAux_eq_bellmanAux, gotohAlign,
    gotohTable_eq]
  cases ys <;> simp [specRow, specCell, cellHead_cons]

-- ══════════════════════════════════════════════════════════════════
-- ALGORITHM 3: fused Gotoh.  Same table, but each cell compares raw
-- scores first and only allocates the winning candidate pair; the
-- diagonal candidate is built once and shared across the three
-- previous-step classes.  Same asymptotics, smaller constants.
-- ══════════════════════════════════════════════════════════════════

/-- The fused choice: compare raw scores first, allocate only the
winning pair.  Provably identical to the left-biased `maxOn` chain. -/
private theorem fusedPick_eq (dTail gxTail gyTail : List Step)
    (ds gxs gys : Int) :
    (if gxs ≤ ds then
       if gys ≤ ds then (Step.diag :: dTail, ds)
       else (Step.gapY :: gyTail, gys)
     else if gys ≤ gxs then (Step.gapX :: gxTail, gxs)
     else (Step.gapY :: gyTail, gys)) =
    maxOn (fun item : List Step × Int => item.2)
      (maxOn (fun item : List Step × Int => item.2)
        (Step.diag :: dTail, ds) (Step.gapX :: gxTail, gxs))
      (Step.gapY :: gyTail, gys) := by
  simp only [maxOn_eq_if]
  by_cases h1 : gxs ≤ ds <;> simp [h1]

def mkCellMainFused (sc : Scoring) (x y : Char) (nj nj1 cur1 : Cell) :
    Cell :=
  let d := nj1.neutral
  let ds := diagCost sc x y + d.2
  let gx := cur1.afterGapX
  let gy := nj.afterGapY
  let oe := sc.gapOpen + sc.gapExtend
  let dPair : List Step × Int := (.diag :: d.1, ds)
  let pick (gxs gys : Int) : List Step × Int :=
    if gxs ≤ ds then
      if gys ≤ ds then dPair else (.gapY :: gy.1, gys)
    else
      if gys ≤ gxs then (.gapX :: gx.1, gxs) else (.gapY :: gy.1, gys)
  { neutral   := pick (oe + gx.2) (oe + gy.2)
  , afterGapX := pick (sc.gapExtend + gx.2) (oe + gy.2)
  , afterGapY := pick (oe + gx.2) (sc.gapExtend + gy.2) }

theorem mkCellMainFused_eq (sc : Scoring) (x y : Char)
    (nj nj1 cur1 : Cell) :
    mkCellMainFused sc x y nj nj1 cur1 = mkCellMain sc x y nj nj1 cur1 := by
  simp only [mkCellMainFused, mkCellMain, fusedPick_eq]

def rowUpFused (sc : Scoring) (x : Char) :
    List Char → List Cell → List Cell
  | [], next => [mkCellGapYOnly sc (cellHead next)]
  | y :: ys, next =>
      let nrest := next.tail
      let cur := rowUpFused sc x ys nrest
      mkCellMainFused sc x y (cellHead next) (cellHead nrest)
        (cellHead cur) :: cur

def gotohFusedTable (sc : Scoring) : List Char → List Char → List Cell
  | [], ys => lastRow sc ys
  | x :: xs, ys => rowUpFused sc x ys (gotohFusedTable sc xs ys)

def gotohFusedAlign (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  some (cellHead (gotohFusedTable sc xs ys)).neutral

theorem rowUpFused_eq_rowUp (sc : Scoring) (x : Char)
    (ys : List Char) (next : List Cell) :
    rowUpFused sc x ys next = rowUp sc x ys next := by
  induction ys generalizing next with
  | nil => rfl
  | cons y ys ih =>
      rw [rowUpFused, rowUp, ih, mkCellMainFused_eq]

theorem gotohFusedTable_eq (sc : Scoring) (xs ys : List Char) :
    gotohFusedTable sc xs ys = gotohTable sc xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [gotohFusedTable, gotohTable, ih, rowUpFused_eq_rowUp]

/-- Frozen-contract equality for the fused Gotoh tabulation. -/
theorem gotohFusedAlign_equals_getBestAlignment
    (sc : Scoring) (xs ys : List Char) :
    gotohFusedAlign sc xs ys = getBestAlignment sc xs ys := by
  rw [← gotohAlign_equals_getBestAlignment, gotohFusedAlign, gotohAlign,
    gotohFusedTable_eq]

-- ── Executable witnesses: all three algorithms reproduce the spec's
--    own demo answers (checked at compile time). ──

#guard bellmanAlign demoScoring ['A','B','C'] ['A','B','B','C']
  == getBestAlignment demoScoring ['A','B','C'] ['A','B','B','C']
#guard gotohAlign demoScoring ['A','B','C'] ['A','B','B','C']
  == getBestAlignment demoScoring ['A','B','C'] ['A','B','B','C']
#guard gotohFusedAlign demoScoring ['A','B','C'] ['A','B','B','C']
  == getBestAlignment demoScoring ['A','B','C'] ['A','B','B','C']
#guard gotohAlign demoScoring ['A','B','B','A'] ['A','A']
  == some ([.diag, .gapY, .gapY, .diag], -1)
#guard gotohFusedAlign demoScoring [] [] == some ([], 0)

end AlignmentSpec
