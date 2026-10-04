import AlignmentExchange

/-!
TRUE WFA: furthest-reaching wavefronts over penalty levels.

The algorithm runs forward over PREFIXES in the doubled penalty model
of `penalty_transform` (match 0, mismatch `px = 2(M−X)`, gap extension
`pe = M−2E`, gap opening `po = pe − 2O`).  State per penalty level p:
three "fronts", one `Option` cell per diagonal `k = j − i ∈ [−m, n]`
(list index `t = k + m`):

  * `xf` — furthest cell whose prefix walk ends in a gap-in-x column,
  * `yf` — ends in a gap-in-y column,
  * `mf` — furthest cell reachable in ANY ending state (the `min` of
    the three classical M/I/D penalty tables), closed under free
    diagonal extension along matching characters — the greedy step
    justified by `bellmanAux_match_extend`.

A cell carries its offset (consumed xs-prefix length), the two
remaining suffixes (so extension is head-comparison on shared list
tails, O(1) per matched character), and the reversed walk so far
(cons-shared).  Termination is by fuel; running out of fuel — or an
unreasonable scoring, checked at run time by `wfaGateB` — falls back
to the proven `gotohFusedAlign`, so exported theorems can stay free of
hypotheses.
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- Penalties and the runtime gate
-- ══════════════════════════════════════════════════════════════════

/-- Doubled mismatch penalty. -/
def wfaPx (sc : Scoring) : Int := 2 * (sc.matchScore - sc.mismatchScore)

/-- Doubled gap-extension penalty. -/
def wfaPe (sc : Scoring) : Int := sc.matchScore - 2 * sc.gapExtend

/-- Doubled gap-opening penalty (open + first extension). -/
def wfaPo (sc : Scoring) : Int := wfaPe sc - 2 * sc.gapOpen

/-- The fast path additionally needs strictly positive mismatch and
extension penalties, so every wavefront update references strictly
earlier levels. -/
def wfaGateB (sc : Scoring) : Bool :=
  reasonableB sc && decide (1 ≤ wfaPx sc) && decide (1 ≤ wfaPe sc)

-- ══════════════════════════════════════════════════════════════════
-- Cells, fronts, levels
-- ══════════════════════════════════════════════════════════════════

/-- One furthest-reaching point: `off`/`joff` = consumed prefix
lengths of xs/ys, the remaining suffixes, and the reversed prefix
walk. -/
structure WCell where
  off   : Nat
  joff  : Nat
  xsRem : List Char
  ysRem : List Char
  walk  : List Step
deriving Repr

/-- A front: one optional cell per diagonal, index `t = k + m`. -/
abbrev WFront := List (Option WCell)

structure WLevel where
  mf : WFront
  xf : WFront
  yf : WFront
deriving Repr

/-- Left-biased choice of the further cell. -/
def betterCell : Option WCell → Option WCell → Option WCell
  | none, b => b
  | some a, none => some a
  | some a, some b => if b.off ≤ a.off then some a else some b

/-- Leading run of `s`, the first different step, and the remainder —
on the REVERSED walk, so this is the walk's trailing run. -/
def splitRun (s : Step) : List Step → Nat × Option Step × List Step
  | [] => (0, none, [])
  | c :: rest =>
      if c = s then
        ((splitRun s rest).1 + 1, (splitRun s rest).2)
      else (0, some c, rest)

/-- Boundary surgery on a reversed walk: un-consume exactly one x and
one y (remove the trailing diagonal, or the last x/y-consumer plus
one trailing gap column).  Never increases the penalty — each removed
column has nonnegative penalty and run merges only help. -/
def demoteWalk : List Step → Option (List Step)
  | [] => none
  | .diag :: rest => some rest
  | .gapX :: rest =>
      match splitRun .gapX (.gapX :: rest) with
      | (a, some .diag, t) => some (List.replicate a .gapX ++ t)
      | (a, some .gapY, t) => some (List.replicate (a - 1) .gapX ++ t)
      | _ => none
  | .gapY :: rest =>
      match splitRun .gapY (.gapY :: rest) with
      | (b, some .diag, t) => some (List.replicate b .gapY ++ t)
      | (b, some .gapX, t) => some (List.replicate (b - 1) .gapY ++ t)
      | _ => none

/-- Step one cell back along its diagonal (used only when a cell is
pinned at a string end and cannot take the requested step). -/
def demoteCell (xs ys : List Char) (c : WCell) : Option WCell :=
  match c.off, c.joff, demoteWalk c.walk with
  | i + 1, j + 1, some w =>
      some ⟨i, j, xs.drop i, ys.drop j, w⟩
  | _, _, _ => none

/-- Consume one y with a gap-in-x column (stays on offset, moves one
diagonal up). -/
def pushGapX (c : WCell) : Option WCell :=
  match c.ysRem with
  | _ :: yr => some ⟨c.off, c.joff + 1, c.xsRem, yr, .gapX :: c.walk⟩
  | [] => none

/-- Consume one x with a gap-in-y column. -/
def pushGapY (c : WCell) : Option WCell :=
  match c.xsRem with
  | _ :: xr => some ⟨c.off + 1, c.joff, xr, c.ysRem, .gapY :: c.walk⟩
  | [] => none

/-- Consume one character from each string with a diagonal column
(match or mismatch — callers charge the mismatch penalty). -/
def pushDiag (c : WCell) : Option WCell :=
  match c.xsRem, c.ysRem with
  | _ :: xr, _ :: yr =>
      some ⟨c.off + 1, c.joff + 1, xr, yr, .diag :: c.walk⟩
  | _, _ => none

/-- A push that falls back to one boundary demotion when pinned. -/
def stepWith (push : WCell → Option WCell) (xs ys : List Char) :
    Option WCell → Option WCell
  | some c =>
      match push c with
      | some r => some r
      | none => (demoteCell xs ys c).bind push
  | none => none

/-- Free extension: while the suffix heads match, take diagonals. -/
def extendGo (i j : Nat) (w : List Step) :
    List Char → List Char → WCell
  | x :: xr, y :: yr =>
      if x = y then extendGo (i + 1) (j + 1) (.diag :: w) xr yr
      else ⟨i, j, x :: xr, y :: yr, w⟩
  | xr, yr => ⟨i, j, xr, yr, w⟩

def extendCell (c : WCell) : WCell :=
  extendGo c.off c.joff c.walk c.xsRem c.ysRem

/-- Shift one diagonal up (for gap-in-x updates: the predecessor of
diagonal `t` sits on `t − 1`). -/
def shiftUp (f : WFront) : WFront := none :: f.dropLast

/-- Shift one diagonal down (for gap-in-y updates). -/
def shiftDown (f : WFront) : WFront := f.drop 1 ++ [none]

def emptyFront (len : Nat) : WFront := List.replicate len none

def frontAt (len : Nat) (hist : List WLevel) (delta : Nat)
    (sel : WLevel → WFront) : WFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => emptyFront len

/-- One wavefront step: build level `p` from the history
(`hist.head?` is level `p − 1`). -/
def nextLevel (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List WLevel) : WLevel :=
  let xf := List.zipWith betterCell
    (shiftUp ((frontAt len hist pe (·.xf)).map (stepWith pushGapX xs ys)))
    (shiftUp ((frontAt len hist po (·.mf)).map (stepWith pushGapX xs ys)))
  let yf := List.zipWith betterCell
    (shiftDown ((frontAt len hist pe (·.yf)).map (stepWith pushGapY xs ys)))
    (shiftDown ((frontAt len hist po (·.mf)).map (stepWith pushGapY xs ys)))
  let base := List.zipWith betterCell
    (List.zipWith betterCell
      ((frontAt len hist px (·.mf)).map (stepWith pushDiag xs ys)) xf) yf
  ⟨base.map (Option.map extendCell), xf, yf⟩

/-- Level 0: the empty prefix at cell (0,0), diagonal 0, extended. -/
def seedLevel (m len : Nat) (xs ys : List Char) : WLevel :=
  ⟨(emptyFront len).set m (some (extendCell ⟨0, 0, xs, ys, []⟩)),
   emptyFront len, emptyFront len⟩

/-- The finished cell, if the corner diagonal's furthest point has
consumed both strings. -/
def cornerOf (n : Nat) (lv : WLevel) : Option WCell :=
  match lv.mf[n]? with
  | some (some c) =>
      match c.xsRem, c.ysRem with
      | [], [] => some c
      | _, _ => none
  | _ => none

def wfaLoop (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List WLevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevel xs ys len pe po px hist
      match cornerOf n lv with
      | some c => some c
      | none =>
          wfaLoop xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

-- ══════════════════════════════════════════════════════════════════
-- Banded fronts: store only the active window of diagonals
-- ══════════════════════════════════════════════════════════════════

/-- Pad (or truncate) to exactly `len` optional cells. -/
def padTo (len : Nat) (l : List (Option WCell)) : WFront :=
  l.take len ++ List.replicate (len - l.length) none

/-- A banded front: `pad` empty diagonals, then the stored band.  It
denotes (`tden`) the full-width front `padTo len (replicate pad none
++ body)`; anything a band operation parks beyond index `len − 1` is
dropped by the `padTo` truncation, exactly as the full-width
operations drop it off the end of the list. -/
structure TFront where
  pad  : Nat
  body : List (Option WCell)
deriving Repr

/-- The full-width front a banded front denotes. -/
def tden (len : Nat) (f : TFront) : WFront :=
  padTo len (List.replicate f.pad none ++ f.body)

/-- `zipWith betterCell` extended with implicit trailing `none`s. -/
def zipExt : List (Option WCell) → List (Option WCell) →
    List (Option WCell)
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => betterCell x y :: zipExt a b

/-- Banded `List.zipWith betterCell`: align the bands, then zip.  An
empty band denotes the all-`none` front, so the other side wins
outright — without this short-circuit the general case would
materialize the other band's padding. -/
def zipT : TFront → TFront → TFront
  | ⟨_, []⟩, g => g
  | f, ⟨_, []⟩ => f
  | ⟨p, a⟩, ⟨q, b⟩ =>
      let lo := min p q
      ⟨lo, zipExt (List.replicate (p - lo) none ++ a)
        (List.replicate (q - lo) none ++ b)⟩

/-- Banded `shiftUp` — constant time. -/
def shiftUpT (f : TFront) : TFront := ⟨f.pad + 1, f.body⟩

/-- Banded `shiftDown`; the `take` keeps a cell parked beyond the
window from re-entering it. -/
def shiftDownT (len : Nat) (f : TFront) : TFront :=
  match f.pad with
  | p + 1 => ⟨p, f.body.take (len - (p + 1))⟩
  | 0 => ⟨0, (f.body.drop 1).take (len - 1)⟩

/-- Map over the band (for functions sending `none` to `none`). -/
def mapT (g : Option WCell → Option WCell) (f : TFront) : TFront :=
  ⟨f.pad, f.body.map g⟩

structure TLevel where
  mf : TFront
  xf : TFront
  yf : TFront
deriving Repr

/-- The full-width level a banded level denotes. -/
def tdenLevel (len : Nat) (lv : TLevel) : WLevel :=
  ⟨tden len lv.mf, tden len lv.xf, tden len lv.yf⟩

def frontAtT (hist : List TLevel) (delta : Nat)
    (sel : TLevel → TFront) : TFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => ⟨0, []⟩

/-- One banded wavefront step — denotes `nextLevel`
(`nextLevelT_den`). -/
def nextLevelT (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List TLevel) : TLevel :=
  let xf := zipT
    (shiftUpT (mapT (stepWith pushGapX xs ys) (frontAtT hist pe (·.xf))))
    (shiftUpT (mapT (stepWith pushGapX xs ys) (frontAtT hist po (·.mf))))
  let yf := zipT
    (shiftDownT len
      (mapT (stepWith pushGapY xs ys) (frontAtT hist pe (·.yf))))
    (shiftDownT len
      (mapT (stepWith pushGapY xs ys) (frontAtT hist po (·.mf))))
  let base := zipT (zipT
    (mapT (stepWith pushDiag xs ys) (frontAtT hist px (·.mf))) xf) yf
  ⟨mapT (Option.map extendCell) base, xf, yf⟩

def seedLevelT (m : Nat) (xs ys : List Char) : TLevel :=
  ⟨⟨m, [some (extendCell ⟨0, 0, xs, ys, []⟩)]⟩, ⟨0, []⟩, ⟨0, []⟩⟩

/-- The cell the band holds at absolute diagonal index `n`. -/
def tgetT (f : TFront) (n : Nat) : Option WCell :=
  if n < f.pad then none else (f.body[n - f.pad]?).getD none

def cornerOfT (n : Nat) (lv : TLevel) : Option WCell :=
  match tgetT lv.mf n with
  | some c =>
      match c.xsRem, c.ysRem with
      | [], [] => some c
      | _, _ => none
  | none => none

def wfaLoopT (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List TLevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevelT xs ys len pe po px hist
      match cornerOfT n lv with
      | some c => some c
      | none =>
          wfaLoopT xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

/-- The banded wavefront run — equal to `wfaRun` (`wfaRunT_eq`), but
each level costs O(active band) instead of O(m + n). -/
def wfaRunT (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevelT m xs ys
  let result :=
    match cornerOfT n lv0 with
    | some c => some c
    | none => wfaLoopT xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

-- ══════════════════════════════════════════════════════════════════
-- Array-backed bands: contiguous storage for the active window
-- ══════════════════════════════════════════════════════════════════

structure AFront where
  pad  : Nat
  body : Array (Option WCell)
deriving Repr

/-- The banded (list) front an array-backed front denotes. -/
def aden (f : AFront) : TFront := ⟨f.pad, f.body.toList⟩

/-- `zipExt` on arrays: zip the overlap, append the longer tail. -/
def azipExt (a b : Array (Option WCell)) : Array (Option WCell) :=
  if a.size ≤ b.size then
    Array.zipWith betterCell a b ++ b.extract a.size b.size
  else
    Array.zipWith betterCell a b ++ a.extract b.size a.size

def zipA (f g : AFront) : AFront :=
  if f.body.isEmpty then g
  else if g.body.isEmpty then f
  else
    let lo := min f.pad g.pad
    ⟨lo, azipExt (Array.replicate (f.pad - lo) none ++ f.body)
      (Array.replicate (g.pad - lo) none ++ g.body)⟩

def shiftUpA (f : AFront) : AFront := ⟨f.pad + 1, f.body⟩

def shiftDownA (len : Nat) (f : AFront) : AFront :=
  match f.pad with
  | p + 1 => ⟨p, f.body.extract 0 (len - (p + 1))⟩
  | 0 => ⟨0, f.body.extract 1 (1 + (len - 1))⟩

def mapA (g : Option WCell → Option WCell) (f : AFront) : AFront :=
  ⟨f.pad, f.body.map g⟩

structure ALevel where
  mf : AFront
  xf : AFront
  yf : AFront
deriving Repr

def adenLevel (lv : ALevel) : TLevel :=
  ⟨aden lv.mf, aden lv.xf, aden lv.yf⟩

def frontAtA (hist : List ALevel) (delta : Nat)
    (sel : ALevel → AFront) : AFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => ⟨0, #[]⟩

/-- One array-banded wavefront step — denotes `nextLevelT`
(`nextLevelA_den`). -/
def nextLevelA (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List ALevel) : ALevel :=
  let xf := zipA
    (shiftUpA (mapA (stepWith pushGapX xs ys) (frontAtA hist pe (·.xf))))
    (shiftUpA (mapA (stepWith pushGapX xs ys) (frontAtA hist po (·.mf))))
  let yf := zipA
    (shiftDownA len
      (mapA (stepWith pushGapY xs ys) (frontAtA hist pe (·.yf))))
    (shiftDownA len
      (mapA (stepWith pushGapY xs ys) (frontAtA hist po (·.mf))))
  let base := zipA (zipA
    (mapA (stepWith pushDiag xs ys) (frontAtA hist px (·.mf))) xf) yf
  ⟨mapA (Option.map extendCell) base, xf, yf⟩

def seedLevelA (m : Nat) (xs ys : List Char) : ALevel :=
  ⟨⟨m, #[some (extendCell ⟨0, 0, xs, ys, []⟩)]⟩, ⟨0, #[]⟩, ⟨0, #[]⟩⟩

/-- The cell the array band holds at absolute diagonal index `n` —
constant time. -/
def tgetA (f : AFront) (n : Nat) : Option WCell :=
  if n < f.pad then none else (f.body[n - f.pad]?).getD none

def cornerOfA (n : Nat) (lv : ALevel) : Option WCell :=
  match tgetA lv.mf n with
  | some c =>
      match c.xsRem, c.ysRem with
      | [], [] => some c
      | _, _ => none
  | none => none

def wfaLoopA (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List ALevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevelA xs ys len pe po px hist
      match cornerOfA n lv with
      | some c => some c
      | none =>
          wfaLoopA xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

/-- The array-banded wavefront run — equal to `wfaRunT` and so to
`wfaRun` (`wfaRunA_eq`). -/
def wfaRunA (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevelA m xs ys
  let result :=
    match cornerOfA n lv0 with
    | some c => some c
    | none => wfaLoopA xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

/-- The wavefront run: `none` means fuel ran out (never happens with
the chosen fuel, but the fallback keeps the contract airtight without
a fuel lemma).  This full-width version is the proof model; the
executed fast path is the denote-equal `wfaRunT`. -/
def wfaRun (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevel m len xs ys
  let result :=
    match cornerOf n lv0 with
    | some c => some c
    | none => wfaLoop xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

/-- TRUE WFA with runtime gate and proven fallback.  The executed
fast path is the banded `wfaRunT`; every theorem below reaches it
through `wfaRunT_eq`.  (An array-backed variant `wfaRunA` is proven
equal too — `wfaRunA_eq` — but measured performance-neutral: the s²
cost is per-cell work, not list-node overhead, so the list bands
stay in the executed path.) -/
def wfaAlign (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunT sc xs ys with
    | some r => some r
    | none => gotohFusedAlign sc xs ys
  else gotohFusedAlign sc xs ys

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 0: banded fronts denote full-width fronts
-- ══════════════════════════════════════════════════════════════════

theorem padTo_zero (l : List (Option WCell)) : padTo 0 l = [] := by
  simp [padTo]

theorem padTo_nil (len : Nat) :
    padTo len [] = List.replicate len none := by
  simp [padTo]

theorem padTo_succ_cons (len : Nat) (x : Option WCell)
    (l : List (Option WCell)) :
    padTo (len + 1) (x :: l) = x :: padTo len l := by
  simp [padTo, List.take_succ_cons, Nat.succ_sub_succ]

theorem padTo_succ_nil (len : Nat) :
    padTo (len + 1) [] = none :: padTo len [] := by
  simp [padTo_nil, List.replicate_succ]

theorem padTo_length (len : Nat) (l : List (Option WCell)) :
    (padTo len l).length = len := by
  induction len generalizing l with
  | zero => simp [padTo_zero]
  | succ len ih =>
      cases l with
      | nil => rw [padTo_succ_nil]; simp [ih]
      | cons x l => rw [padTo_succ_cons]; simp [ih]

theorem padTo_take (len : Nat) :
    ∀ (k : Nat) (l : List (Option WCell)), k ≤ len →
      (padTo len l).take k = padTo k l := by
  induction len with
  | zero =>
      intro k l hk
      have : k = 0 := Nat.le_zero.mp hk
      subst this
      simp [padTo_zero]
  | succ len ih =>
      intro k l hk
      cases k with
      | zero => simp [padTo_zero]
      | succ k =>
          cases l with
          | nil =>
              rw [padTo_succ_nil, padTo_succ_nil, List.take_succ_cons,
                ih k [] (Nat.le_of_succ_le_succ hk)]
          | cons x l =>
              rw [padTo_succ_cons, padTo_succ_cons, List.take_succ_cons,
                ih k l (Nat.le_of_succ_le_succ hk)]

theorem dropLast_cons_cons (x y : Option WCell)
    (l : List (Option WCell)) :
    (x :: y :: l).dropLast = x :: (y :: l).dropLast := by
  simp [List.dropLast]

theorem padTo_dropLast (len : Nat) :
    ∀ l : List (Option WCell),
      (padTo (len + 1) l).dropLast = padTo len l := by
  induction len with
  | zero =>
      intro l
      cases l with
      | nil => rw [padTo_succ_nil, padTo_zero]; simp
      | cons x l => rw [padTo_succ_cons, padTo_zero]; simp [padTo_zero]
  | succ len ih =>
      intro l
      cases l with
      | nil =>
          rw [padTo_succ_nil, padTo_succ_nil, dropLast_cons_cons,
            ← padTo_succ_nil, ih [], padTo_succ_nil]
      | cons x l =>
          rw [padTo_succ_cons, padTo_succ_cons]
          cases hl : padTo (len + 1) l with
          | nil =>
              have hlen := padTo_length (len + 1) l
              rw [hl] at hlen
              simp at hlen
          | cons y t =>
              rw [dropLast_cons_cons, ← hl, ih l]

theorem padTo_drop_one (len : Nat) (l : List (Option WCell)) :
    (padTo (len + 1) l).drop 1 = padTo len (l.drop 1) := by
  cases l with
  | nil => rw [padTo_succ_nil]; rfl
  | cons x l => rw [padTo_succ_cons]; rfl

theorem padTo_snoc_none (len : Nat) :
    ∀ l : List (Option WCell),
      padTo len l ++ [none] = padTo (len + 1) (l.take len) := by
  induction len with
  | zero => intro l; simp [padTo_zero, padTo_succ_nil]
  | succ len ih =>
      intro l
      cases l with
      | nil =>
          rw [padTo_succ_nil, List.cons_append, ih []]
          simp [padTo_succ_nil]
      | cons x l =>
          rw [padTo_succ_cons, List.cons_append, ih l,
            List.take_succ_cons, padTo_succ_cons]

theorem map_padTo (g : Option WCell → Option WCell)
    (hg : g none = none) (len : Nat) :
    ∀ l : List (Option WCell),
      (padTo len l).map g = padTo len (l.map g) := by
  induction len with
  | zero => intro l; simp [padTo_zero]
  | succ len ih =>
      intro l
      cases l with
      | nil => rw [padTo_succ_nil]; simp [hg, ih [], padTo_succ_nil]
      | cons x l =>
          rw [padTo_succ_cons, List.map_cons, ih l, List.map_cons,
            padTo_succ_cons]

theorem betterCell_none_right (x : Option WCell) :
    betterCell x none = x := by
  cases x <;> rfl

theorem zipExt_nil_right (a : List (Option WCell)) :
    zipExt a [] = a := by
  cases a <;> rfl

theorem zip_padTo (len : Nat) :
    ∀ a b : List (Option WCell),
      List.zipWith betterCell (padTo len a) (padTo len b) =
        padTo len (zipExt a b) := by
  induction len with
  | zero => intro a b; simp [padTo_zero]
  | succ len ih =>
      intro a b
      cases a with
      | nil =>
          cases b with
          | nil =>
              rw [padTo_succ_nil, List.zipWith_cons_cons, ih [] []]
              simp [zipExt, betterCell, padTo_succ_nil]
          | cons y b =>
              rw [padTo_succ_nil, padTo_succ_cons,
                List.zipWith_cons_cons, ih [] b]
              simp [zipExt, betterCell, padTo_succ_cons]
      | cons x a =>
          cases b with
          | nil =>
              rw [padTo_succ_cons, padTo_succ_nil,
                List.zipWith_cons_cons, ih a [], betterCell_none_right,
                zipExt_nil_right, zipExt_nil_right, padTo_succ_cons]
          | cons y b =>
              rw [padTo_succ_cons, padTo_succ_cons,
                List.zipWith_cons_cons, ih a b]
              simp [zipExt, padTo_succ_cons]

theorem zipExt_rep :
    ∀ (k : Nat) (a b : List (Option WCell)),
      zipExt (List.replicate k none ++ a) (List.replicate k none ++ b) =
        List.replicate k none ++ zipExt a b := by
  intro k
  induction k with
  | zero => intro a b; rfl
  | succ k ih =>
      intro a b
      simp only [List.replicate_succ, List.cons_append]
      show betterCell none none :: _ = _
      rw [show betterCell none none = none from rfl, ih]

theorem zipExt_shift (p q : Nat) (a b : List (Option WCell)) :
    zipExt (List.replicate p none ++ a) (List.replicate q none ++ b) =
      List.replicate (min p q) none ++
        zipExt (List.replicate (p - min p q) none ++ a)
          (List.replicate (q - min p q) none ++ b) := by
  rcases Nat.le_total p q with h | h
  · rw [Nat.min_eq_left h]
    obtain ⟨d, rfl⟩ : ∃ d, q = p + d :=
      ⟨q - p, (Nat.add_sub_cancel' h).symm⟩
    rw [Nat.sub_self, Nat.add_sub_cancel_left,
      ← List.replicate_append_replicate, List.append_assoc, zipExt_rep,
      List.replicate_zero, List.nil_append]
  · rw [Nat.min_eq_right h]
    obtain ⟨d, rfl⟩ : ∃ d, p = q + d :=
      ⟨p - q, (Nat.add_sub_cancel' h).symm⟩
    rw [Nat.sub_self, Nat.add_sub_cancel_left,
      ← List.replicate_append_replicate, List.append_assoc, zipExt_rep,
      List.replicate_zero, List.nil_append]

theorem padTo_rep (len p : Nat) :
    padTo len (List.replicate p (none : Option WCell)) =
      List.replicate len none := by
  simp only [padTo, List.take_replicate, List.length_replicate,
    List.replicate_append_replicate]
  rw [show min len p + (len - p) = len from by omega]

theorem zipWith_rep_left (L : WFront) :
    List.zipWith betterCell (List.replicate L.length none) L = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, ih]
      rfl

theorem zipWith_rep_right (L : WFront) :
    List.zipWith betterCell L (List.replicate L.length none) = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, ih, betterCell_none_right]

theorem tden_rep_nil (len p : Nat) :
    tden len ⟨p, []⟩ = List.replicate len none := by
  simp [tden, padTo_rep]

theorem tden_length (len : Nat) (f : TFront) :
    (tden len f).length = len := by
  simp [tden, padTo_length]

theorem zipWith_rep_left' (len : Nat) (L : WFront)
    (h : L.length = len) :
    List.zipWith betterCell (List.replicate len none) L = L := by
  subst h
  exact zipWith_rep_left L

theorem zipWith_rep_right' (len : Nat) (L : WFront)
    (h : L.length = len) :
    List.zipWith betterCell L (List.replicate len none) = L := by
  subst h
  exact zipWith_rep_right L

theorem tden_zipT (len : Nat) (f g : TFront) :
    tden len (zipT f g) =
      List.zipWith betterCell (tden len f) (tden len g) := by
  obtain ⟨p, a⟩ := f
  obtain ⟨q, b⟩ := g
  cases a with
  | nil =>
      show tden len ⟨q, b⟩ = _
      rw [tden_rep_nil]
      exact (zipWith_rep_left' len (tden len ⟨q, b⟩)
        (tden_length len ⟨q, b⟩)).symm
  | cons x a =>
      cases b with
      | nil =>
          show tden len ⟨p, x :: a⟩ = _
          rw [tden_rep_nil]
          exact (zipWith_rep_right' len (tden len ⟨p, x :: a⟩)
            (tden_length len ⟨p, x :: a⟩)).symm
      | cons y b =>
          show tden len ⟨min p q, zipExt _ _⟩ = _
          simp only [tden]
          rw [← zipExt_shift, zip_padTo]

theorem tden_shiftUpT (len : Nat) (f : TFront) :
    tden (len + 1) (shiftUpT f) = shiftUp (tden (len + 1) f) := by
  simp only [tden, shiftUpT, shiftUp, List.replicate_succ,
    List.cons_append, padTo_succ_cons, padTo_dropLast]

theorem padTo_rep_take :
    ∀ (p len : Nat) (body : List (Option WCell)),
      padTo (len + 1) (List.replicate p none ++ body.take (len - p)) =
        padTo (len + 1) ((List.replicate p none ++ body).take len) := by
  intro p
  induction p with
  | zero => intro len body; simp
  | succ p ih =>
      intro len body
      cases len with
      | zero =>
          rw [Nat.zero_sub, List.take_zero, List.take_zero,
            List.append_nil, padTo_rep, padTo_nil]
      | succ len =>
          simp only [List.replicate_succ, List.cons_append,
            Nat.succ_sub_succ, padTo_succ_cons, List.take_succ_cons]
          rw [ih len body]

theorem tden_shiftDownT (len : Nat) (f : TFront) :
    tden (len + 1) (shiftDownT (len + 1) f) =
      shiftDown (tden (len + 1) f) := by
  obtain ⟨pad, body⟩ := f
  cases pad with
  | zero =>
      simp only [tden, shiftDownT, shiftDown, List.replicate_zero,
        List.nil_append, padTo_drop_one, padTo_snoc_none,
        Nat.add_sub_cancel]
  | succ p =>
      simp only [tden, shiftDownT, shiftDown, List.replicate_succ,
        List.cons_append, padTo_drop_one, padTo_snoc_none,
        List.drop_succ_cons, List.drop_zero, Nat.succ_sub_succ,
        padTo_rep_take]

theorem tden_mapT (len : Nat) (g : Option WCell → Option WCell)
    (hg : g none = none) (f : TFront) :
    tden len (mapT g f) = (tden len f).map g := by
  simp only [tden, mapT, map_padTo g hg, List.map_append,
    List.map_replicate, hg]

theorem tden_empty (len : Nat) :
    tden len ⟨0, []⟩ = emptyFront len := by
  rw [tden_rep_nil]; rfl

theorem frontAtT_den (len : Nat) (hist : List TLevel) (delta : Nat)
    (selT : TLevel → TFront) (selW : WLevel → WFront)
    (hsel : ∀ lv, selW (tdenLevel len lv) = tden len (selT lv)) :
    tden len (frontAtT hist delta selT) =
      frontAt len (hist.map (tdenLevel len)) delta selW := by
  simp only [frontAtT, frontAt, List.getElem?_map]
  cases hist[delta - 1]? with
  | some lv => simp [hsel]
  | none => simp [tden_empty]

theorem nextLevelT_den (xs ys : List Char) (len : Nat)
    (pe po px : Nat) (hist : List TLevel) :
    tdenLevel (len + 1) (nextLevelT xs ys (len + 1) pe po px hist) =
      nextLevel xs ys (len + 1) pe po px
        (hist.map (tdenLevel (len + 1))) := by
  simp only [nextLevelT, nextLevel, tdenLevel, WLevel.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [tden_zipT, tden_shiftUpT, tden_shiftDownT,
      tden_mapT (len + 1) (stepWith pushGapX xs ys) rfl,
      tden_mapT (len + 1) (stepWith pushGapY xs ys) rfl,
      tden_mapT (len + 1) (stepWith pushDiag xs ys) rfl,
      tden_mapT (len + 1) (Option.map extendCell) rfl,
      frontAtT_den (len + 1) hist pe (·.xf) (·.xf) (fun _ => rfl),
      frontAtT_den (len + 1) hist po (·.mf) (·.mf) (fun _ => rfl),
      frontAtT_den (len + 1) hist pe (·.yf) (·.yf) (fun _ => rfl),
      frontAtT_den (len + 1) hist px (·.mf) (·.mf) (fun _ => rfl)]

theorem padTo_rep_singleton :
    ∀ (m len : Nat) (c : Option WCell), m < len →
      padTo len (List.replicate m none ++ [c]) =
        (List.replicate len (none : Option WCell)).set m c := by
  intro m
  induction m with
  | zero =>
      intro len c hlen
      cases len with
      | zero => exact absurd hlen (Nat.lt_irrefl 0)
      | succ len =>
          rw [List.replicate_zero, List.nil_append, padTo_succ_cons,
            padTo_nil, List.replicate_succ]
          rfl
  | succ m ih =>
      intro len c hlen
      cases len with
      | zero => exact absurd hlen (Nat.not_lt_zero _)
      | succ len =>
          rw [List.replicate_succ, List.cons_append, padTo_succ_cons,
            ih len c (Nat.lt_of_succ_lt_succ hlen),
            List.replicate_succ (n := len)]
          rfl

theorem seedLevelT_den (m len : Nat) (xs ys : List Char)
    (h : m < len) :
    tdenLevel len (seedLevelT m xs ys) = seedLevel m len xs ys := by
  have hmf := padTo_rep_singleton m len
    (some (extendCell ⟨0, 0, xs, ys, []⟩)) h
  simp [tdenLevel, seedLevelT, seedLevel, tden, padTo_nil, emptyFront,
    hmf]

theorem padTo_getElem? :
    ∀ (len n : Nat) (l : List (Option WCell)), n < len →
      (padTo len l)[n]? = some (l[n]?.getD none) := by
  intro len
  induction len with
  | zero => intro n l h; exact absurd h (Nat.not_lt_zero n)
  | succ len ih =>
      intro n l h
      cases l with
      | nil =>
          rw [padTo_succ_nil]
          cases n with
          | zero => rfl
          | succ n =>
              rw [List.getElem?_cons_succ,
                ih n [] (Nat.lt_of_succ_lt_succ h)]
              simp
      | cons x l =>
          rw [padTo_succ_cons]
          cases n with
          | zero => rfl
          | succ n =>
              rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
                ih n l (Nat.lt_of_succ_lt_succ h)]

theorem tgetT_den (len n : Nat) (f : TFront) (h : n < len) :
    (tden len f)[n]? = some (tgetT f n) := by
  rw [tden, padTo_getElem? len n _ h, tgetT]
  rcases Nat.lt_or_ge n f.pad with hn | hn
  · rw [if_pos hn, List.getElem?_append_left (by simpa using hn),
      List.getElem?_replicate]
    simp [hn]
  · rw [if_neg (Nat.not_lt.mpr hn),
      List.getElem?_append_right (by simpa using hn)]
    simp

theorem cornerOfT_den (len n : Nat) (h : n < len) (lv : TLevel) :
    cornerOfT n lv = cornerOf n (tdenLevel len lv) := by
  simp only [cornerOfT, cornerOf, tdenLevel]
  rw [tgetT_den len n lv.mf h]
  cases tgetT lv.mf n with
  | some c => rfl
  | none => rfl

theorem wfaLoopT_eq (xs ys : List Char) (len n : Nat)
    (pe po px : Nat) (hn : n < len + 1) :
    ∀ (fuel : Nat) (hist : List TLevel),
      wfaLoopT xs ys (len + 1) n pe po px fuel hist =
        wfaLoop xs ys (len + 1) n pe po px fuel
          (hist.map (tdenLevel (len + 1))) := by
  intro fuel
  induction fuel with
  | zero => intro hist; rfl
  | succ fuel ih =>
      intro hist
      simp only [wfaLoopT, wfaLoop]
      rw [← nextLevelT_den xs ys len pe po px hist,
        ← cornerOfT_den (len + 1) n hn]
      cases cornerOfT n (nextLevelT xs ys (len + 1) pe po px hist) with
      | some c => rfl
      | none =>
          rw [ih ((nextLevelT xs ys (len + 1) pe po px hist ::
              hist).take (max pe (max po px))),
            List.map_take, List.map_cons]

theorem wfaRunT_eq (sc : Scoring) (xs ys : List Char) :
    wfaRunT sc xs ys = wfaRun sc xs ys := by
  have hm : xs.length < xs.length + ys.length + 1 := by omega
  have hn : ys.length < xs.length + ys.length + 1 := by omega
  simp only [wfaRunT, wfaRun]
  simp only [wfaLoopT_eq xs ys (xs.length + ys.length) ys.length
      ((wfaPe sc).toNat) ((wfaPo sc).toNat) ((wfaPx sc).toNat) hn,
    cornerOfT_den (xs.length + ys.length + 1) ys.length hn,
    List.map_cons, List.map_nil,
    seedLevelT_den xs.length (xs.length + ys.length + 1) xs ys hm]

-- ── LAYER 0b: array-backed bands denote list bands ──

theorem zipExt_eq_append (la : List (Option WCell)) :
    ∀ lb : List (Option WCell),
      zipExt la lb = List.zipWith betterCell la lb ++
        (if la.length ≤ lb.length then lb.drop la.length
         else la.drop lb.length) := by
  induction la with
  | nil => intro lb; simp [zipExt]
  | cons x a ih =>
      intro lb
      cases lb with
      | nil => simp [zipExt]
      | cons y b =>
          simp only [zipExt, List.zipWith_cons_cons, List.length_cons,
            Nat.add_le_add_iff_right, List.drop_succ_cons,
            List.cons_append, ih b]

theorem azipExt_toList (a b : Array (Option WCell)) :
    (azipExt a b).toList = zipExt a.toList b.toList := by
  unfold azipExt
  by_cases h : a.size ≤ b.size
  · rw [if_pos h, Array.toList_append, Array.toList_zipWith,
      Array.toList_extract, zipExt_eq_append,
      if_pos (by simp only [Array.length_toList]; exact h),
      List.extract_eq_take_drop, Array.length_toList]
    congr 1
    exact List.take_of_length_le (by simp [Array.length_toList])
  · rw [if_neg h, Array.toList_append, Array.toList_zipWith,
      Array.toList_extract, zipExt_eq_append,
      if_neg (by simp only [Array.length_toList]; exact h),
      List.extract_eq_take_drop, Array.length_toList]
    congr 1
    exact List.take_of_length_le (by simp [Array.length_toList])

theorem toList_eq_nil_of_isEmpty (a : Array (Option WCell))
    (h : a.isEmpty = true) : a.toList = [] := by
  have hs : a.size = 0 := by simpa [Array.isEmpty] using h
  have hl := Array.length_toList (xs := a)
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem toList_cons_of_not_isEmpty (a : Array (Option WCell))
    (h : a.isEmpty = false) : ∃ x t, a.toList = x :: t := by
  have hs : a.size ≠ 0 := by simpa [Array.isEmpty] using h
  cases ht : a.toList with
  | nil =>
      exfalso
      have hl := Array.length_toList (xs := a)
      rw [ht] at hl
      simp at hl
      exact hs hl.symm
  | cons x t => exact ⟨x, t, rfl⟩

theorem aden_zipA (f g : AFront) :
    aden (zipA f g) = zipT (aden f) (aden g) := by
  obtain ⟨fp, fb⟩ := f
  obtain ⟨gp, gb⟩ := g
  unfold zipA
  cases hf : fb.isEmpty with
  | true =>
      simp only [hf, if_true]
      have h0 := toList_eq_nil_of_isEmpty fb hf
      show aden ⟨gp, gb⟩ = zipT ⟨fp, fb.toList⟩ (aden ⟨gp, gb⟩)
      rw [h0]
      rfl
  | false =>
      obtain ⟨x, ft, hft⟩ := toList_cons_of_not_isEmpty fb hf
      cases hg : gb.isEmpty with
      | true =>
          simp only [hf, hg, if_false, if_true, Bool.false_eq_true]
          have h0 := toList_eq_nil_of_isEmpty gb hg
          show (⟨fp, fb.toList⟩ : TFront) =
            zipT ⟨fp, fb.toList⟩ ⟨gp, gb.toList⟩
          rw [h0, hft]
          rfl
      | false =>
          obtain ⟨y, gt, hgt⟩ := toList_cons_of_not_isEmpty gb hg
          simp only [hf, hg, if_false, Bool.false_eq_true]
          show (⟨min fp gp,
            (azipExt (Array.replicate (fp - min fp gp) none ++ fb)
              (Array.replicate (gp - min fp gp) none ++ gb)).toList⟩ :
                TFront) =
            zipT ⟨fp, fb.toList⟩ ⟨gp, gb.toList⟩
          rw [azipExt_toList, Array.toList_append, Array.toList_append,
            Array.toList_replicate, Array.toList_replicate, hft, hgt]
          rfl

theorem aden_shiftUpA (f : AFront) :
    aden (shiftUpA f) = shiftUpT (aden f) := rfl

theorem aden_shiftDownA (len : Nat) (f : AFront) :
    aden (shiftDownA len f) = shiftDownT len (aden f) := by
  obtain ⟨pad, body⟩ := f
  cases pad with
  | zero =>
      simp only [shiftDownA, shiftDownT, aden, Array.toList_extract,
        List.extract_eq_take_drop]
      rw [show 1 + (len - 1) - 1 = len - 1 from by omega]
  | succ p =>
      simp only [shiftDownA, shiftDownT, aden, Array.toList_extract,
        List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]

theorem aden_mapA (g : Option WCell → Option WCell) (f : AFront) :
    aden (mapA g f) = mapT g (aden f) := by
  simp only [aden, mapA, mapT, Array.toList_map]

theorem frontAtA_den (hist : List ALevel) (delta : Nat)
    (selA : ALevel → AFront) (selT : TLevel → TFront)
    (hsel : ∀ lv, selT (adenLevel lv) = aden (selA lv)) :
    aden (frontAtA hist delta selA) =
      frontAtT (hist.map adenLevel) delta selT := by
  simp only [frontAtA, frontAtT, List.getElem?_map]
  cases hist[delta - 1]? with
  | some lv => simp [hsel]
  | none => rfl

theorem nextLevelA_den (xs ys : List Char) (len : Nat)
    (pe po px : Nat) (hist : List ALevel) :
    adenLevel (nextLevelA xs ys len pe po px hist) =
      nextLevelT xs ys len pe po px (hist.map adenLevel) := by
  simp only [nextLevelA, nextLevelT, adenLevel, TLevel.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [aden_zipA, aden_shiftUpA, aden_shiftDownA, aden_mapA,
      frontAtA_den hist pe (·.xf) (·.xf) (fun _ => rfl),
      frontAtA_den hist po (·.mf) (·.mf) (fun _ => rfl),
      frontAtA_den hist pe (·.yf) (·.yf) (fun _ => rfl),
      frontAtA_den hist px (·.mf) (·.mf) (fun _ => rfl)]

theorem seedLevelA_den (m : Nat) (xs ys : List Char) :
    adenLevel (seedLevelA m xs ys) = seedLevelT m xs ys := rfl

theorem tgetA_den (f : AFront) (n : Nat) :
    tgetA f n = tgetT (aden f) n := by
  simp only [tgetA, tgetT, aden, Array.getElem?_toList]

theorem cornerOfA_den (n : Nat) (lv : ALevel) :
    cornerOfA n lv = cornerOfT n (adenLevel lv) := by
  simp only [cornerOfA, cornerOfT, adenLevel, tgetA_den]

theorem wfaLoopA_eq (xs ys : List Char) (len n : Nat)
    (pe po px : Nat) :
    ∀ (fuel : Nat) (hist : List ALevel),
      wfaLoopA xs ys len n pe po px fuel hist =
        wfaLoopT xs ys len n pe po px fuel (hist.map adenLevel) := by
  intro fuel
  induction fuel with
  | zero => intro hist; rfl
  | succ fuel ih =>
      intro hist
      simp only [wfaLoopA, wfaLoopT]
      rw [← nextLevelA_den xs ys len pe po px hist, ← cornerOfA_den]
      cases cornerOfA n (nextLevelA xs ys len pe po px hist) with
      | some c => rfl
      | none =>
          rw [ih ((nextLevelA xs ys len pe po px hist :: hist).take
              (max pe (max po px))), List.map_take, List.map_cons]

theorem wfaRunA_eq (sc : Scoring) (xs ys : List Char) :
    wfaRunA sc xs ys = wfaRunT sc xs ys := by
  simp only [wfaRunA, wfaRunT]
  simp only [wfaLoopA_eq xs ys (xs.length + ys.length + 1) ys.length
      ((wfaPe sc).toNat) ((wfaPo sc).toNat) ((wfaPx sc).toNat),
    cornerOfA_den, List.map_cons, List.map_nil, seedLevelA_den]

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 1: appending columns to a walk
-- ══════════════════════════════════════════════════════════════════

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 1: appending columns to a walk
-- ══════════════════════════════════════════════════════════════════

/-- The carried previous-step state after playing a walk. -/
def lastPrev (w : List Step) (prev : Option Step) : Option Step :=
  match w with
  | [] => prev
  | s :: rest => lastPrev rest (some s)

theorem lastPrev_snoc (w : List Step) (s : Step) (prev : Option Step) :
    lastPrev (w ++ [s]) prev = some s := by
  induction w generalizing prev with
  | nil => rfl
  | cons a w ih => exact ih (some a)

/-- The last state of a stored (reversed) walk is its head. -/
theorem lastPrev_reverse (r : List Step) (prev : Option Step) :
    lastPrev r.reverse prev =
      match r with
      | [] => prev
      | s :: _ => some s := by
  cases r with
  | nil => rfl
  | cons s rest => rw [List.reverse_cons, lastPrev_snoc]

/-- THE APPEND LEMMA: scores add across a split, with the boundary
previous-step correction.  (This is also the BiWFA splitting
ingredient.) -/
theorem scoreWalk_append (sc : Scoring) (w1 w2 : List Step)
    (xs1 ys1 xs2 ys2 : List Char) (prev : Option Step)
    (h1 : IsMonotoneWalk w1 xs1 ys1) :
    scoreWalk sc (w1 ++ w2) (xs1 ++ xs2) (ys1 ++ ys2) prev =
      scoreWalk sc w1 xs1 ys1 prev +
        scoreWalk sc w2 xs2 ys2 (lastPrev w1 prev) := by
  induction w1 generalizing xs1 ys1 prev with
  | nil =>
      obtain ⟨hx, hy⟩ := h1
      simp at hx hy
      cases xs1 with
      | cons x xs1 => simp at hx
      | nil =>
          cases ys1 with
          | cons y ys1 => simp at hy
          | nil => simp [scoreWalk, lastPrev]
  | cons s w1 ih =>
      obtain ⟨hx, hy⟩ := h1
      cases s with
      | diag =>
          cases xs1 with
          | nil => simp [xConsumed] at hx
          | cons x xs1 =>
              cases ys1 with
              | nil => simp [yConsumed] at hy
              | cons y ys1 =>
                  simp [xConsumed, yConsumed] at hx hy
                  rw [List.cons_append, List.cons_append, List.cons_append,
                    scoreWalk_diag_cons, scoreWalk_diag_cons,
                    ih xs1 ys1 (some .diag) ⟨by omega, by omega⟩]
                  show _ = _ + _ + _
                  rw [Int.add_assoc]
                  rfl
      | gapX =>
          cases ys1 with
          | nil => simp [yConsumed] at hy
          | cons y ys1 =>
              simp [xConsumed, yConsumed] at hx hy
              rw [List.cons_append, List.cons_append,
                scoreWalk_gapX_cons, scoreWalk_gapX_cons,
                ih xs1 ys1 (some .gapX) ⟨by omega, by omega⟩]
              show _ = _ + _ + _
              rw [Int.add_assoc]
              rfl
      | gapY =>
          cases xs1 with
          | nil => simp [xConsumed] at hx
          | cons x xs1 =>
              simp [xConsumed, yConsumed] at hx hy
              rw [List.cons_append, List.cons_append,
                scoreWalk_gapY_cons, scoreWalk_gapY_cons,
                ih xs1 ys1 (some .gapY) ⟨by omega, by omega⟩]
              show _ = _ + _ + _
              rw [Int.add_assoc]
              rfl

-- Closed forms for singleton walks.
theorem scoreWalk_single_diag (sc : Scoring) (x y : Char)
    (prev : Option Step) :
    scoreWalk sc [.diag] [x] [y] prev = diagCost sc x y := by
  rw [scoreWalk_diag_cons]; simp [scoreWalk]

theorem scoreWalk_single_gapX (sc : Scoring) (y : Char)
    (prev : Option Step) :
    scoreWalk sc [.gapX] [] [y] prev = gapXCost sc prev := by
  rw [scoreWalk_gapX_cons]; simp [scoreWalk]

theorem scoreWalk_single_gapY (sc : Scoring) (x : Char)
    (prev : Option Step) :
    scoreWalk sc [.gapY] [x] [] prev = gapYCost sc prev := by
  rw [scoreWalk_gapY_cons]; simp [scoreWalk]

-- Snoc corollaries of the append lemma.
theorem scoreWalk_snoc_diag (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (x y : Char) (prev : Option Step)
    (h1 : IsMonotoneWalk w xs1 ys1) :
    scoreWalk sc (w ++ [.diag]) (xs1 ++ [x]) (ys1 ++ [y]) prev =
      scoreWalk sc w xs1 ys1 prev + diagCost sc x y := by
  rw [scoreWalk_append sc w [.diag] xs1 ys1 [x] [y] prev h1,
    scoreWalk_single_diag]

theorem scoreWalk_snoc_gapX (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (y : Char) (prev : Option Step)
    (h1 : IsMonotoneWalk w xs1 ys1) :
    scoreWalk sc (w ++ [.gapX]) xs1 (ys1 ++ [y]) prev =
      scoreWalk sc w xs1 ys1 prev + gapXCost sc (lastPrev w prev) := by
  have := scoreWalk_append sc w [.gapX] xs1 ys1 [] [y] prev h1
  rw [List.append_nil] at this
  rw [this, scoreWalk_single_gapX]

theorem scoreWalk_snoc_gapY (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (x : Char) (prev : Option Step)
    (h1 : IsMonotoneWalk w xs1 ys1) :
    scoreWalk sc (w ++ [.gapY]) (xs1 ++ [x]) ys1 prev =
      scoreWalk sc w xs1 ys1 prev + gapYCost sc (lastPrev w prev) := by
  have := scoreWalk_append sc w [.gapY] xs1 ys1 [x] [] prev h1
  rw [List.append_nil] at this
  rw [this, scoreWalk_single_gapY]

-- Validity is preserved by snoc (pure count arithmetic).
theorem isMonotoneWalk_snoc_diag (w : List Step) (xs1 ys1 : List Char)
    (x y : Char) (h : IsMonotoneWalk w xs1 ys1) :
    IsMonotoneWalk (w ++ [.diag]) (xs1 ++ [x]) (ys1 ++ [y]) := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] <;> omega

theorem isMonotoneWalk_snoc_gapX (w : List Step) (xs1 ys1 : List Char)
    (y : Char) (h : IsMonotoneWalk w xs1 ys1) :
    IsMonotoneWalk (w ++ [.gapX]) xs1 (ys1 ++ [y]) := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] <;> omega

theorem isMonotoneWalk_snoc_gapY (w : List Step) (xs1 ys1 : List Char)
    (x : Char) (h : IsMonotoneWalk w xs1 ys1) :
    IsMonotoneWalk (w ++ [.gapY]) (xs1 ++ [x]) ys1 := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] <;> omega

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 1b: the prefix penalty and its exact increments
-- ══════════════════════════════════════════════════════════════════

/-- Doubled penalty of a prefix walk against its consumed prefixes
(the quantity the wavefront levels count). -/
def penOf (sc : Scoring) (w : List Step) (xsPre ysPre : List Char) :
    Int :=
  sc.matchScore * ((xsPre.length : Int) + (ysPre.length : Int)) -
    2 * scoreWalk sc w xsPre ysPre none

theorem penOf_nil (sc : Scoring) : penOf sc [] [] [] = 0 := by
  simp [penOf, scoreWalk]

/-- On valid walks the prefix penalty is the doubled-model
`pathPenalty`, hence nonnegative under a reasonable scoring. -/
theorem penOf_eq_pathPenalty (sc : Scoring) (w : List Step)
    (xsPre ysPre : List Char) (h : IsMonotoneWalk w xsPre ysPre) :
    penOf sc w xsPre ysPre = pathPenalty sc w xsPre ysPre none := by
  have := penalty_transform sc w xsPre ysPre none h
  rw [penOf]
  omega

theorem penOf_nonneg (sc : Scoring) (hr : ReasonableScoring sc)
    (w : List Step) (xsPre ysPre : List Char)
    (h : IsMonotoneWalk w xsPre ysPre) :
    0 ≤ penOf sc w xsPre ysPre := by
  rw [penOf_eq_pathPenalty sc w xsPre ysPre h]
  exact pathPenalty_nonneg sc w xsPre ysPre none hr

theorem penOf_snoc_diag (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (x y : Char)
    (h : IsMonotoneWalk w xs1 ys1) :
    penOf sc (w ++ [.diag]) (xs1 ++ [x]) (ys1 ++ [y]) =
      penOf sc w xs1 ys1 + (if x = y then 0 else wfaPx sc) := by
  rw [penOf, penOf, scoreWalk_snoc_diag sc w xs1 ys1 x y none h]
  have hx : ((xs1 ++ [x]).length : Int) = (xs1.length : Int) + 1 := by
    simp
  have hy : ((ys1 ++ [y]).length : Int) = (ys1.length : Int) + 1 := by
    simp
  rw [hx, hy]
  rw [show (xs1.length : Int) + 1 + ((ys1.length : Int) + 1) =
    ((xs1.length : Int) + (ys1.length : Int)) + 2 from by omega]
  rw [Int.mul_add]
  unfold wfaPx diagCost
  by_cases hxy : x = y <;> simp [hxy] <;> omega

theorem penOf_snoc_gapX (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (y : Char)
    (h : IsMonotoneWalk w xs1 ys1) :
    penOf sc (w ++ [.gapX]) xs1 (ys1 ++ [y]) =
      penOf sc w xs1 ys1 +
        (if lastPrev w none = some .gapX then wfaPe sc else wfaPo sc) := by
  rw [penOf, penOf, scoreWalk_snoc_gapX sc w xs1 ys1 y none h]
  have hy : ((ys1 ++ [y]).length : Int) = (ys1.length : Int) + 1 := by
    simp
  rw [hy]
  rw [show (xs1.length : Int) + ((ys1.length : Int) + 1) =
    ((xs1.length : Int) + (ys1.length : Int)) + 1 from by omega]
  rw [Int.mul_add]
  unfold wfaPe wfaPo wfaPe gapXCost
  by_cases hp : lastPrev w none = some Step.gapX <;> simp [hp] <;> omega

theorem penOf_snoc_gapY (sc : Scoring) (w : List Step)
    (xs1 ys1 : List Char) (x : Char)
    (h : IsMonotoneWalk w xs1 ys1) :
    penOf sc (w ++ [.gapY]) (xs1 ++ [x]) ys1 =
      penOf sc w xs1 ys1 +
        (if lastPrev w none = some .gapY then wfaPe sc else wfaPo sc) := by
  rw [penOf, penOf, scoreWalk_snoc_gapY sc w xs1 ys1 x none h]
  have hx : ((xs1 ++ [x]).length : Int) = (xs1.length : Int) + 1 := by
    simp
  rw [hx]
  rw [show (xs1.length : Int) + 1 + (ys1.length : Int) =
    ((xs1.length : Int) + (ys1.length : Int)) + 1 from by omega]
  rw [Int.mul_add]
  unfold wfaPe wfaPo wfaPe gapYCost
  by_cases hp : lastPrev w none = some Step.gapY <;> simp [hp] <;> omega

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 2: the boundary surgery never cheats
-- ══════════════════════════════════════════════════════════════════

/-- What it means for a stored cell to be a genuine ≤-p point. -/
structure CellOK (sc : Scoring) (xs ys : List Char) (p : Int)
    (c : WCell) : Prop where
  hxs    : c.xsRem = xs.drop c.off
  hys    : c.ysRem = ys.drop c.joff
  hoff   : c.off ≤ xs.length
  hjoff  : c.joff ≤ ys.length
  hvalid : IsMonotoneWalk c.walk.reverse (xs.take c.off) (ys.take c.joff)
  hpen   : penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) ≤ p

theorem splitRun_some (s : Step) (l : List Step) (a : Nat) (e : Step)
    (t : List Step) (h : splitRun s l = (a, some e, t)) :
    l = List.replicate a s ++ e :: t ∧ ¬ e = s := by
  induction l generalizing a with
  | nil => simp [splitRun] at h
  | cons c rest ih =>
      by_cases hc : c = s
      · simp only [splitRun, if_pos hc] at h
        have h1 : (splitRun s rest).1 + 1 = a := congrArg Prod.fst h
        have h2 : (splitRun s rest).2 = (some e, t) := congrArg Prod.snd h
        cases a with
        | zero => omega
        | succ a0 =>
            have hsp' : splitRun s rest = (a0, some e, t) := by
              have hfst : (splitRun s rest).1 = a0 := by omega
              calc splitRun s rest
                  = ((splitRun s rest).1, (splitRun s rest).2) := rfl
                _ = (a0, some e, t) := by rw [hfst, h2]
            obtain ⟨hl, he⟩ := ih a0 hsp'
            subst hc
            simp [List.replicate_succ, hl, he]
      · simp only [splitRun, if_neg hc] at h
        have h1 : (0 : Nat) = a := congrArg Prod.fst h
        have h2 : some c = some e := congrArg (fun q => q.2.1) h
        have h3 : rest = t := congrArg (fun q => q.2.2) h
        obtain rfl : c = e := Option.some.inj h2
        subst h3
        have : a = 0 := h1.symm
        subst this
        simp [hc]

theorem splitRun_head (s : Step) (rest : List Step) :
    (splitRun s (s :: rest)).1 = (splitRun s rest).1 + 1 := by
  simp [splitRun]

-- Consumption sums of gap runs.
theorem xsum_replicate_gapX (a : Nat) :
    ((List.replicate a Step.gapX).map xConsumed).sum = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, xConsumed, ih]

theorem ysum_replicate_gapX (a : Nat) :
    ((List.replicate a Step.gapX).map yConsumed).sum = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, yConsumed, ih]; omega

theorem xsum_replicate_gapY (a : Nat) :
    ((List.replicate a Step.gapY).map xConsumed).sum = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, xConsumed, ih]; omega

theorem ysum_replicate_gapY (a : Nat) :
    ((List.replicate a Step.gapY).map yConsumed).sum = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, yConsumed, ih]

/-- The surgery un-consumes exactly one character of each string. -/
theorem demoteWalk_counts (r r' : List Step)
    (h : demoteWalk r = some r') :
    (r'.map xConsumed).sum + 1 = (r.map xConsumed).sum ∧
    (r'.map yConsumed).sum + 1 = (r.map yConsumed).sum := by
  match r with
  | [] => simp [demoteWalk] at h
  | .diag :: rest =>
      simp only [demoteWalk, Option.some.injEq] at h
      subst h
      simp [xConsumed, yConsumed]
      omega
  | .gapX :: rest =>
      rcases hsp : splitRun .gapX (.gapX :: rest) with ⟨a, oe, t⟩
      have ha : 1 ≤ a := by
        have := splitRun_head .gapX rest
        rw [hsp] at this
        simp at this
        omega
      cases oe with
      | none => simp [demoteWalk, hsp] at h
      | some e =>
          obtain ⟨hl, hne⟩ := splitRun_some _ _ _ _ _ hsp
          cases e with
          | diag =>
              simp only [demoteWalk, hsp, Option.some.injEq] at h
              subst h
              rw [hl]
              simp [xConsumed, yConsumed, xsum_replicate_gapX,
                ysum_replicate_gapX]
              omega
          | gapX => exact absurd rfl hne
          | gapY =>
              simp only [demoteWalk, hsp, Option.some.injEq] at h
              subst h
              rw [hl]
              simp [xConsumed, yConsumed, xsum_replicate_gapX,
                ysum_replicate_gapX]
              omega
  | .gapY :: rest =>
      rcases hsp : splitRun .gapY (.gapY :: rest) with ⟨a, oe, t⟩
      have ha : 1 ≤ a := by
        have := splitRun_head .gapY rest
        rw [hsp] at this
        simp at this
        omega
      cases oe with
      | none => simp [demoteWalk, hsp] at h
      | some e =>
          obtain ⟨hl, hne⟩ := splitRun_some _ _ _ _ _ hsp
          cases e with
          | diag =>
              simp only [demoteWalk, hsp, Option.some.injEq] at h
              subst h
              rw [hl]
              simp [xConsumed, yConsumed, xsum_replicate_gapY,
                ysum_replicate_gapY]
              omega
          | gapY => exact absurd rfl hne
          | gapX =>
              simp only [demoteWalk, hsp, Option.some.injEq] at h
              subst h
              rw [hl]
              simp [xConsumed, yConsumed, xsum_replicate_gapY,
                ysum_replicate_gapY]
              omega

-- Gap-run score closed forms.
theorem scoreWalk_replicate_gapX (sc : Scoring) (a : Nat)
    (L : List Char) (h : L.length = a) (σ : Option Step) :
    scoreWalk sc (List.replicate a .gapX) [] L σ =
      if a = 0 then 0
      else gapXCost sc σ + ((a : Int) - 1) * sc.gapExtend := by
  induction a generalizing L σ with
  | zero =>
      cases L with
      | nil => simp [scoreWalk]
      | cons z L => simp at h
  | succ a ih =>
      cases L with
      | nil => simp at h
      | cons z L =>
          rw [List.replicate_succ, scoreWalk_gapX_cons,
            ih L (by simpa using h) (some .gapX), gapXCost_gapX_eq]
          by_cases ha : a = 0
          · subst ha; simp
          · simp only [ha, if_neg, if_false, Nat.succ_ne_zero]
            rw [show ((a + 1 : Nat) : Int) - 1 = ((a : Int) - 1) + 1 from by
              omega]
            rw [Int.add_mul, Int.one_mul]
            omega

theorem scoreWalk_replicate_gapY (sc : Scoring) (a : Nat)
    (L : List Char) (h : L.length = a) (σ : Option Step) :
    scoreWalk sc (List.replicate a .gapY) L [] σ =
      if a = 0 then 0
      else gapYCost sc σ + ((a : Int) - 1) * sc.gapExtend := by
  induction a generalizing L σ with
  | zero =>
      cases L with
      | nil => simp [scoreWalk]
      | cons z L => simp at h
  | succ a ih =>
      cases L with
      | nil => simp at h
      | cons z L =>
          rw [List.replicate_succ, scoreWalk_gapY_cons,
            ih L (by simpa using h) (some .gapY), gapYCost_gapY_eq]
          by_cases ha : a = 0
          · subst ha; simp
          · simp only [ha, if_neg, if_false, Nat.succ_ne_zero]
            rw [show ((a + 1 : Nat) : Int) - 1 = ((a : Int) - 1) + 1 from by
              omega]
            rw [Int.add_mul, Int.one_mul]
            omega

-- Gap-cost bounds reused from the exchange file, in the forms omega
-- likes.
theorem gapXCost_ge_open (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (σ : Option Step) :
    sc.gapOpen + sc.gapExtend ≤ gapXCost sc σ := by
  have := gapXCost_none_le_prev sc hO σ
  rw [gapXCost_none_eq] at this
  exact this

theorem gapYCost_ge_open (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (σ : Option Step) :
    sc.gapOpen + sc.gapExtend ≤ gapYCost sc σ := by
  have := gapYCost_none_le_prev sc hO σ
  rw [gapYCost_none_eq] at this
  exact this

theorem gapXCost_le_extend (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (σ : Option Step) :
    gapXCost sc σ ≤ sc.gapExtend := by
  have := gapXCost_prev_le_none_sub sc hO σ
  rw [gapXCost_none_eq] at this
  omega

theorem gapYCost_le_extend (sc : Scoring) (hO : sc.gapOpen ≤ 0)
    (σ : Option Step) :
    gapYCost sc σ ≤ sc.gapExtend := by
  have := gapYCost_prev_le_none_sub sc hO σ
  rw [gapYCost_none_eq] at this
  omega

theorem gapXCost_diag_eq (sc : Scoring) :
    gapXCost sc (some .diag) = sc.gapOpen + sc.gapExtend := by
  simp [gapXCost]

theorem gapYCost_diag_eq (sc : Scoring) :
    gapYCost sc (some .diag) = sc.gapOpen + sc.gapExtend := by
  simp [gapYCost]

theorem sum_map_reverse (f : Step → Nat) (l : List Step) :
    (l.reverse.map f).sum = (l.map f).sum := by
  rw [List.map_reverse, List.sum_reverse]

/-- THE SURGERY LEMMA: demoting a walk keeps it valid one cell back
and never increases the doubled penalty. -/
theorem demoteWalk_pen (sc : Scoring) (hr : ReasonableScoring sc)
    (r r' : List Step) (xs' ys' : List Char) (x y : Char)
    (h : demoteWalk r = some r')
    (hvalid : IsMonotoneWalk r.reverse (xs' ++ [x]) (ys' ++ [y])) :
    IsMonotoneWalk r'.reverse xs' ys' ∧
    penOf sc r'.reverse xs' ys' ≤
      penOf sc r.reverse (xs' ++ [x]) (ys' ++ [y]) := by
  have hM := hr.match_pos
  have hE := hr.extend_neg
  have hO := hr.open_neg
  obtain ⟨hcx, hcy⟩ := demoteWalk_counts r r' h
  obtain ⟨hvx, hvy⟩ := hvalid
  have hval' : IsMonotoneWalk r'.reverse xs' ys' := by
    constructor
    · have h1 := sum_map_reverse xConsumed r
      have h2 := sum_map_reverse xConsumed r'
      simp at hvx
      omega
    · have h1 := sum_map_reverse yConsumed r
      have h2 := sum_map_reverse yConsumed r'
      simp at hvy
      omega
  refine ⟨hval', ?_⟩
  have hlxI : ((xs' ++ [x]).length : Int) = (xs'.length : Int) + 1 := by
    simp
  have hlyI : ((ys' ++ [y]).length : Int) = (ys'.length : Int) + 1 := by
    simp
  have hexp : ∀ (w : List Step) (xsP ysP : List Char),
      penOf sc w xsP ysP = sc.matchScore * (xsP.length : Int) +
        sc.matchScore * (ysP.length : Int) -
        2 * scoreWalk sc w xsP ysP none := by
    intro w xsP ysP
    rw [penOf, Int.mul_add]
  have hxprod : sc.matchScore * ((xs'.length : Int) + 1) =
      sc.matchScore * (xs'.length : Int) + sc.matchScore := by
    rw [Int.mul_add, Int.mul_one]
  have hyprod : sc.matchScore * ((ys'.length : Int) + 1) =
      sc.matchScore * (ys'.length : Int) + sc.matchScore := by
    rw [Int.mul_add, Int.mul_one]
  match r with
  | .diag :: rest =>
      have hr' : rest = r' := by
        simp only [demoteWalk, Option.some.injEq] at h
        exact h
      subst hr'
      have hsc := scoreWalk_snoc_diag sc rest.reverse xs' ys' x y none hval'
      rw [hexp, hexp, List.reverse_cons, hsc, hlxI, hlyI, hxprod, hyprod]
      have hdm := diagCost_le_match sc hr x y
      omega
  | .gapX :: rest =>
      rcases hsp : splitRun .gapX (.gapX :: rest) with ⟨a, oe, t⟩
      have ha : 1 ≤ a := by
        have := splitRun_head .gapX rest
        rw [hsp] at this
        simp at this
        omega
      obtain ⟨a0, rfl⟩ : ∃ a0, a = a0 + 1 := ⟨a - 1, by omega⟩
      cases oe with
      | none => simp [demoteWalk, hsp] at h
      | some e =>
          obtain ⟨hl, hne⟩ := splitRun_some _ _ _ _ _ hsp
          have hrev : (Step.gapX :: rest).reverse =
              t.reverse ++ (e :: List.replicate (a0 + 1) Step.gapX) := by
            rw [hl, List.reverse_append, List.reverse_cons,
              List.reverse_replicate, List.append_assoc,
              List.singleton_append]
          rw [hrev] at hvx hvy
          simp only [List.map_append, List.sum_append, List.map_cons,
            List.sum_cons, List.length_append, List.length_cons,
            List.length_nil] at hvx hvy
          cases e with
          | gapX => exact absurd rfl hne
          | diag =>
              have hr' : r' = List.replicate (a0 + 1) .gapX ++ t := by
                simp only [demoteWalk, hsp, Option.some.injEq] at h
                exact h.symm
              subst hr'
              simp only [xConsumed, yConsumed, xsum_replicate_gapX,
                ysum_replicate_gapX] at hvx hvy
              have hbx := sum_map_reverse xConsumed t
              have hby := sum_map_reverse yConsumed t
              have hta : (t.reverse.map xConsumed).sum = xs'.length := by
                simp at hvx; omega
              have htb : (t.reverse.map yConsumed).sum + (a0 + 1) =
                  ys'.length := by
                simp at hvy; omega
              have hvt : IsMonotoneWalk t.reverse xs'
                  (ys'.take ((t.reverse.map yConsumed).sum)) := by
                refine ⟨hta, ?_⟩
                rw [List.length_take]
                omega
              have hdlen :
                  (ys'.drop ((t.reverse.map yConsumed).sum)).length =
                    a0 + 1 := by
                rw [List.length_drop]; omega
              obtain ⟨z, L, hzL⟩ :
                  ∃ z L, ys'.drop ((t.reverse.map yConsumed).sum) =
                    z :: L := by
                cases hd : ys'.drop ((t.reverse.map yConsumed).sum) with
                | nil => rw [hd] at hdlen; simp at hdlen
                | cons z L => exact ⟨z, L, rfl⟩
              have hLlen : L.length = a0 := by
                rw [hzL] at hdlen
                simpa using hdlen
              -- OLD score
              have hOld := scoreWalk_append sc t.reverse
                (Step.diag :: List.replicate (a0 + 1) Step.gapX) xs'
                (ys'.take ((t.reverse.map yConsumed).sum)) [x]
                (ys'.drop ((t.reverse.map yConsumed).sum) ++ [y])
                none hvt
              rw [← List.append_assoc, List.take_append_drop] at hOld
              have hOldInner :
                  scoreWalk sc
                    (Step.diag :: List.replicate (a0 + 1) Step.gapX)
                    [x] (ys'.drop ((t.reverse.map yConsumed).sum) ++ [y])
                    (lastPrev t.reverse none) =
                  diagCost sc x z + (gapXCost sc (some .diag) +
                    ((a0 + 1 : Nat) : Int) * sc.gapExtend -
                      sc.gapExtend) := by
                rw [hzL, List.cons_append, scoreWalk_diag_cons,
                  scoreWalk_replicate_gapX sc (a0 + 1) (L ++ [y])
                    (by simp [hLlen]) (some .diag),
                  if_neg (by omega : ¬ a0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hOldInner] at hOld
              -- NEW score
              have hNew := scoreWalk_append sc t.reverse
                (List.replicate (a0 + 1) Step.gapX) xs'
                (ys'.take ((t.reverse.map yConsumed).sum)) []
                (ys'.drop ((t.reverse.map yConsumed).sum)) none hvt
              rw [List.take_append_drop, List.append_nil] at hNew
              have hNewInner :
                  scoreWalk sc (List.replicate (a0 + 1) Step.gapX) []
                    (ys'.drop ((t.reverse.map yConsumed).sum))
                    (lastPrev t.reverse none) =
                  gapXCost sc (lastPrev t.reverse none) +
                    ((a0 + 1 : Nat) : Int) * sc.gapExtend -
                      sc.gapExtend := by
                rw [scoreWalk_replicate_gapX sc (a0 + 1)
                  (ys'.drop ((t.reverse.map yConsumed).sum)) hdlen
                  (lastPrev t.reverse none),
                  if_neg (by omega : ¬ a0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hNewInner] at hNew
              have hrevNew :
                  (List.replicate (a0 + 1) Step.gapX ++ t).reverse =
                    t.reverse ++ List.replicate (a0 + 1) Step.gapX := by
                rw [List.reverse_append, List.reverse_replicate]
              rw [hexp, hexp, hrev, hrevNew, hOld, hNew, hlxI, hlyI, hxprod, hyprod]
              have hdm := diagCost_le_match sc hr x z
              have hgge := gapXCost_ge_open sc hO (lastPrev t.reverse none)
              have hgdiag := gapXCost_diag_eq sc
              omega
          | gapY =>
              have hr' : r' = List.replicate a0 .gapX ++ t := by
                simp only [demoteWalk, hsp, Option.some.injEq,
                  Nat.add_sub_cancel] at h
                exact h.symm
              subst hr'
              simp only [xConsumed, yConsumed, xsum_replicate_gapX,
                ysum_replicate_gapX] at hvx hvy
              have hbx := sum_map_reverse xConsumed t
              have hby := sum_map_reverse yConsumed t
              have hta : (t.reverse.map xConsumed).sum = xs'.length := by
                simp at hvx; omega
              have htb : (t.reverse.map yConsumed).sum + a0 =
                  ys'.length := by
                simp at hvy; omega
              have hvt : IsMonotoneWalk t.reverse xs'
                  (ys'.take ((t.reverse.map yConsumed).sum)) := by
                refine ⟨hta, ?_⟩
                rw [List.length_take]
                omega
              have hdlen :
                  (ys'.drop ((t.reverse.map yConsumed).sum)).length =
                    a0 := by
                rw [List.length_drop]; omega
              -- OLD score
              have hOld := scoreWalk_append sc t.reverse
                (Step.gapY :: List.replicate (a0 + 1) Step.gapX) xs'
                (ys'.take ((t.reverse.map yConsumed).sum)) [x]
                (ys'.drop ((t.reverse.map yConsumed).sum) ++ [y])
                none hvt
              rw [← List.append_assoc, List.take_append_drop] at hOld
              have hOldInner :
                  scoreWalk sc
                    (Step.gapY :: List.replicate (a0 + 1) Step.gapX)
                    [x] (ys'.drop ((t.reverse.map yConsumed).sum) ++ [y])
                    (lastPrev t.reverse none) =
                  gapYCost sc (lastPrev t.reverse none) +
                    (gapXCost sc (some .gapY) +
                      ((a0 + 1 : Nat) : Int) * sc.gapExtend -
                        sc.gapExtend) := by
                rw [scoreWalk_gapY_cons,
                  scoreWalk_replicate_gapX sc (a0 + 1)
                    (ys'.drop ((t.reverse.map yConsumed).sum) ++ [y])
                    (by simp; omega) (some .gapY),
                  if_neg (by omega : ¬ a0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hOldInner] at hOld
              -- NEW score
              have hNew := scoreWalk_append sc t.reverse
                (List.replicate a0 Step.gapX) xs'
                (ys'.take ((t.reverse.map yConsumed).sum)) []
                (ys'.drop ((t.reverse.map yConsumed).sum)) none hvt
              rw [List.take_append_drop, List.append_nil] at hNew
              have hNewLB :
                  gapXCost sc (lastPrev t.reverse none) +
                      ((a0 : Nat) : Int) * sc.gapExtend - sc.gapExtend ≤
                    scoreWalk sc (List.replicate a0 Step.gapX) []
                      (ys'.drop ((t.reverse.map yConsumed).sum))
                      (lastPrev t.reverse none) := by
                rw [scoreWalk_replicate_gapX sc a0
                  (ys'.drop ((t.reverse.map yConsumed).sum)) hdlen
                  (lastPrev t.reverse none)]
                by_cases h0 : a0 = 0
                · rw [if_pos h0]
                  have hz : ((a0 : Nat) : Int) * sc.gapExtend = 0 := by
                    rw [h0]; omega
                  have hle := gapXCost_le_extend sc hO
                    (lastPrev t.reverse none)
                  omega
                · rw [if_neg h0, Int.sub_mul, Int.one_mul]
                  omega
              have hprodE : ((a0 + 1 : Nat) : Int) * sc.gapExtend =
                  ((a0 : Nat) : Int) * sc.gapExtend + sc.gapExtend := by
                rw [show ((a0 + 1 : Nat) : Int) = ((a0 : Nat) : Int) + 1
                  from by omega, Int.add_mul, Int.one_mul]
              have hrevNew :
                  (List.replicate a0 Step.gapX ++ t).reverse =
                    t.reverse ++ List.replicate a0 Step.gapX := by
                rw [List.reverse_append, List.reverse_replicate]
              rw [hexp, hexp, hrev, hrevNew, hOld, hNew, hlxI, hlyI,
                hxprod, hyprod]
              have hgge := gapXCost_ge_open sc hO (lastPrev t.reverse none)
              have hgle := gapYCost_le_extend sc hO (lastPrev t.reverse none)
              have hggy := gapXCost_gapY_eq sc
              omega
  | .gapY :: rest =>
      rcases hsp : splitRun .gapY (.gapY :: rest) with ⟨b, oe, t⟩
      have hb : 1 ≤ b := by
        have := splitRun_head .gapY rest
        rw [hsp] at this
        simp at this
        omega
      obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 := ⟨b - 1, by omega⟩
      cases oe with
      | none => simp [demoteWalk, hsp] at h
      | some e =>
          obtain ⟨hl, hne⟩ := splitRun_some _ _ _ _ _ hsp
          have hrev : (Step.gapY :: rest).reverse =
              t.reverse ++ (e :: List.replicate (b0 + 1) Step.gapY) := by
            rw [hl, List.reverse_append, List.reverse_cons,
              List.reverse_replicate, List.append_assoc,
              List.singleton_append]
          rw [hrev] at hvx hvy
          simp only [List.map_append, List.sum_append, List.map_cons,
            List.sum_cons, List.length_append, List.length_cons,
            List.length_nil] at hvx hvy
          cases e with
          | gapY => exact absurd rfl hne
          | diag =>
              have hr' : r' = List.replicate (b0 + 1) .gapY ++ t := by
                simp only [demoteWalk, hsp, Option.some.injEq] at h
                exact h.symm
              subst hr'
              simp only [xConsumed, yConsumed, xsum_replicate_gapY,
                ysum_replicate_gapY] at hvx hvy
              have hbx := sum_map_reverse xConsumed t
              have hby := sum_map_reverse yConsumed t
              have htb : (t.reverse.map yConsumed).sum = ys'.length := by
                simp at hvy; omega
              have hta : (t.reverse.map xConsumed).sum + (b0 + 1) =
                  xs'.length := by
                simp at hvx; omega
              have hvt : IsMonotoneWalk t.reverse
                  (xs'.take ((t.reverse.map xConsumed).sum)) ys' := by
                refine ⟨?_, htb⟩
                rw [List.length_take]
                omega
              have hdlen :
                  (xs'.drop ((t.reverse.map xConsumed).sum)).length =
                    b0 + 1 := by
                rw [List.length_drop]; omega
              obtain ⟨z, L, hzL⟩ :
                  ∃ z L, xs'.drop ((t.reverse.map xConsumed).sum) =
                    z :: L := by
                cases hd : xs'.drop ((t.reverse.map xConsumed).sum) with
                | nil => rw [hd] at hdlen; simp at hdlen
                | cons z L => exact ⟨z, L, rfl⟩
              have hLlen : L.length = b0 := by
                rw [hzL] at hdlen
                simpa using hdlen
              -- OLD score
              have hOld := scoreWalk_append sc t.reverse
                (Step.diag :: List.replicate (b0 + 1) Step.gapY)
                (xs'.take ((t.reverse.map xConsumed).sum)) ys'
                (xs'.drop ((t.reverse.map xConsumed).sum) ++ [x]) [y]
                none hvt
              rw [← List.append_assoc, List.take_append_drop] at hOld
              have hOldInner :
                  scoreWalk sc
                    (Step.diag :: List.replicate (b0 + 1) Step.gapY)
                    (xs'.drop ((t.reverse.map xConsumed).sum) ++ [x]) [y]
                    (lastPrev t.reverse none) =
                  diagCost sc z y + (gapYCost sc (some .diag) +
                    ((b0 + 1 : Nat) : Int) * sc.gapExtend -
                      sc.gapExtend) := by
                rw [hzL, List.cons_append, scoreWalk_diag_cons,
                  scoreWalk_replicate_gapY sc (b0 + 1) (L ++ [x])
                    (by simp [hLlen]) (some .diag),
                  if_neg (by omega : ¬ b0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hOldInner] at hOld
              -- NEW score
              have hNew := scoreWalk_append sc t.reverse
                (List.replicate (b0 + 1) Step.gapY)
                (xs'.take ((t.reverse.map xConsumed).sum)) ys'
                (xs'.drop ((t.reverse.map xConsumed).sum)) []
                none hvt
              rw [List.take_append_drop, List.append_nil] at hNew
              have hNewInner :
                  scoreWalk sc (List.replicate (b0 + 1) Step.gapY)
                    (xs'.drop ((t.reverse.map xConsumed).sum)) []
                    (lastPrev t.reverse none) =
                  gapYCost sc (lastPrev t.reverse none) +
                    ((b0 + 1 : Nat) : Int) * sc.gapExtend -
                      sc.gapExtend := by
                rw [scoreWalk_replicate_gapY sc (b0 + 1)
                  (xs'.drop ((t.reverse.map xConsumed).sum)) hdlen
                  (lastPrev t.reverse none),
                  if_neg (by omega : ¬ b0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hNewInner] at hNew
              have hrevNew :
                  (List.replicate (b0 + 1) Step.gapY ++ t).reverse =
                    t.reverse ++ List.replicate (b0 + 1) Step.gapY := by
                rw [List.reverse_append, List.reverse_replicate]
              rw [hexp, hexp, hrev, hrevNew, hOld, hNew, hlxI, hlyI, hxprod, hyprod]
              have hdm := diagCost_le_match sc hr z y
              have hgge := gapYCost_ge_open sc hO (lastPrev t.reverse none)
              have hgdiag := gapYCost_diag_eq sc
              omega
          | gapX =>
              have hr' : r' = List.replicate b0 .gapY ++ t := by
                simp only [demoteWalk, hsp, Option.some.injEq,
                  Nat.add_sub_cancel] at h
                exact h.symm
              subst hr'
              simp only [xConsumed, yConsumed, xsum_replicate_gapY,
                ysum_replicate_gapY] at hvx hvy
              have hbx := sum_map_reverse xConsumed t
              have hby := sum_map_reverse yConsumed t
              have htb : (t.reverse.map yConsumed).sum = ys'.length := by
                simp at hvy; omega
              have hta : (t.reverse.map xConsumed).sum + b0 =
                  xs'.length := by
                simp at hvx; omega
              have hvt : IsMonotoneWalk t.reverse
                  (xs'.take ((t.reverse.map xConsumed).sum)) ys' := by
                refine ⟨?_, htb⟩
                rw [List.length_take]
                omega
              have hdlen :
                  (xs'.drop ((t.reverse.map xConsumed).sum)).length =
                    b0 := by
                rw [List.length_drop]; omega
              -- OLD score
              have hOld := scoreWalk_append sc t.reverse
                (Step.gapX :: List.replicate (b0 + 1) Step.gapY)
                (xs'.take ((t.reverse.map xConsumed).sum)) ys'
                (xs'.drop ((t.reverse.map xConsumed).sum) ++ [x]) [y]
                none hvt
              rw [← List.append_assoc, List.take_append_drop] at hOld
              have hOldInner :
                  scoreWalk sc
                    (Step.gapX :: List.replicate (b0 + 1) Step.gapY)
                    (xs'.drop ((t.reverse.map xConsumed).sum) ++ [x]) [y]
                    (lastPrev t.reverse none) =
                  gapXCost sc (lastPrev t.reverse none) +
                    (gapYCost sc (some .gapX) +
                      ((b0 + 1 : Nat) : Int) * sc.gapExtend -
                        sc.gapExtend) := by
                rw [scoreWalk_gapX_cons,
                  scoreWalk_replicate_gapY sc (b0 + 1)
                    (xs'.drop ((t.reverse.map xConsumed).sum) ++ [x])
                    (by simp; omega) (some .gapX),
                  if_neg (by omega : ¬ b0 + 1 = 0),
                  Int.sub_mul, Int.one_mul]
                omega
              rw [hOldInner] at hOld
              -- NEW score
              have hNew := scoreWalk_append sc t.reverse
                (List.replicate b0 Step.gapY)
                (xs'.take ((t.reverse.map xConsumed).sum)) ys'
                (xs'.drop ((t.reverse.map xConsumed).sum)) []
                none hvt
              rw [List.take_append_drop, List.append_nil] at hNew
              have hNewLB :
                  gapYCost sc (lastPrev t.reverse none) +
                      ((b0 : Nat) : Int) * sc.gapExtend - sc.gapExtend ≤
                    scoreWalk sc (List.replicate b0 Step.gapY)
                      (xs'.drop ((t.reverse.map xConsumed).sum)) []
                      (lastPrev t.reverse none) := by
                rw [scoreWalk_replicate_gapY sc b0
                  (xs'.drop ((t.reverse.map xConsumed).sum)) hdlen
                  (lastPrev t.reverse none)]
                by_cases h0 : b0 = 0
                · rw [if_pos h0]
                  have hz : ((b0 : Nat) : Int) * sc.gapExtend = 0 := by
                    rw [h0]; omega
                  have hle := gapYCost_le_extend sc hO
                    (lastPrev t.reverse none)
                  omega
                · rw [if_neg h0, Int.sub_mul, Int.one_mul]
                  omega
              have hprodE : ((b0 + 1 : Nat) : Int) * sc.gapExtend =
                  ((b0 : Nat) : Int) * sc.gapExtend + sc.gapExtend := by
                rw [show ((b0 + 1 : Nat) : Int) = ((b0 : Nat) : Int) + 1
                  from by omega, Int.add_mul, Int.one_mul]
              have hrevNew :
                  (List.replicate b0 Step.gapY ++ t).reverse =
                    t.reverse ++ List.replicate b0 Step.gapY := by
                rw [List.reverse_append, List.reverse_replicate]
              rw [hexp, hexp, hrev, hrevNew, hOld, hNew, hlxI, hlyI,
                hxprod, hyprod]
              have hgge := gapYCost_ge_open sc hO (lastPrev t.reverse none)
              have hgle := gapXCost_le_extend sc hO (lastPrev t.reverse none)
              have hggx := gapYCost_gapX_eq sc
              omega

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 3: every cell operation preserves genuineness
-- ══════════════════════════════════════════════════════════════════

theorem take_snoc {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

theorem lastPrev_reverse_none (w : List Step) :
    lastPrev w.reverse none = w.head? := by
  cases w with
  | nil => rfl
  | cons s r => rw [List.reverse_cons, lastPrev_snoc]; rfl

/-- The head character of a stored suffix is the indexed character. -/
theorem head_of_drop {α : Type} (l : List α) (i : Nat) (a : α)
    (rest : List α) (h : l.drop i = a :: rest) :
    i < l.length ∧ l[i]? = some a ∧ l.drop (i + 1) = rest := by
  have h1 : (l.drop i)[0]? = some a := by rw [h]; rfl
  rw [List.getElem?_drop] at h1
  simp only [Nat.add_zero] at h1
  have h2 : i < l.length := by
    rcases Nat.lt_or_ge i l.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h1
      simp at h1
  refine ⟨h2, h1, ?_⟩
  rw [← List.tail_drop, h]
  rfl

theorem demoteCell_sound (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : demoteCell xs ys c = some c') :
    CellOK sc xs ys p c' ∧ c'.off + 1 = c.off ∧ c'.joff + 1 = c.joff := by
  cases hi : c.off with
  | zero => simp [demoteCell, hi] at h
  | succ i =>
      cases hj : c.joff with
      | zero => simp [demoteCell, hi, hj] at h
      | succ j =>
          cases hdw : demoteWalk c.walk with
          | none => simp [demoteCell, hi, hj, hdw] at h
          | some w =>
              simp only [demoteCell, hi, hj, hdw,
                Option.some.injEq] at h
              have hxi : i < xs.length := by
                have := hok.hoff; omega
              have hyj : j < ys.length := by
                have := hok.hjoff; omega
              have htx := take_snoc xs i hxi
              have hty := take_snoc ys j hyj
              have hvold := hok.hvalid
              have hpold := hok.hpen
              rw [hi, hj, htx, hty] at hvold hpold
              obtain ⟨hval', hpen'⟩ := demoteWalk_pen sc hr c.walk w
                (xs.take i) (ys.take j) xs[i] ys[j] hdw hvold
              subst h
              refine ⟨⟨rfl, rfl, ?_, ?_, hval', ?_⟩, rfl, rfl⟩
              · show i ≤ xs.length
                omega
              · show j ≤ ys.length
                omega
              · show penOf sc w.reverse (xs.take i) (ys.take j) ≤ p
                omega

/-- Core accounting for a gap-in-x push: exact fields and the exact
penalty increment. -/
theorem pushGapX_core (sc : Scoring) (xs ys : List Char)
    (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapX c = some c') :
    c' = ⟨c.off, c.joff + 1, c.xsRem, ys.drop (c.joff + 1),
      .gapX :: c.walk⟩ ∧
    c.joff < ys.length ∧
    IsMonotoneWalk c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) ∧
    penOf sc c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if c.walk.head? = some .gapX then wfaPe sc else wfaPo sc) := by
  cases hyr : c.ysRem with
  | nil => simp [pushGapX, hyr] at h
  | cons y yr =>
      simp only [pushGapX, hyr, Option.some.injEq] at h
      obtain ⟨hlt, hget, hdrop⟩ := head_of_drop ys c.joff y yr
        (by rw [← hok.hys, hyr])
      have hy : ys[c.joff] = y := by
        rw [List.getElem?_eq_getElem hlt] at hget
        exact Option.some.inj hget
      have hty := take_snoc ys c.joff hlt
      rw [hy] at hty
      subst h
      have hv' : IsMonotoneWalk (Step.gapX :: c.walk).reverse
          (xs.take c.off) (ys.take (c.joff + 1)) := by
        rw [List.reverse_cons, hty]
        exact isMonotoneWalk_snoc_gapX c.walk.reverse _ _ y hok.hvalid
      refine ⟨by rw [hdrop], hlt, hv', ?_⟩
      show penOf sc (Step.gapX :: c.walk).reverse (xs.take c.off)
        (ys.take (c.joff + 1)) = _
      rw [List.reverse_cons, hty,
        penOf_snoc_gapX sc c.walk.reverse (xs.take c.off)
          (ys.take c.joff) y hok.hvalid,
        lastPrev_reverse_none]

theorem pushGapY_core (sc : Scoring) (xs ys : List Char)
    (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapY c = some c') :
    c' = ⟨c.off + 1, c.joff, xs.drop (c.off + 1), c.ysRem,
      .gapY :: c.walk⟩ ∧
    c.off < xs.length ∧
    IsMonotoneWalk c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) ∧
    penOf sc c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if c.walk.head? = some .gapY then wfaPe sc else wfaPo sc) := by
  cases hxr : c.xsRem with
  | nil => simp [pushGapY, hxr] at h
  | cons x xr =>
      simp only [pushGapY, hxr, Option.some.injEq] at h
      obtain ⟨hlt, hget, hdrop⟩ := head_of_drop xs c.off x xr
        (by rw [← hok.hxs, hxr])
      have hx : xs[c.off] = x := by
        rw [List.getElem?_eq_getElem hlt] at hget
        exact Option.some.inj hget
      have htx := take_snoc xs c.off hlt
      rw [hx] at htx
      subst h
      have hv' : IsMonotoneWalk (Step.gapY :: c.walk).reverse
          (xs.take (c.off + 1)) (ys.take c.joff) := by
        rw [List.reverse_cons, htx]
        exact isMonotoneWalk_snoc_gapY c.walk.reverse _ _ x hok.hvalid
      refine ⟨by rw [hdrop], hlt, hv', ?_⟩
      show penOf sc (Step.gapY :: c.walk).reverse (xs.take (c.off + 1))
        (ys.take c.joff) = _
      rw [List.reverse_cons, htx,
        penOf_snoc_gapY sc c.walk.reverse (xs.take c.off)
          (ys.take c.joff) x hok.hvalid,
        lastPrev_reverse_none]

theorem pushDiag_core (sc : Scoring) (xs ys : List Char)
    (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushDiag c = some c') :
    c' = ⟨c.off + 1, c.joff + 1, xs.drop (c.off + 1),
      ys.drop (c.joff + 1), .diag :: c.walk⟩ ∧
    c.off < xs.length ∧ c.joff < ys.length ∧
    IsMonotoneWalk c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) ∧
    penOf sc c'.walk.reverse (xs.take c'.off) (ys.take c'.joff) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if xs[c.off]? = ys[c.joff]? then 0 else wfaPx sc) := by
  cases hxr : c.xsRem with
  | nil => simp [pushDiag, hxr] at h
  | cons x xr =>
      cases hyr : c.ysRem with
      | nil => simp [pushDiag, hxr, hyr] at h
      | cons y yr =>
          simp only [pushDiag, hxr, hyr, Option.some.injEq] at h
          obtain ⟨hltx, hgetx, hdropx⟩ := head_of_drop xs c.off x xr
            (by rw [← hok.hxs, hxr])
          obtain ⟨hlty, hgety, hdropy⟩ := head_of_drop ys c.joff y yr
            (by rw [← hok.hys, hyr])
          have hx : xs[c.off] = x := by
            rw [List.getElem?_eq_getElem hltx] at hgetx
            exact Option.some.inj hgetx
          have hy : ys[c.joff] = y := by
            rw [List.getElem?_eq_getElem hlty] at hgety
            exact Option.some.inj hgety
          have htx := take_snoc xs c.off hltx
          have hty := take_snoc ys c.joff hlty
          rw [hx] at htx
          rw [hy] at hty
          subst h
          have hv' : IsMonotoneWalk (Step.diag :: c.walk).reverse
              (xs.take (c.off + 1)) (ys.take (c.joff + 1)) := by
            rw [List.reverse_cons, htx, hty]
            exact isMonotoneWalk_snoc_diag c.walk.reverse _ _ x y
              hok.hvalid
          refine ⟨by rw [hdropx, hdropy], hltx, hlty, hv', ?_⟩
          show penOf sc (Step.diag :: c.walk).reverse
            (xs.take (c.off + 1)) (ys.take (c.joff + 1)) = _
          rw [List.reverse_cons, htx, hty,
            penOf_snoc_diag sc c.walk.reverse (xs.take c.off)
              (ys.take c.joff) x y hok.hvalid, hgetx, hgety]
          simp only [Option.some.injEq]

/-- Penalty increments are capped by the opening charge. -/
theorem incr_le_po (sc : Scoring) (hr : ReasonableScoring sc)
    (b : Bool)  :
    (if b then wfaPe sc else wfaPo sc) ≤ wfaPo sc := by
  have := hr.open_neg
  cases b <;> simp [wfaPe, wfaPo] <;> omega

/-- Packaged soundness: any gap-in-x push (charged the opening
penalty) or an extension push from a gap-in-x-ending cell (charged
the extension penalty). -/
theorem pushGapX_sound_po (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapX c = some c') :
    CellOK sc xs ys (p + wfaPo sc) c' ∧
    c'.walk.head? = some .gapX ∧ c'.off = c.off ∧
    c'.joff = c.joff + 1 := by
  obtain ⟨hc', hlt, hv', hp'⟩ := pushGapX_core sc xs ys c c' p hok h
  have hif : (if c.walk.head? = some .gapX then wfaPe sc
      else wfaPo sc) ≤ wfaPo sc := by
    have := hr.open_neg
    by_cases hb : c.walk.head? = some .gapX <;>
      simp only [hb, if_pos, if_neg, if_true, if_false, wfaPe, wfaPo] <;>
      omega
  subst hc'
  have h1 := hok.hoff
  have h2 := hok.hpen
  have hp2 : penOf sc (Step.gapX :: c.walk).reverse (xs.take c.off)
      (ys.take (c.joff + 1)) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if c.walk.head? = some Step.gapX then wfaPe sc
          else wfaPo sc) := hp'
  refine ⟨⟨hok.hxs, rfl, ?_, ?_, hv', ?_⟩, rfl, rfl, rfl⟩
  · show c.off ≤ xs.length; omega
  · show c.joff + 1 ≤ ys.length; omega
  · show penOf sc (Step.gapX :: c.walk).reverse (xs.take c.off)
      (ys.take (c.joff + 1)) ≤ p + wfaPo sc
    omega

theorem pushGapX_sound_pe (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapX c = some c')
    (hend : c.walk.head? = some .gapX) :
    CellOK sc xs ys (p + wfaPe sc) c' ∧
    c'.walk.head? = some .gapX ∧ c'.off = c.off ∧
    c'.joff = c.joff + 1 := by
  obtain ⟨hc', hlt, hv', hp'⟩ := pushGapX_core sc xs ys c c' p hok h
  rw [if_pos hend] at hp'
  subst hc'
  have h1 := hok.hoff
  have h2 := hok.hpen
  have hp2 : penOf sc (Step.gapX :: c.walk).reverse (xs.take c.off)
      (ys.take (c.joff + 1)) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        wfaPe sc := hp'
  refine ⟨⟨hok.hxs, rfl, ?_, ?_, hv', ?_⟩, rfl, rfl, rfl⟩
  · show c.off ≤ xs.length; omega
  · show c.joff + 1 ≤ ys.length; omega
  · show penOf sc (Step.gapX :: c.walk).reverse (xs.take c.off)
      (ys.take (c.joff + 1)) ≤ p + wfaPe sc
    omega

theorem pushGapY_sound_po (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapY c = some c') :
    CellOK sc xs ys (p + wfaPo sc) c' ∧
    c'.walk.head? = some .gapY ∧ c'.off = c.off + 1 ∧
    c'.joff = c.joff := by
  obtain ⟨hc', hlt, hv', hp'⟩ := pushGapY_core sc xs ys c c' p hok h
  have hif : (if c.walk.head? = some .gapY then wfaPe sc
      else wfaPo sc) ≤ wfaPo sc := by
    have := hr.open_neg
    by_cases hb : c.walk.head? = some .gapY <;>
      simp only [hb, if_pos, if_neg, if_true, if_false, wfaPe, wfaPo] <;>
      omega
  subst hc'
  have h1 := hok.hjoff
  have h2 := hok.hpen
  have hp2 : penOf sc (Step.gapY :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take c.joff) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if c.walk.head? = some Step.gapY then wfaPe sc
          else wfaPo sc) := hp'
  refine ⟨⟨rfl, hok.hys, ?_, ?_, hv', ?_⟩, rfl, rfl, rfl⟩
  · show c.off + 1 ≤ xs.length; omega
  · show c.joff ≤ ys.length; omega
  · show penOf sc (Step.gapY :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take c.joff) ≤ p + wfaPo sc
    omega

theorem pushGapY_sound_pe (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c) (h : pushGapY c = some c')
    (hend : c.walk.head? = some .gapY) :
    CellOK sc xs ys (p + wfaPe sc) c' ∧
    c'.walk.head? = some .gapY ∧ c'.off = c.off + 1 ∧
    c'.joff = c.joff := by
  obtain ⟨hc', hlt, hv', hp'⟩ := pushGapY_core sc xs ys c c' p hok h
  rw [if_pos hend] at hp'
  subst hc'
  have h1 := hok.hjoff
  have h2 := hok.hpen
  have hp2 : penOf sc (Step.gapY :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take c.joff) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        wfaPe sc := hp'
  refine ⟨⟨rfl, hok.hys, ?_, ?_, hv', ?_⟩, rfl, rfl, rfl⟩
  · show c.off + 1 ≤ xs.length; omega
  · show c.joff ≤ ys.length; omega
  · show penOf sc (Step.gapY :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take c.joff) ≤ p + wfaPe sc
    omega

theorem pushDiag_sound_px (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c c' : WCell) (p : Int)
    (hpx : 0 ≤ wfaPx sc)
    (hok : CellOK sc xs ys p c) (h : pushDiag c = some c') :
    CellOK sc xs ys (p + wfaPx sc) c' ∧
    c'.off = c.off + 1 ∧ c'.joff = c.joff + 1 := by
  obtain ⟨hc', hltx, hlty, hv', hp'⟩ := pushDiag_core sc xs ys c c' p
    hok h
  have hif : (if xs[c.off]? = ys[c.joff]? then (0 : Int)
      else wfaPx sc) ≤ wfaPx sc := by
    by_cases hb : xs[c.off]? = ys[c.joff]? <;>
      simp only [hb, if_pos, if_neg, if_true, if_false] <;> omega
  subst hc'
  have h2 := hok.hpen
  have hp2 : penOf sc (Step.diag :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take (c.joff + 1)) =
      penOf sc c.walk.reverse (xs.take c.off) (ys.take c.joff) +
        (if xs[c.off]? = ys[c.joff]? then 0 else wfaPx sc) := hp'
  refine ⟨⟨rfl, rfl, ?_, ?_, hv', ?_⟩, rfl, rfl⟩
  · show c.off + 1 ≤ xs.length; omega
  · show c.joff + 1 ≤ ys.length; omega
  · show penOf sc (Step.diag :: c.walk).reverse (xs.take (c.off + 1))
      (ys.take (c.joff + 1)) ≤ p + wfaPx sc
    omega

/-- `stepWith` soundness: a produced cell is genuine at the pushed
charge, whether or not the boundary demotion fired. -/
theorem stepWith_sound (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char)
    (push : WCell → Option WCell) (q : Int)
    (hpush : ∀ (c c' : WCell) (p : Int), CellOK sc xs ys p c →
      push c = some c' → CellOK sc xs ys (p + q) c')
    (oc : Option WCell) (c' : WCell) (p : Int)
    (hok : ∀ c, oc = some c → CellOK sc xs ys p c)
    (h : stepWith push xs ys oc = some c') :
    CellOK sc xs ys (p + q) c' := by
  cases oc with
  | none => simp [stepWith] at h
  | some c =>
      have hc := hok c rfl
      simp only [stepWith] at h
      cases hp : push c with
      | some r =>
          rw [hp] at h
          simp at h
          subst h
          exact hpush c r p hc hp
      | none =>
          rw [hp] at h
          simp only [Option.bind] at h
          cases hd : demoteCell xs ys c with
          | none => rw [hd] at h; simp at h
          | some d =>
              rw [hd] at h
              simp only [Option.bind_some] at h
              obtain ⟨hdok, _, _⟩ := demoteCell_sound sc hr xs ys c d p
                hc hd
              exact hpush d c' p hdok h

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 3b: free extension is sound and lands on a closed cell
-- ══════════════════════════════════════════════════════════════════

/-- A cell whose suffix heads do not match (or have run out). -/
def ExtClosed (c : WCell) : Prop :=
  ∀ x xr y yr, c.xsRem = x :: xr → c.ysRem = y :: yr → ¬ x = y

theorem extendGo_spec (sc : Scoring) (xs ys : List Char) (p : Int) :
    ∀ (xr : List Char) (yr : List Char) (i j : Nat) (w : List Step),
      CellOK sc xs ys p ⟨i, j, xr, yr, w⟩ →
      CellOK sc xs ys p (extendGo i j w xr yr) ∧
      ExtClosed (extendGo i j w xr yr) ∧
      i ≤ (extendGo i j w xr yr).off ∧
      (extendGo i j w xr yr).off + j = (extendGo i j w xr yr).joff + i := by
  intro xr
  induction xr with
  | nil =>
      intro yr i j w hok
      refine ⟨hok, ?_, by simp [extendGo], by simp [extendGo]; omega⟩
      intro x xr' y yr' hx hy
      simp [extendGo] at hx
  | cons x xr ih =>
      intro yr i j w hok
      cases yr with
      | nil =>
          refine ⟨hok, ?_, by simp [extendGo], by simp [extendGo]; omega⟩
          intro x' xr' y yr' hx hy
          simp [extendGo] at hy
      | cons y yr =>
          by_cases hxy : x = y
          · rw [show extendGo i j w (x :: xr) (y :: yr) =
              extendGo (i + 1) (j + 1) (.diag :: w) xr yr from by
                rw [extendGo, if_pos hxy]]
            obtain ⟨hltx, hgetx, hdropx⟩ := head_of_drop xs i x xr
              (by rw [← hok.hxs])
            obtain ⟨hlty, hgety, hdropy⟩ := head_of_drop ys j y yr
              (by rw [← hok.hys])
            have hgx : xs[i] = x := by
              rw [List.getElem?_eq_getElem hltx] at hgetx
              exact Option.some.inj hgetx
            have hgy : ys[j] = y := by
              rw [List.getElem?_eq_getElem hlty] at hgety
              exact Option.some.inj hgety
            have hok' : CellOK sc xs ys p
                ⟨i + 1, j + 1, xr, yr, .diag :: w⟩ := by
              have htx := take_snoc xs i hltx
              have hty := take_snoc ys j hlty
              rw [hgx] at htx
              rw [hgy] at hty
              have hv' : IsMonotoneWalk (Step.diag :: w).reverse
                  (xs.take (i + 1)) (ys.take (j + 1)) := by
                rw [List.reverse_cons, htx, hty]
                exact isMonotoneWalk_snoc_diag w.reverse _ _ x y
                  hok.hvalid
              have hp' : penOf sc (Step.diag :: w).reverse
                  (xs.take (i + 1)) (ys.take (j + 1)) =
                  penOf sc w.reverse (xs.take i) (ys.take j) := by
                rw [List.reverse_cons, htx, hty,
                  penOf_snoc_diag sc w.reverse (xs.take i) (ys.take j)
                    x y hok.hvalid, if_pos hxy]
                omega
              have hpen : penOf sc w.reverse (xs.take i)
                  (ys.take j) ≤ p := hok.hpen
              refine ⟨hdropx.symm, hdropy.symm, ?_, ?_, hv', ?_⟩
              · show i + 1 ≤ xs.length; omega
              · show j + 1 ≤ ys.length; omega
              · show penOf sc (Step.diag :: w).reverse
                  (xs.take (i + 1)) (ys.take (j + 1)) ≤ p
                omega
            obtain ⟨h1, h2, h3, h4⟩ := ih yr (i + 1) (j + 1)
              (.diag :: w) hok'
            exact ⟨h1, h2, by omega, by omega⟩
          · rw [show extendGo i j w (x :: xr) (y :: yr) =
              (⟨i, j, x :: xr, y :: yr, w⟩ : WCell) from by
                rw [extendGo, if_neg hxy]]
            refine ⟨hok, ?_, by show i ≤ i; omega,
              by show i + j = j + i; omega⟩
            intro x' xr' y' yr' hx hy
            have hx' : x :: xr = x' :: xr' := hx
            have hy' : y :: yr = y' :: yr' := hy
            have hxx : x = x' := by injection hx'
            have hyy : y = y' := by injection hy'
            rw [← hxx, ← hyy]
            exact hxy

theorem extendCell_spec (sc : Scoring) (xs ys : List Char) (p : Int)
    (c : WCell) (hok : CellOK sc xs ys p c) :
    CellOK sc xs ys p (extendCell c) ∧ ExtClosed (extendCell c) ∧
    c.off ≤ (extendCell c).off ∧
    (extendCell c).off + c.joff = (extendCell c).joff + c.off := by
  have := extendGo_spec sc xs ys p c.xsRem c.ysRem c.off c.joff c.walk
    (by exact hok)
  exact this

/-- `betterCell` only ever returns one of its arguments. -/
theorem betterCell_cases (a b : Option WCell) (c : WCell)
    (h : betterCell a b = some c) :
    a = some c ∨ b = some c := by
  cases a with
  | none => right; exact h
  | some a' =>
      cases b with
      | none => left; exact h
      | some b' =>
          simp only [betterCell] at h
          by_cases hc : b'.off ≤ a'.off
          · rw [if_pos hc] at h; left; exact h
          · rw [if_neg hc] at h; right; exact h

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 5a: `stepWith` soundness at the three charges
-- ══════════════════════════════════════════════════════════════════

theorem CellOK.mono (sc : Scoring) (xs ys : List Char) {p q : Int}
    {c : WCell} (h : CellOK sc xs ys p c) (hpq : p ≤ q) :
    CellOK sc xs ys q c := by
  refine ⟨h.hxs, h.hys, h.hoff, h.hjoff, h.hvalid, ?_⟩
  have := h.hpen
  omega

theorem head_replicate_succ_append (s : Step) (a : Nat)
    (t : List Step) :
    (List.replicate (a + 1) s ++ t).head? = some s := by
  simp [List.replicate_succ]

/-- Any-source gap-in-x step: charged the opening penalty. -/
theorem stepWith_gapX_po (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c0 c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c0)
    (h : stepWith pushGapX xs ys (some c0) = some c') :
    CellOK sc xs ys (p + wfaPo sc) c' ∧
    c'.walk.head? = some .gapX ∧
    c'.joff + c0.off = c'.off + c0.joff + 1 := by
  simp only [stepWith] at h
  cases hp : pushGapX c0 with
  | some r =>
      rw [hp] at h
      simp at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := pushGapX_sound_po sc hr xs ys c0 r p
        hok hp
      exact ⟨h1, h2, by omega⟩
  | none =>
      rw [hp] at h
      cases hd : demoteCell xs ys c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          obtain ⟨hdok, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c0 d p
            hok hd
          obtain ⟨h1, h2, h3, h4⟩ := pushGapX_sound_po sc hr xs ys d c'
            p hdok h
          exact ⟨h1, h2, by omega⟩

theorem stepWith_gapY_po (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c0 c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c0)
    (h : stepWith pushGapY xs ys (some c0) = some c') :
    CellOK sc xs ys (p + wfaPo sc) c' ∧
    c'.walk.head? = some .gapY ∧
    c'.joff + c0.off + 1 = c'.off + c0.joff := by
  simp only [stepWith] at h
  cases hp : pushGapY c0 with
  | some r =>
      rw [hp] at h
      simp at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := pushGapY_sound_po sc hr xs ys c0 r p
        hok hp
      exact ⟨h1, h2, by omega⟩
  | none =>
      rw [hp] at h
      cases hd : demoteCell xs ys c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          obtain ⟨hdok, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c0 d p
            hok hd
          obtain ⟨h1, h2, h3, h4⟩ := pushGapY_sound_po sc hr xs ys d c'
            p hdok h
          exact ⟨h1, h2, by omega⟩

theorem stepWith_diag_px (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c0 c' : WCell) (p : Int)
    (hpx : 0 ≤ wfaPx sc)
    (hok : CellOK sc xs ys p c0)
    (h : stepWith pushDiag xs ys (some c0) = some c') :
    CellOK sc xs ys (p + wfaPx sc) c' ∧
    c'.joff + c0.off = c'.off + c0.joff := by
  simp only [stepWith] at h
  cases hp : pushDiag c0 with
  | some r =>
      rw [hp] at h
      simp at h
      subst h
      obtain ⟨h1, h2, h3⟩ := pushDiag_sound_px sc hr xs ys c0 r p hpx
        hok hp
      exact ⟨h1, by omega⟩
  | none =>
      rw [hp] at h
      cases hd : demoteCell xs ys c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          obtain ⟨hdok, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c0 d p
            hok hd
          obtain ⟨h1, h2, h3⟩ := pushDiag_sound_px sc hr xs ys d c' p
            hpx hdok h
          exact ⟨h1, by omega⟩

/-- Extension-source gap-in-x step, charged only the extension
penalty.  The delicate branch: if the boundary demotion stripped the
trailing gap run entirely, the removed columns contained a full
opening charge, which pays for the new opening. -/
theorem stepWith_gapX_pe (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c0 c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c0) (hend : c0.walk.head? = some .gapX)
    (h : stepWith pushGapX xs ys (some c0) = some c') :
    CellOK sc xs ys (p + wfaPe sc) c' ∧
    c'.walk.head? = some .gapX ∧
    c'.joff + c0.off = c'.off + c0.joff + 1 := by
  have hE := hr.extend_neg
  have hO := hr.open_neg
  have hM := hr.match_pos
  simp only [stepWith] at h
  cases hp : pushGapX c0 with
  | some r =>
      rw [hp] at h
      simp at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := pushGapX_sound_pe sc hr xs ys c0 r p
        hok hp hend
      exact ⟨h1, h2, by omega⟩
  | none =>
      rw [hp] at h
      cases hd : demoteCell xs ys c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          by_cases hde : d.walk.head? = some .gapX
          · obtain ⟨hdok, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c0
              d p hok hd
            obtain ⟨h1, h2, h3, h4⟩ := pushGapX_sound_pe sc hr xs ys d
              c' p hdok h hde
            exact ⟨h1, h2, by omega⟩
          · -- the demotion stripped the whole trailing gap run
            obtain ⟨rest, hwalk⟩ : ∃ rest, c0.walk = .gapX :: rest := by
              cases hw : c0.walk with
              | nil => rw [hw] at hend; simp at hend
              | cons s r0 =>
                  rw [hw] at hend
                  simp at hend
                  exact ⟨r0, by rw [hend]⟩
            -- destructure the demotion
            cases hi : c0.off with
            | zero => simp [demoteCell, hi] at hd
            | succ i0 =>
                cases hj : c0.joff with
                | zero => simp [demoteCell, hi, hj] at hd
                | succ j0 =>
                    cases hdw : demoteWalk c0.walk with
                    | none => simp [demoteCell, hi, hj, hdw] at hd
                    | some w =>
                        simp only [demoteCell, hi, hj, hdw,
                          Option.some.injEq] at hd
                        rw [hwalk] at hdw
                        rcases hsp : splitRun .gapX (.gapX :: rest)
                          with ⟨a, oe, t⟩
                        have ha : 1 ≤ a := by
                          have := splitRun_head .gapX rest
                          rw [hsp] at this
                          simp at this
                          omega
                        cases oe with
                        | none => simp [demoteWalk, hsp] at hdw
                        | some e =>
                            obtain ⟨hl, hne⟩ :=
                              splitRun_some _ _ _ _ _ hsp
                            cases e with
                            | gapX => exact absurd rfl hne
                            | diag =>
                                simp only [demoteWalk, hsp,
                                  Option.some.injEq] at hdw
                                exfalso
                                apply hde
                                rw [← hd]
                                obtain ⟨a0, rfl⟩ : ∃ a0, a = a0 + 1 :=
                                  ⟨a - 1, by omega⟩
                                rw [← hdw]
                                exact head_replicate_succ_append _ _ _
                            | gapY =>
                                simp only [demoteWalk, hsp,
                                  Option.some.injEq] at hdw
                                have ha1 : a = 1 := by
                                  rcases Nat.lt_or_ge a 2 with h2 | h2
                                  · omega
                                  · exfalso
                                    apply hde
                                    rw [← hd, ← hdw]
                                    obtain ⟨a1, ha1⟩ :
                                        ∃ a1, a - 1 = a1 + 1 :=
                                      ⟨a - 2, by omega⟩
                                    rw [ha1]
                                    exact head_replicate_succ_append
                                      _ _ _
                                subst ha1
                                simp only [Nat.sub_self,
                                  List.replicate_zero,
                                  List.nil_append] at hdw
                                subst hdw
                                -- c0.walk = gapX :: gapY :: t, d.walk = t
                                have hrest : rest = .gapY :: t := by
                                  have := hl
                                  simp [List.replicate_succ] at this
                                  exact this
                                -- penalty bookkeeping
                                have hxi : i0 < xs.length := by
                                  have := hok.hoff; omega
                                have hyj : j0 < ys.length := by
                                  have := hok.hjoff; omega
                                have htx := take_snoc xs i0 hxi
                                have hty := take_snoc ys j0 hyj
                                have hvold := hok.hvalid
                                rw [hwalk, hrest, hi, hj] at hvold
                                have hrev3 :
                                    (Step.gapX :: Step.gapY :: t).reverse
                                    = (t.reverse ++ [Step.gapY]) ++
                                      [Step.gapX] := by
                                  rw [List.reverse_cons,
                                    List.reverse_cons]
                                obtain ⟨hvx3, hvy3⟩ := hvold
                                rw [hrev3] at hvx3 hvy3
                                rw [List.length_take_of_le
                                  (by omega : i0 + 1 ≤ xs.length)] at hvx3
                                rw [List.length_take_of_le
                                  (by omega : j0 + 1 ≤ ys.length)] at hvy3
                                simp only [List.map_append,
                                  List.sum_append, List.map_cons,
                                  List.sum_cons, List.map_nil,
                                  List.sum_nil, xConsumed,
                                  yConsumed] at hvx3 hvy3
                                have hvt : IsMonotoneWalk t.reverse
                                    (xs.take i0) (ys.take j0) := by
                                  constructor
                                  · rw [List.length_take_of_le
                                      (by omega : i0 ≤ xs.length)]
                                    omega
                                  · rw [List.length_take_of_le
                                      (by omega : j0 ≤ ys.length)]
                                    omega
                                have hvmid : IsMonotoneWalk
                                    (t.reverse ++ [Step.gapY])
                                    (xs.take (i0 + 1)) (ys.take j0) := by
                                  constructor
                                  · simp only [List.map_append,
                                      List.sum_append, List.map_cons,
                                      List.sum_cons, List.map_nil,
                                      List.sum_nil, xConsumed]
                                    rw [List.length_take_of_le
                                      (by omega : i0 + 1 ≤ xs.length)]
                                    omega
                                  · simp only [List.map_append,
                                      List.sum_append, List.map_cons,
                                      List.sum_cons, List.map_nil,
                                      List.sum_nil, yConsumed]
                                    rw [List.length_take_of_le
                                      (by omega : j0 ≤ ys.length)]
                                    omega
                                have hpen1 := penOf_snoc_gapX sc
                                  (t.reverse ++ [Step.gapY])
                                  (xs.take (i0 + 1)) (ys.take j0)
                                  ys[j0] hvmid
                                rw [lastPrev_snoc] at hpen1
                                rw [if_neg (by simp)] at hpen1
                                have hpen2 := penOf_snoc_gapY sc
                                  t.reverse (xs.take i0) (ys.take j0)
                                  xs[i0] hvt
                                have hincr2 : (if lastPrev t.reverse
                                    none = some Step.gapY then wfaPe sc
                                    else wfaPo sc) ≥ wfaPe sc := by
                                  by_cases hb : lastPrev t.reverse none
                                      = some Step.gapY <;>
                                    simp only [hb, if_pos, if_neg,
                                      if_true, if_false, wfaPe,
                                      wfaPo] <;> omega
                                have hpold : penOf sc
                                    ((t.reverse ++ [Step.gapY]) ++
                                      [Step.gapX])
                                    (xs.take (i0 + 1))
                                    (ys.take j0 ++ [ys[j0]]) ≤ p := by
                                  have := hok.hpen
                                  rw [hwalk, hrest, hi, hj, hrev3,
                                    hty] at this
                                  exact this
                                have hpd : penOf sc t.reverse
                                    (xs.take i0) (ys.take j0) ≤
                                    p - wfaPo sc - wfaPe sc := by
                                  rw [← htx] at hpen2
                                  omega
                                have hdok2 : CellOK sc xs ys
                                    (p - wfaPo sc - wfaPe sc) d := by
                                  rw [← hd]
                                  refine ⟨rfl, rfl, ?_, ?_, hvt, hpd⟩
                                  · show i0 ≤ xs.length; omega
                                  · show j0 ≤ ys.length; omega
                                obtain ⟨h1, h2, h3, h4⟩ :=
                                  pushGapX_sound_po sc hr xs ys d c'
                                    (p - wfaPo sc - wfaPe sc) hdok2 h
                                refine ⟨h1.mono sc xs ys (by
                                  unfold wfaPe wfaPo wfaPe
                                  omega), h2, ?_⟩
                                have hdo : d.off = i0 := by rw [← hd]
                                have hdj : d.joff = j0 := by rw [← hd]
                                omega

theorem stepWith_gapY_pe (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (c0 c' : WCell) (p : Int)
    (hok : CellOK sc xs ys p c0) (hend : c0.walk.head? = some .gapY)
    (h : stepWith pushGapY xs ys (some c0) = some c') :
    CellOK sc xs ys (p + wfaPe sc) c' ∧
    c'.walk.head? = some .gapY ∧
    c'.joff + c0.off + 1 = c'.off + c0.joff := by
  have hE := hr.extend_neg
  have hO := hr.open_neg
  have hM := hr.match_pos
  simp only [stepWith] at h
  cases hp : pushGapY c0 with
  | some r =>
      rw [hp] at h
      simp at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := pushGapY_sound_pe sc hr xs ys c0 r p
        hok hp hend
      exact ⟨h1, h2, by omega⟩
  | none =>
      rw [hp] at h
      cases hd : demoteCell xs ys c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          by_cases hde : d.walk.head? = some .gapY
          · obtain ⟨hdok, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c0
              d p hok hd
            obtain ⟨h1, h2, h3, h4⟩ := pushGapY_sound_pe sc hr xs ys d
              c' p hdok h hde
            exact ⟨h1, h2, by omega⟩
          · obtain ⟨rest, hwalk⟩ : ∃ rest, c0.walk = .gapY :: rest := by
              cases hw : c0.walk with
              | nil => rw [hw] at hend; simp at hend
              | cons s r0 =>
                  rw [hw] at hend
                  simp at hend
                  exact ⟨r0, by rw [hend]⟩
            cases hi : c0.off with
            | zero => simp [demoteCell, hi] at hd
            | succ i0 =>
                cases hj : c0.joff with
                | zero => simp [demoteCell, hi, hj] at hd
                | succ j0 =>
                    cases hdw : demoteWalk c0.walk with
                    | none => simp [demoteCell, hi, hj, hdw] at hd
                    | some w =>
                        simp only [demoteCell, hi, hj, hdw,
                          Option.some.injEq] at hd
                        rw [hwalk] at hdw
                        rcases hsp : splitRun .gapY (.gapY :: rest)
                          with ⟨b, oe, t⟩
                        have hb : 1 ≤ b := by
                          have := splitRun_head .gapY rest
                          rw [hsp] at this
                          simp at this
                          omega
                        cases oe with
                        | none => simp [demoteWalk, hsp] at hdw
                        | some e =>
                            obtain ⟨hl, hne⟩ :=
                              splitRun_some _ _ _ _ _ hsp
                            cases e with
                            | gapY => exact absurd rfl hne
                            | diag =>
                                simp only [demoteWalk, hsp,
                                  Option.some.injEq] at hdw
                                exfalso
                                apply hde
                                rw [← hd]
                                obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 :=
                                  ⟨b - 1, by omega⟩
                                rw [← hdw]
                                exact head_replicate_succ_append _ _ _
                            | gapX =>
                                simp only [demoteWalk, hsp,
                                  Option.some.injEq] at hdw
                                have hb1 : b = 1 := by
                                  rcases Nat.lt_or_ge b 2 with h2 | h2
                                  · omega
                                  · exfalso
                                    apply hde
                                    rw [← hd, ← hdw]
                                    obtain ⟨b1, hb1⟩ :
                                        ∃ b1, b - 1 = b1 + 1 :=
                                      ⟨b - 2, by omega⟩
                                    rw [hb1]
                                    exact head_replicate_succ_append
                                      _ _ _
                                subst hb1
                                simp only [Nat.sub_self,
                                  List.replicate_zero,
                                  List.nil_append] at hdw
                                subst hdw
                                have hrest : rest = .gapX :: t := by
                                  have := hl
                                  simp [List.replicate_succ] at this
                                  exact this
                                have hxi : i0 < xs.length := by
                                  have := hok.hoff; omega
                                have hyj : j0 < ys.length := by
                                  have := hok.hjoff; omega
                                have htx := take_snoc xs i0 hxi
                                have hty := take_snoc ys j0 hyj
                                have hvold := hok.hvalid
                                rw [hwalk, hrest, hi, hj] at hvold
                                have hrev3 :
                                    (Step.gapY :: Step.gapX :: t).reverse
                                    = (t.reverse ++ [Step.gapX]) ++
                                      [Step.gapY] := by
                                  rw [List.reverse_cons,
                                    List.reverse_cons]
                                obtain ⟨hvx3, hvy3⟩ := hvold
                                rw [hrev3] at hvx3 hvy3
                                rw [List.length_take_of_le
                                  (by omega : i0 + 1 ≤ xs.length)] at hvx3
                                rw [List.length_take_of_le
                                  (by omega : j0 + 1 ≤ ys.length)] at hvy3
                                simp only [List.map_append,
                                  List.sum_append, List.map_cons,
                                  List.sum_cons, List.map_nil,
                                  List.sum_nil, xConsumed,
                                  yConsumed] at hvx3 hvy3
                                have hvt : IsMonotoneWalk t.reverse
                                    (xs.take i0) (ys.take j0) := by
                                  constructor
                                  · rw [List.length_take_of_le
                                      (by omega : i0 ≤ xs.length)]
                                    omega
                                  · rw [List.length_take_of_le
                                      (by omega : j0 ≤ ys.length)]
                                    omega
                                have hvmid : IsMonotoneWalk
                                    (t.reverse ++ [Step.gapX])
                                    (xs.take i0) (ys.take (j0 + 1)) := by
                                  constructor
                                  · simp only [List.map_append,
                                      List.sum_append, List.map_cons,
                                      List.sum_cons, List.map_nil,
                                      List.sum_nil, xConsumed]
                                    rw [List.length_take_of_le
                                      (by omega : i0 ≤ xs.length)]
                                    omega
                                  · simp only [List.map_append,
                                      List.sum_append, List.map_cons,
                                      List.sum_cons, List.map_nil,
                                      List.sum_nil, yConsumed]
                                    rw [List.length_take_of_le
                                      (by omega : j0 + 1 ≤ ys.length)]
                                    omega
                                have hpen1 := penOf_snoc_gapY sc
                                  (t.reverse ++ [Step.gapX])
                                  (xs.take i0) (ys.take (j0 + 1))
                                  xs[i0] hvmid
                                rw [lastPrev_snoc] at hpen1
                                rw [if_neg (by simp)] at hpen1
                                have hpen2 := penOf_snoc_gapX sc
                                  t.reverse (xs.take i0) (ys.take j0)
                                  ys[j0] hvt
                                have hpold : penOf sc
                                    ((t.reverse ++ [Step.gapX]) ++
                                      [Step.gapY])
                                    (xs.take i0 ++ [xs[i0]])
                                    (ys.take (j0 + 1)) ≤ p := by
                                  have := hok.hpen
                                  rw [hwalk, hrest, hi, hj, hrev3,
                                    htx] at this
                                  exact this
                                have hpd : penOf sc t.reverse
                                    (xs.take i0) (ys.take j0) ≤
                                    p - wfaPo sc - wfaPe sc := by
                                  rw [← hty] at hpen2
                                  have hincr2 : (if lastPrev t.reverse
                                      none = some Step.gapX then
                                      wfaPe sc else wfaPo sc) ≥
                                      wfaPe sc := by
                                    by_cases hbx : lastPrev t.reverse
                                        none = some Step.gapX <;>
                                      simp only [hbx, if_pos, if_neg,
                                        if_true, if_false, wfaPe,
                                        wfaPo] <;> omega
                                  omega
                                have hdok2 : CellOK sc xs ys
                                    (p - wfaPo sc - wfaPe sc) d := by
                                  rw [← hd]
                                  refine ⟨rfl, rfl, ?_, ?_, hvt, hpd⟩
                                  · show i0 ≤ xs.length; omega
                                  · show j0 ≤ ys.length; omega
                                obtain ⟨h1, h2, h3, h4⟩ :=
                                  pushGapY_sound_po sc hr xs ys d c'
                                    (p - wfaPo sc - wfaPe sc) hdok2 h
                                refine ⟨h1.mono sc xs ys (by
                                  unfold wfaPe wfaPo wfaPe
                                  omega), h2, ?_⟩
                                have hdo : d.off = i0 := by rw [← hd]
                                have hdj : d.joff = j0 := by rw [← hd]
                                omega

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 5b: front and level invariants
-- ══════════════════════════════════════════════════════════════════

/-- A sound front at level p: right length; every stored cell genuine,
on its diagonal (`t = k + m` becomes `joff + m = off + t`), and ending
in the required column type. -/
def FrontOK (sc : Scoring) (xs ys : List Char) (p : Int)
    (ends : Option Step) (f : WFront) : Prop :=
  f.length = xs.length + ys.length + 1 ∧
  ∀ (t : Nat) (c : WCell), f[t]? = some (some c) →
    CellOK sc xs ys p c ∧
    c.joff + xs.length = c.off + t ∧
    (∀ e, ends = some e → c.walk.head? = some e)

structure LevelOK (sc : Scoring) (xs ys : List Char) (p : Int)
    (lv : WLevel) : Prop where
  hmf : FrontOK sc xs ys p none lv.mf
  hxf : FrontOK sc xs ys p (some .gapX) lv.xf
  hyf : FrontOK sc xs ys p (some .gapY) lv.yf
  hclosed : ∀ (t : Nat) (c : WCell), lv.mf[t]? = some (some c) →
    ExtClosed c

/-- History soundness: entry d is the (fully sound) level
`p − 1 − d`, where p is the level about to be built.  The history may
be truncated to any window — only its entries are constrained. -/
abbrev HistOK (sc : Scoring) (xs ys : List Char) (p : Nat)
    (hist : List WLevel) : Prop :=
  ∀ (d : Nat) (lv : WLevel), hist[d]? = some lv →
    LevelOK sc xs ys ((p : Int) - 1 - (d : Int)) lv

theorem emptyFront_ok (sc : Scoring) (xs ys : List Char) (p : Int)
    (ends : Option Step) :
    FrontOK sc xs ys p ends
      (emptyFront (xs.length + ys.length + 1)) := by
  refine ⟨by simp [emptyFront], ?_⟩
  intro t c hc
  rw [emptyFront, List.getElem?_replicate] at hc
  by_cases ht : t < xs.length + ys.length + 1
  · rw [if_pos ht] at hc; simp at hc
  · rw [if_neg ht] at hc; simp at hc

theorem frontAt_ok (sc : Scoring) (xs ys : List Char) (p : Nat)
    (hist : List WLevel) (delta : Nat) (hdelta : 1 ≤ delta)
    (hh : HistOK sc xs ys p hist)
    (sel : WLevel → WFront) (ends : Option Step)
    (hsel : ∀ lv q, LevelOK sc xs ys q lv →
      FrontOK sc xs ys q ends (sel lv)) :
    FrontOK sc xs ys ((p : Int) - delta) ends
      (frontAt (xs.length + ys.length + 1) hist delta sel) := by
  rw [frontAt]
  cases hg : hist[delta - 1]? with
  | none => exact emptyFront_ok sc xs ys _ ends
  | some lv =>
      have hlv := hh (delta - 1) lv hg
      have heq : (p : Int) - 1 - ((delta - 1 : Nat) : Int) =
          (p : Int) - delta := by omega
      rw [heq] at hlv
      exact hsel lv _ hlv

-- Index bookkeeping for the three front transformers.
theorem shiftUp_some_cell (f : WFront) (t : Nat) (c : WCell)
    (h : (shiftUp f)[t]? = some (some c)) :
    ∃ t0, t = t0 + 1 ∧ f[t0]? = some (some c) := by
  cases t with
  | zero => simp [shiftUp] at h
  | succ t0 =>
      refine ⟨t0, rfl, ?_⟩
      simp only [shiftUp, List.getElem?_cons_succ] at h
      rw [List.getElem?_dropLast] at h
      by_cases hlt : t0 < f.length - 1
      · rw [if_pos hlt] at h; exact h
      · rw [if_neg hlt] at h; simp at h

theorem shiftDown_some_cell (f : WFront) (t : Nat) (c : WCell)
    (h : (shiftDown f)[t]? = some (some c)) :
    f[t + 1]? = some (some c) := by
  simp only [shiftDown] at h
  rw [List.getElem?_append] at h
  by_cases hlt : t < (f.drop 1).length
  · rw [if_pos hlt] at h
    rw [List.getElem?_drop] at h
    rw [show 1 + t = t + 1 from by omega] at h
    exact h
  · rw [if_neg hlt] at h
    cases hk : t - (f.drop 1).length with
    | zero => rw [hk] at h; simp at h
    | succ k => rw [hk] at h; simp at h

theorem map_stepWith_some (push : WCell → Option WCell)
    (xs ys : List Char) (f : WFront) (t : Nat) (c' : WCell)
    (h : (f.map (stepWith push xs ys))[t]? = some (some c')) :
    ∃ c0, f[t]? = some (some c0) ∧
      stepWith push xs ys (some c0) = some c' := by
  rw [List.getElem?_map] at h
  cases hf : f[t]? with
  | none => rw [hf] at h; simp at h
  | some o =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases o with
      | none => simp [stepWith] at h
      | some c0 => exact ⟨c0, rfl, h⟩

theorem zipWith_better_some (f g : WFront) (t : Nat) (c : WCell)
    (h : (List.zipWith betterCell f g)[t]? = some (some c)) :
    f[t]? = some (some c) ∨ g[t]? = some (some c) := by
  rw [List.getElem?_zipWith] at h
  cases hf : f[t]? with
  | none => rw [hf] at h; simp at h
  | some a =>
      cases hg : g[t]? with
      | none => rw [hf, hg] at h; simp at h
      | some b =>
          rw [hf, hg] at h
          simp only [Option.some.injEq] at h
          rcases betterCell_cases a b c h with rfl | rfl
          · left; rfl
          · right; rfl

theorem length_shiftUp (f : WFront) (h : 1 ≤ f.length) :
    (shiftUp f).length = f.length := by
  simp [shiftUp]
  omega

theorem length_shiftDown (f : WFront) (h : 1 ≤ f.length) :
    (shiftDown f).length = f.length := by
  simp [shiftDown]
  omega

-- The seed level is sound at level 0.
theorem seedLevel_sound (sc : Scoring) (xs ys : List Char) :
    LevelOK sc xs ys 0
      (seedLevel xs.length (xs.length + ys.length + 1) xs ys) := by
  have hseed : CellOK sc xs ys 0 (⟨0, 0, xs, ys, []⟩ : WCell) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show (0 : Nat) ≤ xs.length; omega
    · show (0 : Nat) ≤ ys.length; omega
    · show IsMonotoneWalk [] (xs.take 0) (ys.take 0)
      exact ⟨by simp, by simp⟩
    · show penOf sc [] (xs.take 0) (ys.take 0) ≤ 0
      simp [penOf, scoreWalk]
  obtain ⟨hext, hclosed, hoff, hdiag⟩ :=
    extendCell_spec sc xs ys 0 ⟨0, 0, xs, ys, []⟩ hseed
  have hcell : ∀ (t : Nat) (c : WCell),
      ((emptyFront (xs.length + ys.length + 1)).set xs.length
        (some (extendCell ⟨0, 0, xs, ys, []⟩)))[t]? =
          some (some c) →
      c = extendCell ⟨0, 0, xs, ys, []⟩ ∧ t = xs.length := by
    intro t c hc
    rw [List.getElem?_set] at hc
    by_cases hteq : xs.length = t
    · rw [if_pos hteq] at hc
      by_cases hlt : xs.length <
          (emptyFront (xs.length + ys.length + 1)).length
      · rw [if_pos hlt] at hc
        simp at hc
        exact ⟨hc.symm, hteq.symm⟩
      · exfalso
        apply hlt
        simp [emptyFront]
        omega
    · rw [if_neg hteq] at hc
      rw [emptyFront, List.getElem?_replicate] at hc
      by_cases ht : t < xs.length + ys.length + 1
      · rw [if_pos ht] at hc; simp at hc
      · rw [if_neg ht] at hc; simp at hc
  refine ⟨⟨?_, ?_⟩, emptyFront_ok sc xs ys 0 (some .gapX),
    emptyFront_ok sc xs ys 0 (some .gapY), ?_⟩
  · show ((emptyFront (xs.length + ys.length + 1)).set xs.length
      (some (extendCell ⟨0, 0, xs, ys, []⟩))).length = _
    simp [emptyFront]
  · intro t c hc
    obtain ⟨rfl, rfl⟩ := hcell t c hc
    refine ⟨hext, ?_, by intro e he; simp at he⟩
    show (extendCell ⟨0, 0, xs, ys, []⟩).joff + xs.length =
      (extendCell ⟨0, 0, xs, ys, []⟩).off + xs.length
    have h4 : (extendCell ⟨0, 0, xs, ys, []⟩).off +
        (⟨0, 0, xs, ys, []⟩ : WCell).joff =
        (extendCell ⟨0, 0, xs, ys, []⟩).joff +
        (⟨0, 0, xs, ys, []⟩ : WCell).off := hdiag
    have h5 : (⟨0, 0, xs, ys, []⟩ : WCell).joff = 0 := rfl
    have h6 : (⟨0, 0, xs, ys, []⟩ : WCell).off = 0 := rfl
    omega
  · intro t c hc
    obtain ⟨rfl, rfl⟩ := hcell t c hc
    exact hclosed

theorem histOK_singleton (sc : Scoring) (xs ys : List Char)
    (lv0 : WLevel) (h0 : LevelOK sc xs ys 0 lv0) :
    HistOK sc xs ys 1 [lv0] := by
  intro d lv hd
  cases d with
  | zero =>
      simp at hd
      subst hd
      simpa using h0
  | succ d => simp at hd

theorem histOK_take (sc : Scoring) (xs ys : List Char) (p k : Nat)
    (hist : List WLevel) (hh : HistOK sc xs ys p hist) :
    HistOK sc xs ys p (hist.take k) := by
  intro d lv hd
  rw [List.getElem?_take] at hd
  by_cases hdk : d < k
  · rw [if_pos hdk] at hd
    exact hh d lv hd
  · rw [if_neg hdk] at hd
    simp at hd

theorem histOK_cons (sc : Scoring) (xs ys : List Char) (p : Nat)
    (hist : List WLevel) (lv : WLevel)
    (hh : HistOK sc xs ys p hist)
    (hlv : LevelOK sc xs ys (p : Int) lv) :
    HistOK sc xs ys (p + 1) (lv :: hist) := by
  intro d lv' hd
  cases d with
  | zero =>
      simp at hd
      have heq : ((p + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int) =
          (p : Int) := by omega
      rw [heq, ← hd]
      exact hlv
  | succ d =>
      rw [List.getElem?_cons_succ] at hd
      have hlv' := hh d lv' hd
      have heq : ((p + 1 : Nat) : Int) - 1 - ((d + 1 : Nat) : Int) =
          (p : Int) - 1 - (d : Int) := by omega
      rw [heq]
      exact hlv'

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 5c: one wavefront step is sound; the loop is sound
-- ══════════════════════════════════════════════════════════════════

theorem map_extend_some (f : WFront) (t : Nat) (c' : WCell)
    (h : (f.map (Option.map extendCell))[t]? = some (some c')) :
    ∃ c1, f[t]? = some (some c1) ∧ c' = extendCell c1 := by
  rw [List.getElem?_map] at h
  cases hf : f[t]? with
  | none => rw [hf] at h; simp at h
  | some o =>
      rw [hf] at h
      cases o with
      | none => simp at h
      | some c1 =>
          simp at h
          exact ⟨c1, rfl, h.symm⟩

theorem nextLevel_sound (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc)
    (xs ys : List Char) (p : Nat) (hist : List WLevel)
    (hh : HistOK sc xs ys p hist) :
    LevelOK sc xs ys (p : Int)
      (nextLevel xs ys (xs.length + ys.length + 1)
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist) := by
  have hO := hr.open_neg
  have hpo1 : 1 ≤ wfaPo sc := by unfold wfaPo; omega
  have hpeC : (((wfaPe sc).toNat : Nat) : Int) = wfaPe sc := by omega
  have hpoC : (((wfaPo sc).toNat : Nat) : Int) = wfaPo sc := by omega
  have hpxC : (((wfaPx sc).toNat : Nat) : Int) = wfaPx sc := by omega
  have hpx0 : 0 ≤ wfaPx sc := by omega
  have hAx := frontAt_ok sc xs ys p hist (wfaPe sc).toNat (by omega)
    hh (·.xf) (some .gapX) (fun lv q h => h.hxf)
  have hBm := frontAt_ok sc xs ys p hist (wfaPo sc).toNat (by omega)
    hh (·.mf) none (fun lv q h => h.hmf)
  have hCy := frontAt_ok sc xs ys p hist (wfaPe sc).toNat (by omega)
    hh (·.yf) (some .gapY) (fun lv q h => h.hyf)
  have hEm := frontAt_ok sc xs ys p hist (wfaPx sc).toNat (by omega)
    hh (·.mf) none (fun lv q h => h.hmf)
  -- the new gap-in-x front
  have hxfOK : FrontOK sc xs ys (p : Int) (some .gapX)
      (List.zipWith betterCell
        (shiftUp ((frontAt (xs.length + ys.length + 1) hist
          (wfaPe sc).toNat (·.xf)).map (stepWith pushGapX xs ys)))
        (shiftUp ((frontAt (xs.length + ys.length + 1) hist
          (wfaPo sc).toNat (·.mf)).map (stepWith pushGapX xs ys)))) := by
    have l1 : ((frontAt (xs.length + ys.length + 1) hist
        (wfaPe sc).toNat (·.xf)).map (stepWith pushGapX xs ys)).length =
        xs.length + ys.length + 1 := by
      rw [List.length_map]; exact hAx.1
    have l2 : ((frontAt (xs.length + ys.length + 1) hist
        (wfaPo sc).toNat (·.mf)).map (stepWith pushGapX xs ys)).length =
        xs.length + ys.length + 1 := by
      rw [List.length_map]; exact hBm.1
    constructor
    · rw [List.length_zipWith, length_shiftUp _ (by omega),
        length_shiftUp _ (by omega), l1, l2]
      omega
    · intro t c' hc'
      rcases zipWith_better_some _ _ t c' hc' with hside | hside
      · obtain ⟨t0, rfl, hsrc⟩ := shiftUp_some_cell _ t c' hside
        obtain ⟨c0, hc0, hstep⟩ := map_stepWith_some _ xs ys _ t0 c'
          hsrc
        obtain ⟨hok0, hdiag0, hends0⟩ := hAx.2 t0 c0 hc0
        obtain ⟨hok', hhead', hdelta⟩ := stepWith_gapX_pe sc hr xs ys
          c0 c' _ hok0 (hends0 .gapX rfl) hstep
        refine ⟨hok'.mono sc xs ys (by omega), by omega, ?_⟩
        intro e he
        have : e = Step.gapX := (Option.some.inj he).symm
        rw [this]
        exact hhead'
      · obtain ⟨t0, rfl, hsrc⟩ := shiftUp_some_cell _ t c' hside
        obtain ⟨c0, hc0, hstep⟩ := map_stepWith_some _ xs ys _ t0 c'
          hsrc
        obtain ⟨hok0, hdiag0, hends0⟩ := hBm.2 t0 c0 hc0
        obtain ⟨hok', hhead', hdelta⟩ := stepWith_gapX_po sc hr xs ys
          c0 c' _ hok0 hstep
        refine ⟨hok'.mono sc xs ys (by omega), by omega, ?_⟩
        intro e he
        have : e = Step.gapX := (Option.some.inj he).symm
        rw [this]
        exact hhead'
  -- the new gap-in-y front
  have hyfOK : FrontOK sc xs ys (p : Int) (some .gapY)
      (List.zipWith betterCell
        (shiftDown ((frontAt (xs.length + ys.length + 1) hist
          (wfaPe sc).toNat (·.yf)).map (stepWith pushGapY xs ys)))
        (shiftDown ((frontAt (xs.length + ys.length + 1) hist
          (wfaPo sc).toNat (·.mf)).map (stepWith pushGapY xs ys)))) := by
    have l1 : ((frontAt (xs.length + ys.length + 1) hist
        (wfaPe sc).toNat (·.yf)).map (stepWith pushGapY xs ys)).length =
        xs.length + ys.length + 1 := by
      rw [List.length_map]; exact hCy.1
    have l2 : ((frontAt (xs.length + ys.length + 1) hist
        (wfaPo sc).toNat (·.mf)).map (stepWith pushGapY xs ys)).length =
        xs.length + ys.length + 1 := by
      rw [List.length_map]; exact hBm.1
    constructor
    · rw [List.length_zipWith, length_shiftDown _ (by omega),
        length_shiftDown _ (by omega), l1, l2]
      omega
    · intro t c' hc'
      rcases zipWith_better_some _ _ t c' hc' with hside | hside
      · have hsrc := shiftDown_some_cell _ t c' hside
        obtain ⟨c0, hc0, hstep⟩ := map_stepWith_some _ xs ys _ (t + 1)
          c' hsrc
        obtain ⟨hok0, hdiag0, hends0⟩ := hCy.2 (t + 1) c0 hc0
        obtain ⟨hok', hhead', hdelta⟩ := stepWith_gapY_pe sc hr xs ys
          c0 c' _ hok0 (hends0 .gapY rfl) hstep
        refine ⟨hok'.mono sc xs ys (by omega), by omega, ?_⟩
        intro e he
        have : e = Step.gapY := (Option.some.inj he).symm
        rw [this]
        exact hhead'
      · have hsrc := shiftDown_some_cell _ t c' hside
        obtain ⟨c0, hc0, hstep⟩ := map_stepWith_some _ xs ys _ (t + 1)
          c' hsrc
        obtain ⟨hok0, hdiag0, hends0⟩ := hBm.2 (t + 1) c0 hc0
        obtain ⟨hok', hhead', hdelta⟩ := stepWith_gapY_po sc hr xs ys
          c0 c' _ hok0 hstep
        refine ⟨hok'.mono sc xs ys (by omega), by omega, ?_⟩
        intro e he
        have : e = Step.gapY := (Option.some.inj he).symm
        rw [this]
        exact hhead'
  -- the base of the new match front
  have hbaseOK : FrontOK sc xs ys (p : Int) none
      (List.zipWith betterCell
        (List.zipWith betterCell
          ((frontAt (xs.length + ys.length + 1) hist
            (wfaPx sc).toNat (·.mf)).map (stepWith pushDiag xs ys))
          (List.zipWith betterCell
            (shiftUp ((frontAt (xs.length + ys.length + 1) hist
              (wfaPe sc).toNat (·.xf)).map (stepWith pushGapX xs ys)))
            (shiftUp ((frontAt (xs.length + ys.length + 1) hist
              (wfaPo sc).toNat (·.mf)).map (stepWith pushGapX xs ys)))))
        (List.zipWith betterCell
          (shiftDown ((frontAt (xs.length + ys.length + 1) hist
            (wfaPe sc).toNat (·.yf)).map (stepWith pushGapY xs ys)))
          (shiftDown ((frontAt (xs.length + ys.length + 1) hist
            (wfaPo sc).toNat (·.mf)).map (stepWith pushGapY xs ys))))) := by
    constructor
    · rw [List.length_zipWith, List.length_zipWith, List.length_map,
        hEm.1, hxfOK.1, hyfOK.1]
      omega
    · intro t c' hc'
      rcases zipWith_better_some _ _ t c' hc' with hside | hside
      · rcases zipWith_better_some _ _ t c' hside with hs2 | hs2
        · obtain ⟨c0, hc0, hstep⟩ := map_stepWith_some _ xs ys _ t c'
            hs2
          obtain ⟨hok0, hdiag0, hends0⟩ := hEm.2 t c0 hc0
          obtain ⟨hok', hdelta⟩ := stepWith_diag_px sc hr xs ys c0 c'
            _ hpx0 hok0 hstep
          refine ⟨hok'.mono sc xs ys (by omega), by omega, ?_⟩
          intro e he
          simp at he
        · obtain ⟨h1, h2, _⟩ := hxfOK.2 t c' hs2
          exact ⟨h1, h2, by intro e he; simp at he⟩
      · obtain ⟨h1, h2, _⟩ := hyfOK.2 t c' hside
        exact ⟨h1, h2, by intro e he; simp at he⟩
  -- extension preserves everything and closes the cells
  have hmfOK : FrontOK sc xs ys (p : Int) none
      ((List.zipWith betterCell
        (List.zipWith betterCell
          ((frontAt (xs.length + ys.length + 1) hist
            (wfaPx sc).toNat (·.mf)).map (stepWith pushDiag xs ys))
          (List.zipWith betterCell
            (shiftUp ((frontAt (xs.length + ys.length + 1) hist
              (wfaPe sc).toNat (·.xf)).map (stepWith pushGapX xs ys)))
            (shiftUp ((frontAt (xs.length + ys.length + 1) hist
              (wfaPo sc).toNat (·.mf)).map (stepWith pushGapX xs ys)))))
        (List.zipWith betterCell
          (shiftDown ((frontAt (xs.length + ys.length + 1) hist
            (wfaPe sc).toNat (·.yf)).map (stepWith pushGapY xs ys)))
          (shiftDown ((frontAt (xs.length + ys.length + 1) hist
            (wfaPo sc).toNat (·.mf)).map
              (stepWith pushGapY xs ys))))).map
        (Option.map extendCell)) ∧
      ∀ (t : Nat) (c : WCell),
        ((List.zipWith betterCell
          (List.zipWith betterCell
            ((frontAt (xs.length + ys.length + 1) hist
              (wfaPx sc).toNat (·.mf)).map (stepWith pushDiag xs ys))
            (List.zipWith betterCell
              (shiftUp ((frontAt (xs.length + ys.length + 1) hist
                (wfaPe sc).toNat (·.xf)).map (stepWith pushGapX xs ys)))
              (shiftUp ((frontAt (xs.length + ys.length + 1) hist
                (wfaPo sc).toNat (·.mf)).map
                  (stepWith pushGapX xs ys)))))
          (List.zipWith betterCell
            (shiftDown ((frontAt (xs.length + ys.length + 1) hist
              (wfaPe sc).toNat (·.yf)).map (stepWith pushGapY xs ys)))
            (shiftDown ((frontAt (xs.length + ys.length + 1) hist
              (wfaPo sc).toNat (·.mf)).map
                (stepWith pushGapY xs ys))))).map
          (Option.map extendCell))[t]? = some (some c) →
        ExtClosed c := by
    constructor
    · constructor
      · rw [List.length_map]
        exact hbaseOK.1
      · intro t c' hc'
        obtain ⟨c1, hc1, rfl⟩ := map_extend_some _ t c' hc'
        obtain ⟨hok1, hdiag1, _⟩ := hbaseOK.2 t c1 hc1
        obtain ⟨hok2, _, hoff2, hdiag2⟩ := extendCell_spec sc xs ys _
          c1 hok1
        refine ⟨hok2, by omega, ?_⟩
        intro e he
        simp at he
    · intro t c' hc'
      obtain ⟨c1, hc1, rfl⟩ := map_extend_some _ t c' hc'
      obtain ⟨hok1, _, _⟩ := hbaseOK.2 t c1 hc1
      obtain ⟨_, hclosed, _, _⟩ := extendCell_spec sc xs ys _ c1 hok1
      exact hclosed
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [nextLevel]
  · exact hmfOK.1
  · exact hxfOK
  · exact hyfOK
  · exact hmfOK.2

theorem cornerOf_sound (sc : Scoring) (xs ys : List Char) (p : Int)
    (lv : WLevel) (hlv : LevelOK sc xs ys p lv) (c : WCell)
    (h : cornerOf ys.length lv = some c) :
    IsMonotoneWalk c.walk.reverse xs ys ∧
    penOf sc c.walk.reverse xs ys ≤ p := by
  unfold cornerOf at h
  cases hg : lv.mf[ys.length]? with
  | none => rw [hg] at h; simp at h
  | some o =>
      rw [hg] at h
      cases o with
      | none => simp at h
      | some c0 =>
          dsimp only at h
          cases hxr : c0.xsRem with
          | cons a b => rw [hxr] at h; simp at h
          | nil =>
              cases hyr : c0.ysRem with
              | cons a b => rw [hxr, hyr] at h; simp at h
              | nil =>
                  rw [hxr, hyr] at h
                  simp at h
                  subst h
                  obtain ⟨hok, hdiag, _⟩ := hlv.hmf.2 ys.length c0 hg
                  have hoffm : c0.off = xs.length := by
                    have hd := hok.hxs
                    rw [hxr] at hd
                    have := congrArg List.length hd
                    rw [List.length_drop] at this
                    simp at this
                    have := hok.hoff
                    omega
                  have hjoffn : c0.joff = ys.length := by omega
                  have hv := hok.hvalid
                  have hp := hok.hpen
                  rw [hoffm, hjoffn, List.take_length,
                    List.take_length] at hv hp
                  exact ⟨hv, hp⟩

theorem wfaLoop_sound (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char) :
    ∀ (fuel : Nat) (p : Nat) (hist : List WLevel),
      HistOK sc xs ys p hist →
      ∀ c, wfaLoop xs ys (xs.length + ys.length + 1) ys.length
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat fuel hist =
          some c →
      IsMonotoneWalk c.walk.reverse xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hist _ c h
      simp [wfaLoop] at h
  | succ fuel ih =>
      intro p hist hh c h
      have hlv := nextLevel_sound sc hr hpe1 hpx1 xs ys p hist hh
      simp only [wfaLoop] at h
      cases hcorner : cornerOf ys.length
          (nextLevel xs ys (xs.length + ys.length + 1)
            (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist)
        with
      | some c0 =>
          rw [hcorner] at h
          simp at h
          subst h
          exact (cornerOf_sound sc xs ys _ _ hlv c0 hcorner).1
      | none =>
          rw [hcorner] at h
          exact ih (p + 1) ((nextLevel xs ys
              (xs.length + ys.length + 1) (wfaPe sc).toNat
              (wfaPo sc).toNat (wfaPx sc).toNat hist :: hist).take
                (max (wfaPe sc).toNat (max (wfaPo sc).toNat
                  (wfaPx sc).toNat)))
            (histOK_take sc xs ys (p + 1) _ _
              (histOK_cons sc xs ys p hist _ hh hlv)) c h

theorem wfaRun_sound (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaRun sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  have hseed := seedLevel_sound sc xs ys
  simp only [wfaRun] at h
  cases hc0 : cornerOf ys.length
      (seedLevel xs.length (xs.length + ys.length + 1) xs ys) with
  | some c =>
      rw [hc0] at h
      simp at h
      obtain ⟨hw, hs⟩ := h
      have hval := (cornerOf_sound sc xs ys 0 _ hseed c hc0).1
      rw [← hw]
      exact ⟨hval, hs⟩
  | none =>
      rw [hc0] at h
      cases hl : wfaLoop xs ys (xs.length + ys.length + 1) ys.length
          (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat
          ((xs.length + ys.length + 2) * (wfaPo sc).toNat + 1)
          [seedLevel xs.length (xs.length + ys.length + 1) xs ys] with
      | none => rw [hl] at h; simp at h
      | some c =>
          rw [hl] at h
          simp at h
          obtain ⟨hw, hs⟩ := h
          have hval := wfaLoop_sound sc hr hpe1 hpx1 xs ys _ 1 _
            (histOK_singleton sc xs ys _ hseed) c hl
          rw [← hw]
          exact ⟨hval, hs⟩

/-- Extract the gate's content. -/
theorem wfaGate_spec (sc : Scoring) (hg : wfaGateB sc = true) :
    ReasonableScoring sc ∧ 1 ≤ wfaPe sc ∧ 1 ≤ wfaPx sc := by
  simp only [wfaGateB, Bool.and_eq_true, decide_eq_true_iff] at hg
  exact ⟨(reasonableB_iff sc).mp hg.1.1, hg.2, hg.1.2⟩

/-- THEOREM T1 (unconditional): whatever `wfaAlign` returns is a
genuine alignment carrying its true score. -/
theorem wfaAlign_sound (sc : Scoring) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaAlign sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  unfold wfaAlign at h
  rw [wfaRunT_eq] at h
  by_cases hg : wfaGateB sc
  · rw [if_pos hg] at h
    obtain ⟨hr, hpe1, hpx1⟩ := wfaGate_spec sc hg
    cases hrun : wfaRun sc xs ys with
    | some r =>
        rw [hrun] at h
        simp at h
        rw [h] at hrun
        exact wfaRun_sound sc hr hpe1 hpx1 xs ys w s hrun
    | none =>
        rw [hrun] at h
        rw [gotohFusedAlign_equals_getBestAlignment] at h
        exact getBestAlignment_returns_a_valid_walk sc xs ys w s h
  · rw [if_neg hg] at h
    rw [gotohFusedAlign_equals_getBestAlignment] at h
    exact getBestAlignment_returns_a_valid_walk sc xs ys w s h

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 6a: completeness toolkit
-- ══════════════════════════════════════════════════════════════════

/-- A front covers offset i on diagonal index t. -/
def Covered (f : WFront) (t i : Nat) : Prop :=
  ∃ c : WCell, f[t]? = some (some c) ∧ i ≤ c.off

theorem splitRun_none (s : Step) (l : List Step) (a : Nat)
    (t : List Step) (h : splitRun s l = (a, none, t)) :
    l = List.replicate a s := by
  induction l generalizing a with
  | nil =>
      simp [splitRun] at h
      rw [← h.1]
      rfl
  | cons c rest ih =>
      by_cases hc : c = s
      · simp only [splitRun, if_pos hc] at h
        have h1 : (splitRun s rest).1 + 1 = a := congrArg Prod.fst h
        have h2 : (splitRun s rest).2 = (none, t) := congrArg Prod.snd h
        cases a with
        | zero => omega
        | succ a0 =>
            have hsp' : splitRun s rest = (a0, none, t) := by
              have hfst : (splitRun s rest).1 = a0 := by omega
              calc splitRun s rest
                  = ((splitRun s rest).1, (splitRun s rest).2) := rfl
                _ = (a0, none, t) := by rw [hfst, h2]
            have := ih a0 hsp'
            subst hc
            rw [List.replicate_succ, ← this]
      · simp only [splitRun, if_neg hc] at h
        have h2 : (some c : Option Step) = none :=
          congrArg (fun q => q.2.1) h
        simp at h2

/-- A walk that consumed at least one character of each string can
always be demoted. -/
theorem demoteWalk_isSome (r : List Step)
    (hx : 1 ≤ (r.map xConsumed).sum) (hy : 1 ≤ (r.map yConsumed).sum) :
    ∃ w', demoteWalk r = some w' := by
  match r with
  | [] => simp at hx
  | .diag :: rest => exact ⟨rest, rfl⟩
  | .gapX :: rest =>
      rcases hsp : splitRun .gapX (.gapX :: rest) with ⟨a, oe, t⟩
      cases oe with
      | none =>
          exfalso
          have := splitRun_none _ _ _ _ hsp
          rw [this] at hx
          rw [xsum_replicate_gapX] at hx
          omega
      | some e =>
          obtain ⟨_, hne⟩ := splitRun_some _ _ _ _ _ hsp
          cases e with
          | gapX => exact absurd rfl hne
          | diag =>
              refine ⟨List.replicate a .gapX ++ t, ?_⟩
              simp [demoteWalk, hsp]
          | gapY =>
              refine ⟨List.replicate (a - 1) .gapX ++ t, ?_⟩
              simp [demoteWalk, hsp]
  | .gapY :: rest =>
      rcases hsp : splitRun .gapY (.gapY :: rest) with ⟨b, oe, t⟩
      cases oe with
      | none =>
          exfalso
          have := splitRun_none _ _ _ _ hsp
          rw [this] at hy
          rw [ysum_replicate_gapY] at hy
          omega
      | some e =>
          obtain ⟨_, hne⟩ := splitRun_some _ _ _ _ _ hsp
          cases e with
          | gapY => exact absurd rfl hne
          | diag =>
              refine ⟨List.replicate b .gapY ++ t, ?_⟩
              simp [demoteWalk, hsp]
          | gapX =>
              refine ⟨List.replicate (b - 1) .gapY ++ t, ?_⟩
              simp [demoteWalk, hsp]

/-- A genuine cell strictly inside the grid can always be demoted, and
the demoted cell's fields are explicit. -/
theorem demoteCell_isSome (sc : Scoring) (xs ys : List Char)
    (c : WCell) (p : Int) (hok : CellOK sc xs ys p c)
    (hoff1 : 1 ≤ c.off) (hjoff1 : 1 ≤ c.joff) :
    ∃ d, demoteCell xs ys c = some d ∧ d.off + 1 = c.off ∧
      d.joff + 1 = c.joff ∧ d.xsRem = xs.drop d.off ∧
      d.ysRem = ys.drop d.joff := by
  obtain ⟨hvx, hvy⟩ := hok.hvalid
  have hx1 : 1 ≤ (c.walk.map xConsumed).sum := by
    have h1 := sum_map_reverse xConsumed c.walk
    rw [hvx] at h1
    rw [List.length_take_of_le hok.hoff] at h1
    omega
  have hy1 : 1 ≤ (c.walk.map yConsumed).sum := by
    have h1 := sum_map_reverse yConsumed c.walk
    rw [hvy] at h1
    rw [List.length_take_of_le hok.hjoff] at h1
    omega
  obtain ⟨w', hw'⟩ := demoteWalk_isSome c.walk hx1 hy1
  cases hi : c.off with
  | zero => omega
  | succ i0 =>
      cases hj : c.joff with
      | zero => omega
      | succ j0 =>
          refine ⟨⟨i0, j0, xs.drop i0, ys.drop j0, w'⟩, ?_, ?_, ?_,
            rfl, rfl⟩
          · simp [demoteCell, hi, hj, hw']
          · rfl
          · rfl

-- Coverage propagation through the pipeline pieces.
theorem betterCell_off_left (c : WCell) (o : Option WCell) :
    ∃ c'', betterCell (some c) o = some c'' ∧ c.off ≤ c''.off := by
  cases o with
  | none => exact ⟨c, rfl, Nat.le_refl _⟩
  | some b =>
      simp only [betterCell]
      by_cases hb : b.off ≤ c.off
      · rw [if_pos hb]; exact ⟨c, rfl, Nat.le_refl _⟩
      · rw [if_neg hb]; exact ⟨b, rfl, by omega⟩

theorem betterCell_off_right (o : Option WCell) (c : WCell) :
    ∃ c'', betterCell o (some c) = some c'' ∧ c.off ≤ c''.off := by
  cases o with
  | none => exact ⟨c, rfl, Nat.le_refl _⟩
  | some a =>
      simp only [betterCell]
      by_cases hb : c.off ≤ a.off
      · rw [if_pos hb]; exact ⟨a, rfl, hb⟩
      · rw [if_neg hb]; exact ⟨c, rfl, Nat.le_refl _⟩

theorem covered_zipWith_left (f g : WFront) (t i : Nat)
    (hlen : f.length = g.length) (h : Covered f t i) :
    Covered (List.zipWith betterCell f g) t i := by
  obtain ⟨c, hc, hi⟩ := h
  have ht : t < g.length := by
    rw [← hlen]
    rcases Nat.lt_or_ge t f.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hc
      simp at hc
  obtain ⟨o, ho⟩ : ∃ o, g[t]? = some o :=
    ⟨g[t], List.getElem?_eq_getElem ht⟩
  obtain ⟨c'', hcc, hoff⟩ := betterCell_off_left c o
  refine ⟨c'', ?_, by omega⟩
  rw [List.getElem?_zipWith, hc, ho]
  dsimp only
  rw [hcc]

theorem covered_zipWith_right (f g : WFront) (t i : Nat)
    (hlen : f.length = g.length) (h : Covered g t i) :
    Covered (List.zipWith betterCell f g) t i := by
  obtain ⟨c, hc, hi⟩ := h
  have ht : t < f.length := by
    rw [hlen]
    rcases Nat.lt_or_ge t g.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hc
      simp at hc
  obtain ⟨o, ho⟩ : ∃ o, f[t]? = some o :=
    ⟨f[t], List.getElem?_eq_getElem ht⟩
  obtain ⟨c'', hcc, hoff⟩ := betterCell_off_right o c
  refine ⟨c'', ?_, by omega⟩
  rw [List.getElem?_zipWith, hc, ho]
  dsimp only
  rw [hcc]

theorem extendGo_off_ge : ∀ (xr yr : List Char) (i j : Nat)
    (w : List Step), i ≤ (extendGo i j w xr yr).off := by
  intro xr
  induction xr with
  | nil => intro yr i j w; simp [extendGo]
  | cons x xr ih =>
      intro yr i j w
      cases yr with
      | nil => simp [extendGo]
      | cons y yr =>
          by_cases hxy : x = y
          · rw [show extendGo i j w (x :: xr) (y :: yr) =
              extendGo (i + 1) (j + 1) (.diag :: w) xr yr from by
                rw [extendGo, if_pos hxy]]
            have := ih yr (i + 1) (j + 1) (.diag :: w)
            omega
          · rw [show extendGo i j w (x :: xr) (y :: yr) =
              (⟨i, j, x :: xr, y :: yr, w⟩ : WCell) from by
                rw [extendGo, if_neg hxy]]
            show i ≤ i
            omega

theorem covered_map_extend (f : WFront) (t i : Nat)
    (h : Covered f t i) :
    Covered (f.map (Option.map extendCell)) t i := by
  obtain ⟨c, hc, hi⟩ := h
  refine ⟨extendCell c, ?_, ?_⟩
  · rw [List.getElem?_map, hc]
    rfl
  · have := extendGo_off_ge c.xsRem c.ysRem c.off c.joff c.walk
    unfold extendCell
    omega

theorem covered_shiftUp (f : WFront) (t0 i : Nat)
    (h : Covered f t0 i) (ht : t0 + 1 < f.length) :
    Covered (shiftUp f) (t0 + 1) i := by
  obtain ⟨c, hc, hi⟩ := h
  refine ⟨c, ?_, hi⟩
  simp only [shiftUp, List.getElem?_cons_succ]
  rw [List.getElem?_dropLast, if_pos (by omega)]
  exact hc

theorem covered_shiftDown (f : WFront) (t i : Nat)
    (h : Covered f (t + 1) i) :
    Covered (shiftDown f) t i := by
  obtain ⟨c, hc, hi⟩ := h
  have ht : t + 1 < f.length := by
    rcases Nat.lt_or_ge (t + 1) f.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hc
      simp at hc
  refine ⟨c, ?_, hi⟩
  simp only [shiftDown]
  rw [List.getElem?_append, if_pos (by rw [List.length_drop]; omega),
    List.getElem?_drop, show 1 + t = t + 1 from by omega]
  exact hc

theorem covered_map_step (push : WCell → Option WCell)
    (xs ys : List Char) (f : WFront) (t : Nat) (c0 c' : WCell)
    (hc0 : f[t]? = some (some c0))
    (hstep : stepWith push xs ys (some c0) = some c') (i : Nat)
    (hoff : i ≤ c'.off) :
    Covered (f.map (stepWith push xs ys)) t i := by
  refine ⟨c', ?_, hoff⟩
  rw [List.getElem?_map, hc0]
  simp only [Option.map_some]
  rw [hstep]

-- Un-snoc validity (pure count arithmetic).
theorem isMonotoneWalk_unsnoc_gapX (w0 : List Step)
    (xsPre ysPre0 : List Char) (y : Char)
    (h : IsMonotoneWalk (w0 ++ [.gapX]) xsPre (ysPre0 ++ [y])) :
    IsMonotoneWalk w0 xsPre ysPre0 := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] at hx hy ⊢ <;> omega

theorem isMonotoneWalk_unsnoc_gapY (w0 : List Step)
    (xsPre0 ysPre : List Char) (x : Char)
    (h : IsMonotoneWalk (w0 ++ [.gapY]) (xsPre0 ++ [x]) ysPre) :
    IsMonotoneWalk w0 xsPre0 ysPre := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] at hx hy ⊢ <;> omega

theorem isMonotoneWalk_unsnoc_diag (w0 : List Step)
    (xsPre0 ysPre0 : List Char) (x y : Char)
    (h : IsMonotoneWalk (w0 ++ [.diag]) (xsPre0 ++ [x])
      (ysPre0 ++ [y])) :
    IsMonotoneWalk w0 xsPre0 ysPre0 := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> simp [xConsumed, yConsumed] at hx hy ⊢ <;> omega

/-- The character a snoc-prefix ends with, as an indexed character of
the full string. -/
theorem prefix_last_char {α : Type} (l l0 : List α) (a : α)
    (rest : List α) (h : l = (l0 ++ [a]) ++ rest) :
    l[l0.length]? = some a := by
  subst h
  rw [List.getElem?_append, if_pos (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append, if_neg (by omega)]
  simp

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 6b: pinned cells still produce the needed children
-- ══════════════════════════════════════════════════════════════════

theorem stepWith_gapX_covers (sc : Scoring) (xs ys : List Char)
    (c0 : WCell) (p : Int) (hok : CellOK sc xs ys p c0)
    (i t0 : Nat) (hile : i ≤ c0.off)
    (hdiag : c0.joff + xs.length = c0.off + t0)
    (hchild : i + t0 + 1 ≤ ys.length + xs.length)
    (hj1 : xs.length ≤ i + t0) :
    ∃ c', stepWith pushGapX xs ys (some c0) = some c' ∧
      i ≤ c'.off := by
  cases hyr : c0.ysRem with
  | cons yy yr =>
      refine ⟨⟨c0.off, c0.joff + 1, c0.xsRem, yr, .gapX :: c0.walk⟩,
        ?_, hile⟩
      simp [stepWith, pushGapX, hyr]
  | nil =>
      have hjn : c0.joff = ys.length := by
        have hd := hok.hys
        rw [hyr] at hd
        have hlen := congrArg List.length hd
        rw [List.length_drop] at hlen
        simp at hlen
        have := hok.hjoff
        omega
      have hstrict : i < c0.off := by omega
      obtain ⟨d, hd, hdo, hdj, hdxs, hdys⟩ := demoteCell_isSome sc xs
        ys c0 p hok (by omega) (by omega)
      cases hdr : d.ysRem with
      | nil =>
          exfalso
          rw [hdys] at hdr
          have hlen := congrArg List.length hdr
          rw [List.length_drop] at hlen
          simp at hlen
          omega
      | cons yy yr =>
          refine ⟨⟨d.off, d.joff + 1, d.xsRem, yr, .gapX :: d.walk⟩,
            ?_, ?_⟩
          · simp [stepWith, hd, pushGapX, hdr, hyr]
          · show i ≤ d.off
            omega

theorem stepWith_gapY_covers (sc : Scoring) (xs ys : List Char)
    (c0 : WCell) (p : Int) (hok : CellOK sc xs ys p c0)
    (i0 t0 : Nat) (hile : i0 ≤ c0.off)
    (hdiag : c0.joff + xs.length = c0.off + t0)
    (hchild : i0 + 1 ≤ xs.length)
    (ht01 : 1 ≤ t0) :
    ∃ c', stepWith pushGapY xs ys (some c0) = some c' ∧
      i0 + 1 ≤ c'.off := by
  cases hxr : c0.xsRem with
  | cons xx xr =>
      refine ⟨⟨c0.off + 1, c0.joff, xr, c0.ysRem, .gapY :: c0.walk⟩,
        ?_, ?_⟩
      · simp [stepWith, pushGapY, hxr]
      · show i0 + 1 ≤ c0.off + 1
        omega
  | nil =>
      have him : c0.off = xs.length := by
        have hd := hok.hxs
        rw [hxr] at hd
        have hlen := congrArg List.length hd
        rw [List.length_drop] at hlen
        simp at hlen
        have := hok.hoff
        omega
      obtain ⟨d, hd, hdo, hdj, hdxs, hdys⟩ := demoteCell_isSome sc xs
        ys c0 p hok (by omega) (by omega)
      cases hdr : d.xsRem with
      | nil =>
          exfalso
          rw [hdxs] at hdr
          have hlen := congrArg List.length hdr
          rw [List.length_drop] at hlen
          simp at hlen
          omega
      | cons xx xr =>
          refine ⟨⟨d.off + 1, d.joff, xr, d.ysRem, .gapY :: d.walk⟩,
            ?_, ?_⟩
          · simp [stepWith, hd, pushGapY, hdr, hxr]
          · show i0 + 1 ≤ d.off + 1
            omega

theorem stepWith_diag_covers (sc : Scoring) (xs ys : List Char)
    (c0 : WCell) (p : Int) (hok : CellOK sc xs ys p c0)
    (i0 t0 : Nat) (hile : i0 ≤ c0.off)
    (hdiag : c0.joff + xs.length = c0.off + t0)
    (hchildx : i0 + 1 ≤ xs.length)
    (hchildy : i0 + 1 + t0 ≤ ys.length + xs.length)
    (hj1 : xs.length + 1 ≤ i0 + 1 + t0) :
    ∃ c', stepWith pushDiag xs ys (some c0) = some c' ∧
      i0 + 1 ≤ c'.off := by
  cases hxr : c0.xsRem with
  | cons xx xr =>
      cases hyr : c0.ysRem with
      | cons yy yr =>
          refine ⟨⟨c0.off + 1, c0.joff + 1, xr, yr, .diag :: c0.walk⟩,
            ?_, ?_⟩
          · simp [stepWith, pushDiag, hxr, hyr]
          · show i0 + 1 ≤ c0.off + 1
            omega
      | nil =>
          -- pinned at the y-boundary
          have hjn : c0.joff = ys.length := by
            have hd := hok.hys
            rw [hyr] at hd
            have hlen := congrArg List.length hd
            rw [List.length_drop] at hlen
            simp at hlen
            have := hok.hjoff
            omega
          have hstrict : i0 < c0.off := by omega
          obtain ⟨d, hd, hdo, hdj, hdxs, hdys⟩ := demoteCell_isSome sc
            xs ys c0 p hok (by omega) (by omega)
          have hdx_ne : d.off < xs.length := by
            have := hok.hoff
            omega
          have hdy_ne : d.joff < ys.length := by omega
          cases hdr : d.xsRem with
          | nil =>
              exfalso
              rw [hdxs] at hdr
              have hlen := congrArg List.length hdr
              rw [List.length_drop] at hlen
              simp at hlen
              omega
          | cons xx2 xr2 =>
              cases hdr2 : d.ysRem with
              | nil =>
                  exfalso
                  rw [hdys] at hdr2
                  have hlen := congrArg List.length hdr2
                  rw [List.length_drop] at hlen
                  simp at hlen
                  omega
              | cons yy2 yr2 =>
                  refine ⟨⟨d.off + 1, d.joff + 1, xr2, yr2,
                    .diag :: d.walk⟩, ?_, ?_⟩
                  · simp [stepWith, hd, pushDiag, hdr, hdr2, hxr,
                      hyr]
                  · show i0 + 1 ≤ d.off + 1
                    omega
  | nil =>
      have him : c0.off = xs.length := by
        have hd := hok.hxs
        rw [hxr] at hd
        have hlen := congrArg List.length hd
        rw [List.length_drop] at hlen
        simp at hlen
        have := hok.hoff
        omega
      obtain ⟨d, hd, hdo, hdj, hdxs, hdys⟩ := demoteCell_isSome sc xs
        ys c0 p hok (by omega) (by omega)
      have hdx_ne : d.off < xs.length := by omega
      have hdy_ne : d.joff < ys.length := by
        have := hok.hjoff
        omega
      cases hdr : d.xsRem with
      | nil =>
          exfalso
          rw [hdxs] at hdr
          have hlen := congrArg List.length hdr
          rw [List.length_drop] at hlen
          simp at hlen
          omega
      | cons xx2 xr2 =>
          cases hdr2 : d.ysRem with
          | nil =>
              exfalso
              rw [hdys] at hdr2
              have hlen := congrArg List.length hdr2
              rw [List.length_drop] at hlen
              simp at hlen
              omega
          | cons yy2 yr2 =>
              refine ⟨⟨d.off + 1, d.joff + 1, xr2, yr2,
                .diag :: d.walk⟩, ?_, ?_⟩
              · simp [stepWith, hd, pushDiag, hdr, hdr2, hxr]
              · show i0 + 1 ≤ d.off + 1
                omega

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 6c: the completeness invariant
-- ══════════════════════════════════════════════════════════════════

/-- A complete level: every prefix walk with this exact penalty is
covered on its diagonal by the match front, and by the matching gap
front when it ends in a gap column. -/
def LevelComplete (sc : Scoring) (xs ys : List Char) (p : Int)
    (lv : WLevel) : Prop :=
  ∀ (w : List Step) (xsPre ysPre xsRest ysRest : List Char),
    xs = xsPre ++ xsRest → ys = ysPre ++ ysRest →
    IsMonotoneWalk w xsPre ysPre →
    penOf sc w xsPre ysPre = p →
    Covered lv.mf (ysPre.length + (xs.length - xsPre.length))
      xsPre.length ∧
    (lastPrev w none = some .gapX →
      Covered lv.xf (ysPre.length + (xs.length - xsPre.length))
        xsPre.length) ∧
    (lastPrev w none = some .gapY →
      Covered lv.yf (ysPre.length + (xs.length - xsPre.length))
        xsPre.length)

abbrev HistComplete (sc : Scoring) (xs ys : List Char) (p : Nat)
    (hist : List WLevel) : Prop :=
  ∀ (d : Nat) (lv : WLevel), hist[d]? = some lv →
    LevelComplete sc xs ys ((p : Int) - 1 - (d : Int)) lv

theorem frontAt_eq (len : Nat) (hist : List WLevel) (delta : Nat)
    (lv' : WLevel) (sel : WLevel → WFront)
    (hget : hist[delta - 1]? = some lv') :
    frontAt len hist delta sel = sel lv' := by
  simp only [frontAt, hget]

-- Target pipelines: pushing source coverage into the new fronts.
theorem covered_new_xf (xs ys : List Char) (A B : WFront) (t0 : Nat)
    (c0 c' : WCell)
    (hlenA : A.length = xs.length + ys.length + 1)
    (hlenB : B.length = xs.length + ys.length + 1)
    (ht : t0 + 1 < xs.length + ys.length + 1)
    (i : Nat) (hoff : i ≤ c'.off)
    (hsrc : A[t0]? = some (some c0) ∨ B[t0]? = some (some c0))
    (hstep : stepWith pushGapX xs ys (some c0) = some c') :
    Covered (List.zipWith betterCell
      (shiftUp (A.map (stepWith pushGapX xs ys)))
      (shiftUp (B.map (stepWith pushGapX xs ys)))) (t0 + 1) i := by
  have hlen : (shiftUp (A.map (stepWith pushGapX xs ys))).length =
      (shiftUp (B.map (stepWith pushGapX xs ys))).length := by
    rw [length_shiftUp _ (by rw [List.length_map]; omega),
      length_shiftUp _ (by rw [List.length_map]; omega),
      List.length_map, List.length_map, hlenA, hlenB]
  rcases hsrc with hs | hs
  · apply covered_zipWith_left _ _ _ _ hlen
    apply covered_shiftUp
    · exact covered_map_step _ xs ys A t0 c0 c' hs hstep i hoff
    · rw [List.length_map]; omega
  · apply covered_zipWith_right _ _ _ _ hlen
    apply covered_shiftUp
    · exact covered_map_step _ xs ys B t0 c0 c' hs hstep i hoff
    · rw [List.length_map]; omega

theorem covered_new_yf (xs ys : List Char) (A B : WFront) (t : Nat)
    (c0 c' : WCell)
    (hlenA : A.length = xs.length + ys.length + 1)
    (hlenB : B.length = xs.length + ys.length + 1)
    (i : Nat) (hoff : i ≤ c'.off)
    (hsrc : A[t + 1]? = some (some c0) ∨ B[t + 1]? = some (some c0))
    (hstep : stepWith pushGapY xs ys (some c0) = some c') :
    Covered (List.zipWith betterCell
      (shiftDown (A.map (stepWith pushGapY xs ys)))
      (shiftDown (B.map (stepWith pushGapY xs ys)))) t i := by
  have hlen : (shiftDown (A.map (stepWith pushGapY xs ys))).length =
      (shiftDown (B.map (stepWith pushGapY xs ys))).length := by
    rw [length_shiftDown _ (by rw [List.length_map]; omega),
      length_shiftDown _ (by rw [List.length_map]; omega),
      List.length_map, List.length_map, hlenA, hlenB]
  rcases hsrc with hs | hs
  · apply covered_zipWith_left _ _ _ _ hlen
    apply covered_shiftDown
    exact covered_map_step _ xs ys A (t + 1) c0 c' hs hstep i hoff
  · apply covered_zipWith_right _ _ _ _ hlen
    apply covered_shiftDown
    exact covered_map_step _ xs ys B (t + 1) c0 c' hs hstep i hoff

theorem covered_mf_of_xf (D XF YF : WFront) (t i : Nat)
    (hlenD : D.length = XF.length) (hlenY : YF.length = XF.length)
    (h : Covered XF t i) :
    Covered ((List.zipWith betterCell
      (List.zipWith betterCell D XF) YF).map
        (Option.map extendCell)) t i := by
  apply covered_map_extend
  apply covered_zipWith_left
  · rw [List.length_zipWith, hlenD, hlenY]
    omega
  · exact covered_zipWith_right _ _ _ _ hlenD h

theorem covered_mf_of_yf (D XF YF : WFront) (t i : Nat)
    (hlenD : D.length = XF.length) (hlenY : YF.length = XF.length)
    (h : Covered YF t i) :
    Covered ((List.zipWith betterCell
      (List.zipWith betterCell D XF) YF).map
        (Option.map extendCell)) t i := by
  apply covered_map_extend
  apply covered_zipWith_right
  · rw [List.length_zipWith, hlenD, hlenY]
    omega
  · exact h

theorem covered_mf_of_diag (xs ys : List Char) (Draw XF YF : WFront)
    (t : Nat) (c0 c' : WCell)
    (hlenD : Draw.length = XF.length)
    (hlenY : YF.length = XF.length)
    (i : Nat) (hoff : i ≤ c'.off)
    (hsrc : Draw[t]? = some (some c0))
    (hstep : stepWith pushDiag xs ys (some c0) = some c') :
    Covered ((List.zipWith betterCell
      (List.zipWith betterCell
        (Draw.map (stepWith pushDiag xs ys)) XF) YF).map
        (Option.map extendCell)) t i := by
  apply covered_map_extend
  apply covered_zipWith_left
  · rw [List.length_zipWith, List.length_map, hlenD, hlenY]
    omega
  · apply covered_zipWith_left
    · rw [List.length_map, hlenD]
    · exact covered_map_step _ xs ys Draw t c0 c' hsrc hstep i hoff

/-- THE COMPLETENESS THEOREM for one wavefront step: every prefix walk
whose exact penalty is the new level is covered by the new fronts. -/
theorem nextLevel_complete (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc)
    (xs ys : List Char) (p : Nat) (hist : List WLevel)
    (hh : HistOK sc xs ys p hist)
    (hhc : HistComplete sc xs ys p hist)
    (hlen1 : 1 ≤ p)
    (hwin : hist.length = min p (max (wfaPe sc).toNat
      (max (wfaPo sc).toNat (wfaPx sc).toNat))) :
    LevelComplete sc xs ys (p : Int)
      (nextLevel xs ys (xs.length + ys.length + 1)
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist) := by
  have hO := hr.open_neg
  have hpo1 : 1 ≤ wfaPo sc := by unfold wfaPo; omega
  have hpeC : (((wfaPe sc).toNat : Nat) : Int) = wfaPe sc := by omega
  have hpoC : (((wfaPo sc).toNat : Nat) : Int) = wfaPo sc := by omega
  have hpxC : (((wfaPx sc).toNat : Nat) : Int) = wfaPx sc := by omega
  have hlvOK := nextLevel_sound sc hr hpe1 hpx1 xs ys p hist hh
  have hAxF := frontAt_ok sc xs ys p hist (wfaPe sc).toNat (by omega)
    hh (·.xf) (some .gapX) (fun lv q h => h.hxf)
  have hBmF := frontAt_ok sc xs ys p hist (wfaPo sc).toNat (by omega)
    hh (·.mf) none (fun lv q h => h.hmf)
  have hCyF := frontAt_ok sc xs ys p hist (wfaPe sc).toNat (by omega)
    hh (·.yf) (some .gapY) (fun lv q h => h.hyf)
  have hEmF := frontAt_ok sc xs ys p hist (wfaPx sc).toNat (by omega)
    hh (·.mf) none (fun lv q h => h.hmf)
  have hxfLenE := hlvOK.hxf.1
  have hyfLenE := hlvOK.hyf.1
  simp only [nextLevel] at hxfLenE hyfLenE
  have hlenD1 : ((frontAt (xs.length + ys.length + 1) hist
      (wfaPx sc).toNat (·.mf)).map (stepWith pushDiag xs ys)).length =
      xs.length + ys.length + 1 := by
    rw [List.length_map]; exact hEmF.1
  suffices H : ∀ (N : Nat) (w : List Step)
      (xsPre ysPre xsRest ysRest : List Char),
      w.length ≤ N → xs = xsPre ++ xsRest → ys = ysPre ++ ysRest →
      IsMonotoneWalk w xsPre ysPre →
      penOf sc w xsPre ysPre = (p : Int) →
      Covered (nextLevel xs ys (xs.length + ys.length + 1)
          (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist).mf
        (ysPre.length + (xs.length - xsPre.length)) xsPre.length ∧
      (lastPrev w none = some .gapX →
        Covered (nextLevel xs ys (xs.length + ys.length + 1)
            (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist).xf
          (ysPre.length + (xs.length - xsPre.length)) xsPre.length) ∧
      (lastPrev w none = some .gapY →
        Covered (nextLevel xs ys (xs.length + ys.length + 1)
            (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist).yf
          (ysPre.length + (xs.length - xsPre.length)) xsPre.length) by
    intro w xsPre ysPre xsRest ysRest h1 h2 h3 h4
    exact H w.length w xsPre ysPre xsRest ysRest (Nat.le_refl _) h1 h2
      h3 h4
  intro N
  induction N with
  | zero =>
      intro w xsPre ysPre xsRest ysRest hlen h1 h2 hv hpen
      exfalso
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      obtain ⟨hvx, hvy⟩ := hv
      simp at hvx hvy
      have hxnil : xsPre = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      have hynil : ysPre = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst hxnil
      subst hynil
      rw [penOf_nil] at hpen
      omega
  | succ N ihN =>
      intro w xsPre ysPre xsRest ysRest hlen hxsplit hysplit hvalid
        hpen
      have hxpre_le : xsPre.length ≤ xs.length := by
        rw [hxsplit, List.length_append]; omega
      have hypre_le : ysPre.length ≤ ys.length := by
        rw [hysplit, List.length_append]; omega
      rcases List.eq_nil_or_concat w with hwnil | ⟨w0, last, hwc⟩
      · exfalso
        subst hwnil
        obtain ⟨hvx, hvy⟩ := hvalid
        simp at hvx hvy
        have hxnil : xsPre = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        have hynil : ysPre = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        subst hxnil
        subst hynil
        rw [penOf_nil] at hpen
        omega
      · rw [List.concat_eq_append] at hwc
        subst hwc
        cases last with
        | gapX =>
            have hy1 : 1 ≤ ysPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [yConsumed] at hvy
              omega
            rcases List.eq_nil_or_concat ysPre with hynil |
              ⟨ysPre0, y, hys0⟩
            · rw [hynil] at hy1; simp at hy1
            · rw [List.concat_eq_append] at hys0
              subst hys0
              have hyl : (ysPre0 ++ [y]).length = ysPre0.length + 1 :=
                by simp
              have hvalid0 : IsMonotoneWalk w0 xsPre ysPre0 :=
                isMonotoneWalk_unsnoc_gapX w0 xsPre ysPre0 y hvalid
              have hpeninc := penOf_snoc_gapX sc w0 xsPre ysPre0 y
                hvalid0
              have hys' : ys = ysPre0 ++ (y :: ysRest) := by
                rw [hysplit, List.append_assoc]
                rfl
              have hpen0nn := penOf_nonneg sc hr w0 xsPre ysPre0
                hvalid0
              have htEq : (ysPre0 ++ [y]).length +
                  (xs.length - xsPre.length) =
                  (ysPre0.length + (xs.length - xsPre.length)) + 1 :=
                by rw [hyl]; omega
              have hlast : lastPrev (w0 ++ [Step.gapX]) none =
                  some .gapX := lastPrev_snoc w0 .gapX none
              by_cases hw0x : lastPrev w0 none = some .gapX
              · rw [if_pos hw0x] at hpeninc
                have hplt : penOf sc w0 xsPre ysPre0 =
                    (p : Int) - wfaPe sc := by omega
                have hidx : (wfaPe sc).toNat - 1 < hist.length := by
                  omega
                have hget : hist[(wfaPe sc).toNat - 1]? =
                    some (hist[(wfaPe sc).toNat - 1]'hidx) :=
                  List.getElem?_eq_getElem hidx
                have hlvC := hhc _ _ hget
                have hlvlEq : (p : Int) - 1 -
                    (((wfaPe sc).toNat - 1 : Nat) : Int) =
                    (p : Int) - wfaPe sc := by omega
                rw [hlvlEq] at hlvC
                obtain ⟨_, hcX, _⟩ := hlvC w0 xsPre ysPre0 xsRest
                  (y :: ysRest) hxsplit hys' hvalid0 (by omega)
                obtain ⟨c0, hc0, hioff⟩ := hcX hw0x
                have hlvOK' := hh _ _ hget
                obtain ⟨hok0, hdiag0, _⟩ := hlvOK'.hxf.2 _ c0 hc0
                obtain ⟨c', hstep, hoff'⟩ := stepWith_gapX_covers sc
                  xs ys c0 _ hok0 xsPre.length
                  (ysPre0.length + (xs.length - xsPre.length)) hioff
                  (by omega) (by omega) (by omega)
                have hsrc : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPe sc).toNat (·.xf))[
                      ysPre0.length + (xs.length - xsPre.length)]? =
                    some (some c0) := by
                  rw [frontAt_eq _ _ _ _ _ hget]
                  exact hc0
                have hcovE := covered_new_xf xs ys _ _ _ c0 c' hAxF.1
                  hBmF.1 (by omega) xsPre.length hoff' (Or.inl hsrc)
                  hstep
                refine ⟨?_, ?_, ?_⟩
                · rw [htEq]
                  simp only [nextLevel]
                  exact covered_mf_of_xf _ _ _ _ _
                    (by rw [hlenD1, hxfLenE])
                    (by rw [hyfLenE, hxfLenE]) hcovE
                · intro _
                  rw [htEq]
                  simp only [nextLevel]
                  exact hcovE
                · intro habs
                  rw [hlast] at habs
                  simp at habs
              · rw [if_neg hw0x] at hpeninc
                have hplt : penOf sc w0 xsPre ysPre0 =
                    (p : Int) - wfaPo sc := by omega
                have hidx : (wfaPo sc).toNat - 1 < hist.length := by
                  omega
                have hget : hist[(wfaPo sc).toNat - 1]? =
                    some (hist[(wfaPo sc).toNat - 1]'hidx) :=
                  List.getElem?_eq_getElem hidx
                have hlvC := hhc _ _ hget
                have hlvlEq : (p : Int) - 1 -
                    (((wfaPo sc).toNat - 1 : Nat) : Int) =
                    (p : Int) - wfaPo sc := by omega
                rw [hlvlEq] at hlvC
                obtain ⟨hcM, _, _⟩ := hlvC w0 xsPre ysPre0 xsRest
                  (y :: ysRest) hxsplit hys' hvalid0 (by omega)
                obtain ⟨c0, hc0, hioff⟩ := hcM
                have hlvOK' := hh _ _ hget
                obtain ⟨hok0, hdiag0, _⟩ := hlvOK'.hmf.2 _ c0 hc0
                obtain ⟨c', hstep, hoff'⟩ := stepWith_gapX_covers sc
                  xs ys c0 _ hok0 xsPre.length
                  (ysPre0.length + (xs.length - xsPre.length)) hioff
                  (by omega) (by omega) (by omega)
                have hsrc : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPo sc).toNat (·.mf))[
                      ysPre0.length + (xs.length - xsPre.length)]? =
                    some (some c0) := by
                  rw [frontAt_eq _ _ _ _ _ hget]
                  exact hc0
                have hcovE := covered_new_xf xs ys _ _ _ c0 c' hAxF.1
                  hBmF.1 (by omega) xsPre.length hoff' (Or.inr hsrc)
                  hstep
                refine ⟨?_, ?_, ?_⟩
                · rw [htEq]
                  simp only [nextLevel]
                  exact covered_mf_of_xf _ _ _ _ _
                    (by rw [hlenD1, hxfLenE])
                    (by rw [hyfLenE, hxfLenE]) hcovE
                · intro _
                  rw [htEq]
                  simp only [nextLevel]
                  exact hcovE
                · intro habs
                  rw [hlast] at habs
                  simp at habs
        | gapY =>
            have hx1 : 1 ≤ xsPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [xConsumed] at hvx
              omega
            rcases List.eq_nil_or_concat xsPre with hxnil |
              ⟨xsPre0, x, hxs0⟩
            · rw [hxnil] at hx1; simp at hx1
            · rw [List.concat_eq_append] at hxs0
              subst hxs0
              have hxl : (xsPre0 ++ [x]).length = xsPre0.length + 1 :=
                by simp
              have hvalid0 : IsMonotoneWalk w0 xsPre0 ysPre :=
                isMonotoneWalk_unsnoc_gapY w0 xsPre0 ysPre x hvalid
              have hpeninc := penOf_snoc_gapY sc w0 xsPre0 ysPre x
                hvalid0
              have hxs' : xs = xsPre0 ++ (x :: xsRest) := by
                rw [hxsplit, List.append_assoc]
                rfl
              have hpen0nn := penOf_nonneg sc hr w0 xsPre0 ysPre
                hvalid0
              have htEq : ysPre.length +
                  (xs.length - xsPre0.length) =
                  (ysPre.length +
                    (xs.length - (xsPre0 ++ [x]).length)) + 1 := by
                rw [hxl]; omega
              have hlast : lastPrev (w0 ++ [Step.gapY]) none =
                  some .gapY := lastPrev_snoc w0 .gapY none
              by_cases hw0y : lastPrev w0 none = some .gapY
              · rw [if_pos hw0y] at hpeninc
                have hplt : penOf sc w0 xsPre0 ysPre =
                    (p : Int) - wfaPe sc := by omega
                have hidx : (wfaPe sc).toNat - 1 < hist.length := by
                  omega
                have hget : hist[(wfaPe sc).toNat - 1]? =
                    some (hist[(wfaPe sc).toNat - 1]'hidx) :=
                  List.getElem?_eq_getElem hidx
                have hlvC := hhc _ _ hget
                have hlvlEq : (p : Int) - 1 -
                    (((wfaPe sc).toNat - 1 : Nat) : Int) =
                    (p : Int) - wfaPe sc := by omega
                rw [hlvlEq] at hlvC
                obtain ⟨_, _, hcY⟩ := hlvC w0 xsPre0 ysPre
                  (x :: xsRest) ysRest hxs' hysplit hvalid0 (by omega)
                obtain ⟨c0, hc0, hioff⟩ := hcY hw0y
                have hlvOK' := hh _ _ hget
                obtain ⟨hok0, hdiag0, _⟩ := hlvOK'.hyf.2 _ c0 hc0
                obtain ⟨c', hstep, hoff'⟩ := stepWith_gapY_covers sc
                  xs ys c0 _ hok0 xsPre0.length
                  (ysPre.length + (xs.length - xsPre0.length)) hioff
                  (by omega) (by omega) (by omega)
                have hsrc : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPe sc).toNat (·.yf))[
                      ysPre.length + (xs.length - xsPre0.length)]? =
                    some (some c0) := by
                  rw [frontAt_eq _ _ _ _ _ hget]
                  exact hc0
                have hsrc' : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPe sc).toNat (·.yf))[
                      (ysPre.length +
                        (xs.length - (xsPre0 ++ [x]).length)) + 1]? =
                    some (some c0) := by
                  rw [← htEq]
                  exact hsrc
                have hcovE := covered_new_yf xs ys _ _ _ c0 c' hCyF.1
                  hBmF.1 (xsPre0 ++ [x]).length
                  (by rw [hxl]; omega) (Or.inl hsrc') hstep
                refine ⟨?_, ?_, ?_⟩
                · simp only [nextLevel]
                  exact covered_mf_of_yf _ _ _ _ _
                    (by rw [hlenD1, hxfLenE])
                    (by rw [hyfLenE, hxfLenE]) hcovE
                · intro habs
                  rw [hlast] at habs
                  simp at habs
                · intro _
                  simp only [nextLevel]
                  exact hcovE
              · rw [if_neg hw0y] at hpeninc
                have hplt : penOf sc w0 xsPre0 ysPre =
                    (p : Int) - wfaPo sc := by omega
                have hidx : (wfaPo sc).toNat - 1 < hist.length := by
                  omega
                have hget : hist[(wfaPo sc).toNat - 1]? =
                    some (hist[(wfaPo sc).toNat - 1]'hidx) :=
                  List.getElem?_eq_getElem hidx
                have hlvC := hhc _ _ hget
                have hlvlEq : (p : Int) - 1 -
                    (((wfaPo sc).toNat - 1 : Nat) : Int) =
                    (p : Int) - wfaPo sc := by omega
                rw [hlvlEq] at hlvC
                obtain ⟨hcM, _, _⟩ := hlvC w0 xsPre0 ysPre
                  (x :: xsRest) ysRest hxs' hysplit hvalid0 (by omega)
                obtain ⟨c0, hc0, hioff⟩ := hcM
                have hlvOK' := hh _ _ hget
                obtain ⟨hok0, hdiag0, _⟩ := hlvOK'.hmf.2 _ c0 hc0
                obtain ⟨c', hstep, hoff'⟩ := stepWith_gapY_covers sc
                  xs ys c0 _ hok0 xsPre0.length
                  (ysPre.length + (xs.length - xsPre0.length)) hioff
                  (by omega) (by omega) (by omega)
                have hsrc : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPo sc).toNat (·.mf))[
                      ysPre.length + (xs.length - xsPre0.length)]? =
                    some (some c0) := by
                  rw [frontAt_eq _ _ _ _ _ hget]
                  exact hc0
                have hsrc' : (frontAt (xs.length + ys.length + 1) hist
                    (wfaPo sc).toNat (·.mf))[
                      (ysPre.length +
                        (xs.length - (xsPre0 ++ [x]).length)) + 1]? =
                    some (some c0) := by
                  rw [← htEq]
                  exact hsrc
                have hcovE := covered_new_yf xs ys _ _ _ c0 c' hCyF.1
                  hBmF.1 (xsPre0 ++ [x]).length
                  (by rw [hxl]; omega) (Or.inr hsrc') hstep
                refine ⟨?_, ?_, ?_⟩
                · simp only [nextLevel]
                  exact covered_mf_of_yf _ _ _ _ _
                    (by rw [hlenD1, hxfLenE])
                    (by rw [hyfLenE, hxfLenE]) hcovE
                · intro habs
                  rw [hlast] at habs
                  simp at habs
                · intro _
                  simp only [nextLevel]
                  exact hcovE
        | diag =>
            have hx1 : 1 ≤ xsPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [xConsumed] at hvx
              omega
            have hy1 : 1 ≤ ysPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [yConsumed] at hvy
              omega
            rcases List.eq_nil_or_concat xsPre with hxnil |
              ⟨xsPre0, x, hxs0⟩
            · rw [hxnil] at hx1; simp at hx1
            rcases List.eq_nil_or_concat ysPre with hynil |
              ⟨ysPre0, y, hys0⟩
            · rw [hynil] at hy1; simp at hy1
            rw [List.concat_eq_append] at hxs0 hys0
            subst hxs0
            subst hys0
            have hxl : (xsPre0 ++ [x]).length = xsPre0.length + 1 :=
              by simp
            have hyl : (ysPre0 ++ [y]).length = ysPre0.length + 1 :=
              by simp
            have hvalid0 : IsMonotoneWalk w0 xsPre0 ysPre0 :=
              isMonotoneWalk_unsnoc_diag w0 xsPre0 ysPre0 x y hvalid
            have hpeninc := penOf_snoc_diag sc w0 xsPre0 ysPre0 x y
              hvalid0
            have hxs' : xs = xsPre0 ++ (x :: xsRest) := by
              rw [hxsplit, List.append_assoc]
              rfl
            have hys' : ys = ysPre0 ++ (y :: ysRest) := by
              rw [hysplit, List.append_assoc]
              rfl
            have hpen0nn := penOf_nonneg sc hr w0 xsPre0 ysPre0
              hvalid0
            have htEq : ysPre0.length + (xs.length - xsPre0.length) =
                (ysPre0 ++ [y]).length +
                  (xs.length - (xsPre0 ++ [x]).length) := by
              rw [hxl, hyl]; omega
            have hlast : lastPrev (w0 ++ [Step.diag]) none =
                some .diag := lastPrev_snoc w0 .diag none
            have hxc : xs[xsPre0.length]? = some x :=
              prefix_last_char xs xsPre0 x xsRest hxsplit
            have hyc : ys[ysPre0.length]? = some y :=
              prefix_last_char ys ysPre0 y ysRest hysplit
            by_cases hmatch : x = y
            · -- free extension: same level, shorter walk
              rw [if_pos hmatch] at hpeninc
              have hplt : penOf sc w0 xsPre0 ysPre0 =
                  (p : Int) := by omega
              obtain ⟨hcM0, _, _⟩ := ihN w0 xsPre0 ysPre0
                (x :: xsRest) (y :: ysRest)
                (by simp at hlen; omega) hxs' hys' hvalid0 hplt
              obtain ⟨v, hv, hvoff⟩ := hcM0
              refine ⟨?_, ?_, ?_⟩
              · rw [← htEq]
                by_cases hcase : (xsPre0 ++ [x]).length ≤ v.off
                · exact ⟨v, hv, hcase⟩
                · exfalso
                  have hveq : v.off = xsPre0.length := by
                    rw [hxl] at hcase
                    omega
                  have hclosedv := hlvOK.hclosed _ v hv
                  obtain ⟨hokv, hdiagv, _⟩ := hlvOK.hmf.2 _ v hv
                  have hjv : v.joff = ysPre0.length := by
                    rw [hveq] at hdiagv
                    omega
                  have hxlt : xsPre0.length < xs.length := by
                    rw [hxl] at hxpre_le
                    omega
                  have hylt : ysPre0.length < ys.length := by
                    rw [hyl] at hypre_le
                    omega
                  have hx_eq : xs[xsPre0.length] = x := by
                    rw [List.getElem?_eq_getElem hxlt] at hxc
                    exact Option.some.inj hxc
                  have hy_eq : ys[ysPre0.length] = y := by
                    rw [List.getElem?_eq_getElem hylt] at hyc
                    exact Option.some.inj hyc
                  exact hclosedv xs[xsPre0.length]
                    (xs.drop (xsPre0.length + 1)) ys[ysPre0.length]
                    (ys.drop (ysPre0.length + 1))
                    (by rw [hokv.hxs, hveq]
                        exact List.drop_eq_getElem_cons hxlt)
                    (by rw [hokv.hys, hjv]
                        exact List.drop_eq_getElem_cons hylt)
                    (by rw [hx_eq, hy_eq]; exact hmatch)
              · intro habs
                rw [hlast] at habs
                simp at habs
              · intro habs
                rw [hlast] at habs
                simp at habs
            · -- mismatch: source level L − px
              rw [if_neg hmatch] at hpeninc
              have hplt : penOf sc w0 xsPre0 ysPre0 =
                  (p : Int) - wfaPx sc := by omega
              have hidx : (wfaPx sc).toNat - 1 < hist.length := by
                omega
              have hget : hist[(wfaPx sc).toNat - 1]? =
                  some (hist[(wfaPx sc).toNat - 1]'hidx) :=
                List.getElem?_eq_getElem hidx
              have hlvC := hhc _ _ hget
              have hlvlEq : (p : Int) - 1 -
                  (((wfaPx sc).toNat - 1 : Nat) : Int) =
                  (p : Int) - wfaPx sc := by omega
              rw [hlvlEq] at hlvC
              obtain ⟨hcM, _, _⟩ := hlvC w0 xsPre0 ysPre0
                (x :: xsRest) (y :: ysRest) hxs' hys' hvalid0
                (by omega)
              obtain ⟨c0, hc0, hioff⟩ := hcM
              have hlvOK' := hh _ _ hget
              obtain ⟨hok0, hdiag0, _⟩ := hlvOK'.hmf.2 _ c0 hc0
              obtain ⟨c', hstep, hoff'⟩ := stepWith_diag_covers sc xs
                ys c0 _ hok0 xsPre0.length
                (ysPre0.length + (xs.length - xsPre0.length)) hioff
                (by omega) (by rw [hxl] at hxpre_le; omega)
                (by rw [hyl] at hypre_le; omega) (by omega)
              have hsrc : (frontAt (xs.length + ys.length + 1) hist
                  (wfaPx sc).toNat (·.mf))[
                    ysPre0.length + (xs.length - xsPre0.length)]? =
                  some (some c0) := by
                rw [frontAt_eq _ _ _ _ _ hget]
                exact hc0
              have hsrc' : (frontAt (xs.length + ys.length + 1) hist
                  (wfaPx sc).toNat (·.mf))[
                    (ysPre0 ++ [y]).length +
                      (xs.length - (xsPre0 ++ [x]).length)]? =
                  some (some c0) := by
                rw [← htEq]
                exact hsrc
              have hoff'' : (xsPre0 ++ [x]).length ≤ c'.off := by
                rw [hxl]
                exact hoff'
              refine ⟨?_, ?_, ?_⟩
              · simp only [nextLevel]
                exact covered_mf_of_diag xs ys _ _ _ _ c0 c'
                  (by rw [hEmF.1, hxfLenE])
                  (by rw [hyfLenE, hxfLenE]) _ hoff'' hsrc' hstep
              · intro habs
                rw [hlast] at habs
                simp at habs
              · intro habs
                rw [hlast] at habs
                simp at habs

-- ══════════════════════════════════════════════════════════════════
-- PROOFS, LAYER 6d: the seed level is complete; the loop is optimal
-- ══════════════════════════════════════════════════════════════════

theorem seedLevel_complete (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char) :
    LevelComplete sc xs ys 0
      (seedLevel xs.length (xs.length + ys.length + 1) xs ys) := by
  have hO := hr.open_neg
  have hpo1 : 1 ≤ wfaPo sc := by unfold wfaPo; omega
  have hlvOK := seedLevel_sound sc xs ys
  suffices H : ∀ (N : Nat) (w : List Step)
      (xsPre ysPre xsRest ysRest : List Char),
      w.length ≤ N → xs = xsPre ++ xsRest → ys = ysPre ++ ysRest →
      IsMonotoneWalk w xsPre ysPre →
      penOf sc w xsPre ysPre = 0 →
      Covered (seedLevel xs.length (xs.length + ys.length + 1)
          xs ys).mf
        (ysPre.length + (xs.length - xsPre.length)) xsPre.length by
    intro w xsPre ysPre xsRest ysRest h1 h2 h3 h4
    refine ⟨H w.length w xsPre ysPre xsRest ysRest (Nat.le_refl _) h1
      h2 h3 h4, ?_, ?_⟩
    · intro hend
      exfalso
      rcases List.eq_nil_or_concat w with rfl | ⟨w0, last, hwc⟩
      · simp [lastPrev] at hend
      · rw [List.concat_eq_append] at hwc
        subst hwc
        rw [lastPrev_snoc] at hend
        have hlast : last = .gapX := Option.some.inj hend
        subst hlast
        obtain ⟨hvx, hvy⟩ := h3
        have hy1 : 1 ≤ ysPre.length := by
          simp [yConsumed] at hvy
          omega
        rcases List.eq_nil_or_concat ysPre with rfl | ⟨ys0, y, hys0⟩
        · simp at hy1
        · rw [List.concat_eq_append] at hys0
          subst hys0
          have hvalid0 : IsMonotoneWalk w0 xsPre ys0 :=
            isMonotoneWalk_unsnoc_gapX w0 xsPre ys0 y ⟨hvx, hvy⟩
          have hpeninc := penOf_snoc_gapX sc w0 xsPre ys0 y hvalid0
          have hnn := penOf_nonneg sc hr w0 xsPre ys0 hvalid0
          by_cases hb : lastPrev w0 none = some Step.gapX
          · rw [if_pos hb] at hpeninc
            omega
          · rw [if_neg hb] at hpeninc
            omega
    · intro hend
      exfalso
      rcases List.eq_nil_or_concat w with rfl | ⟨w0, last, hwc⟩
      · simp [lastPrev] at hend
      · rw [List.concat_eq_append] at hwc
        subst hwc
        rw [lastPrev_snoc] at hend
        have hlast : last = .gapY := Option.some.inj hend
        subst hlast
        obtain ⟨hvx, hvy⟩ := h3
        have hx1 : 1 ≤ xsPre.length := by
          simp [xConsumed] at hvx
          omega
        rcases List.eq_nil_or_concat xsPre with rfl | ⟨xs0, x, hxs0⟩
        · simp at hx1
        · rw [List.concat_eq_append] at hxs0
          subst hxs0
          have hvalid0 : IsMonotoneWalk w0 xs0 ysPre :=
            isMonotoneWalk_unsnoc_gapY w0 xs0 ysPre x ⟨hvx, hvy⟩
          have hpeninc := penOf_snoc_gapY sc w0 xs0 ysPre x hvalid0
          have hnn := penOf_nonneg sc hr w0 xs0 ysPre hvalid0
          by_cases hb : lastPrev w0 none = some Step.gapY
          · rw [if_pos hb] at hpeninc
            omega
          · rw [if_neg hb] at hpeninc
            omega
  intro N
  induction N with
  | zero =>
      intro w xsPre ysPre xsRest ysRest hlen h1 h2 hv hpen
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      obtain ⟨hvx, hvy⟩ := hv
      simp at hvx hvy
      have hxnil : xsPre = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      have hynil : ysPre = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst hxnil
      subst hynil
      -- the seed cell covers offset 0 on diagonal m
      refine ⟨extendCell ⟨0, 0, xs, ys, []⟩, ?_, by omega⟩
      show ((emptyFront (xs.length + ys.length + 1)).set xs.length
        (some (extendCell ⟨0, 0, xs, ys, []⟩)))[
          [].length + (xs.length - ([] : List Char).length)]? = _
      have ht : ([] : List Char).length +
          (xs.length - ([] : List Char).length) = xs.length := by
        simp
      rw [ht, List.getElem?_set, if_pos rfl,
        if_pos (by simp [emptyFront]; omega)]
  | succ N ihN =>
      intro w xsPre ysPre xsRest ysRest hlen hxsplit hysplit hvalid
        hpen
      have hxpre_le : xsPre.length ≤ xs.length := by
        rw [hxsplit, List.length_append]; omega
      have hypre_le : ysPre.length ≤ ys.length := by
        rw [hysplit, List.length_append]; omega
      rcases List.eq_nil_or_concat w with hwnil | ⟨w0, last, hwc⟩
      · subst hwnil
        obtain ⟨hvx, hvy⟩ := hvalid
        simp at hvx hvy
        have hxnil : xsPre = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        have hynil : ysPre = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        subst hxnil
        subst hynil
        refine ⟨extendCell ⟨0, 0, xs, ys, []⟩, ?_, by omega⟩
        show ((emptyFront (xs.length + ys.length + 1)).set xs.length
          (some (extendCell ⟨0, 0, xs, ys, []⟩)))[
            [].length + (xs.length - ([] : List Char).length)]? = _
        have ht : ([] : List Char).length +
            (xs.length - ([] : List Char).length) = xs.length := by
          simp
        rw [ht, List.getElem?_set, if_pos rfl,
          if_pos (by simp [emptyFront]; omega)]
      · rw [List.concat_eq_append] at hwc
        subst hwc
        cases last with
        | gapX =>
            exfalso
            obtain ⟨hvx, hvy⟩ := hvalid
            have hy1 : 1 ≤ ysPre.length := by
              simp [yConsumed] at hvy
              omega
            rcases List.eq_nil_or_concat ysPre with rfl |
              ⟨ys0, y, hys0⟩
            · simp at hy1
            · rw [List.concat_eq_append] at hys0
              subst hys0
              have hvalid0 : IsMonotoneWalk w0 xsPre ys0 :=
                isMonotoneWalk_unsnoc_gapX w0 xsPre ys0 y ⟨hvx, hvy⟩
              have hpeninc := penOf_snoc_gapX sc w0 xsPre ys0 y
                hvalid0
              have hnn := penOf_nonneg sc hr w0 xsPre ys0 hvalid0
              by_cases hb : lastPrev w0 none = some Step.gapX
              · rw [if_pos hb] at hpeninc
                omega
              · rw [if_neg hb] at hpeninc
                omega
        | gapY =>
            exfalso
            obtain ⟨hvx, hvy⟩ := hvalid
            have hx1 : 1 ≤ xsPre.length := by
              simp [xConsumed] at hvx
              omega
            rcases List.eq_nil_or_concat xsPre with rfl |
              ⟨xs0, x, hxs0⟩
            · simp at hx1
            · rw [List.concat_eq_append] at hxs0
              subst hxs0
              have hvalid0 : IsMonotoneWalk w0 xs0 ysPre :=
                isMonotoneWalk_unsnoc_gapY w0 xs0 ysPre x ⟨hvx, hvy⟩
              have hpeninc := penOf_snoc_gapY sc w0 xs0 ysPre x
                hvalid0
              have hnn := penOf_nonneg sc hr w0 xs0 ysPre hvalid0
              by_cases hb : lastPrev w0 none = some Step.gapY
              · rw [if_pos hb] at hpeninc
                omega
              · rw [if_neg hb] at hpeninc
                omega
        | diag =>
            have hx1 : 1 ≤ xsPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [xConsumed] at hvx
              omega
            have hy1 : 1 ≤ ysPre.length := by
              obtain ⟨hvx, hvy⟩ := hvalid
              simp [yConsumed] at hvy
              omega
            rcases List.eq_nil_or_concat xsPre with hxnil |
              ⟨xsPre0, x, hxs0⟩
            · rw [hxnil] at hx1; simp at hx1
            rcases List.eq_nil_or_concat ysPre with hynil |
              ⟨ysPre0, y, hys0⟩
            · rw [hynil] at hy1; simp at hy1
            rw [List.concat_eq_append] at hxs0 hys0
            subst hxs0
            subst hys0
            have hxl : (xsPre0 ++ [x]).length = xsPre0.length + 1 :=
              by simp
            have hyl : (ysPre0 ++ [y]).length = ysPre0.length + 1 :=
              by simp
            have hvalid0 : IsMonotoneWalk w0 xsPre0 ysPre0 :=
              isMonotoneWalk_unsnoc_diag w0 xsPre0 ysPre0 x y hvalid
            have hpeninc := penOf_snoc_diag sc w0 xsPre0 ysPre0 x y
              hvalid0
            have hpen0nn := penOf_nonneg sc hr w0 xsPre0 ysPre0
              hvalid0
            have hxs' : xs = xsPre0 ++ (x :: xsRest) := by
              rw [hxsplit, List.append_assoc]
              rfl
            have hys' : ys = ysPre0 ++ (y :: ysRest) := by
              rw [hysplit, List.append_assoc]
              rfl
            have hxc : xs[xsPre0.length]? = some x :=
              prefix_last_char xs xsPre0 x xsRest hxsplit
            have hyc : ys[ysPre0.length]? = some y :=
              prefix_last_char ys ysPre0 y ysRest hysplit
            by_cases hmatch : x = y
            · rw [if_pos hmatch] at hpeninc
              have hplt : penOf sc w0 xsPre0 ysPre0 = 0 := by omega
              have hcM0 := ihN w0 xsPre0 ysPre0 (x :: xsRest)
                (y :: ysRest) (by simp at hlen; omega) hxs' hys'
                hvalid0 hplt
              obtain ⟨v, hv, hvoff⟩ := hcM0
              have htEq : ysPre0.length +
                  (xs.length - xsPre0.length) =
                  (ysPre0 ++ [y]).length +
                    (xs.length - (xsPre0 ++ [x]).length) := by
                rw [hxl, hyl]; omega
              rw [← htEq]
              by_cases hcase : (xsPre0 ++ [x]).length ≤ v.off
              · exact ⟨v, hv, hcase⟩
              · exfalso
                have hveq : v.off = xsPre0.length := by
                  rw [hxl] at hcase
                  omega
                have hclosedv := hlvOK.hclosed _ v hv
                obtain ⟨hokv, hdiagv, _⟩ := hlvOK.hmf.2 _ v hv
                have hjv : v.joff = ysPre0.length := by
                  rw [hveq] at hdiagv
                  omega
                have hxlt : xsPre0.length < xs.length := by
                  rw [hxl] at hxpre_le
                  omega
                have hylt : ysPre0.length < ys.length := by
                  rw [hyl] at hypre_le
                  omega
                have hx_eq : xs[xsPre0.length] = x := by
                  rw [List.getElem?_eq_getElem hxlt] at hxc
                  exact Option.some.inj hxc
                have hy_eq : ys[ysPre0.length] = y := by
                  rw [List.getElem?_eq_getElem hylt] at hyc
                  exact Option.some.inj hyc
                exact hclosedv xs[xsPre0.length]
                  (xs.drop (xsPre0.length + 1)) ys[ysPre0.length]
                  (ys.drop (ysPre0.length + 1))
                  (by rw [hokv.hxs, hveq]
                      exact List.drop_eq_getElem_cons hxlt)
                  (by rw [hokv.hys, hjv]
                      exact List.drop_eq_getElem_cons hylt)
                  (by rw [hx_eq, hy_eq]; exact hmatch)
            · exfalso
              rw [if_neg hmatch] at hpeninc
              omega

-- The corner appears as soon as the match front covers it.
theorem cornerOf_of_covered (sc : Scoring) (xs ys : List Char)
    (p : Int) (lv : WLevel) (hlv : LevelOK sc xs ys p lv)
    (hcov : Covered lv.mf ys.length xs.length) :
    ∃ c, cornerOf ys.length lv = some c := by
  obtain ⟨c, hc, hoff⟩ := hcov
  obtain ⟨hok, hdiag, _⟩ := hlv.hmf.2 _ c hc
  have hoffm : c.off = xs.length := by
    have := hok.hoff
    omega
  have hjoffn : c.joff = ys.length := by omega
  have hxrem : c.xsRem = [] := by
    rw [hok.hxs, hoffm, List.drop_length]
  have hyrem : c.ysRem = [] := by
    rw [hok.hys, hjoffn, List.drop_length]
  refine ⟨c, ?_⟩
  unfold cornerOf
  rw [hc]
  dsimp only
  rw [hxrem, hyrem]

theorem histComplete_singleton (sc : Scoring) (xs ys : List Char)
    (lv0 : WLevel) (h0 : LevelComplete sc xs ys 0 lv0) :
    HistComplete sc xs ys 1 [lv0] := by
  intro d lv hd
  cases d with
  | zero =>
      simp at hd
      have heq : ((1 : Nat) : Int) - 1 - ((0 : Nat) : Int) = 0 := by
        omega
      rw [heq, ← hd]
      exact h0
  | succ d => simp at hd

theorem histComplete_take (sc : Scoring) (xs ys : List Char)
    (p k : Nat) (hist : List WLevel)
    (hh : HistComplete sc xs ys p hist) :
    HistComplete sc xs ys p (hist.take k) := by
  intro d lv hd
  rw [List.getElem?_take] at hd
  by_cases hdk : d < k
  · rw [if_pos hdk] at hd
    exact hh d lv hd
  · rw [if_neg hdk] at hd
    simp at hd

theorem histComplete_cons (sc : Scoring) (xs ys : List Char)
    (p : Nat) (hist : List WLevel) (lv : WLevel)
    (hh : HistComplete sc xs ys p hist)
    (hlv : LevelComplete sc xs ys (p : Int) lv) :
    HistComplete sc xs ys (p + 1) (lv :: hist) := by
  intro d lv' hd
  cases d with
  | zero =>
      simp at hd
      have heq : ((p + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int) =
          (p : Int) := by omega
      rw [heq, ← hd]
      exact hlv
  | succ d =>
      rw [List.getElem?_cons_succ] at hd
      have hlv' := hh d lv' hd
      have heq : ((p + 1 : Nat) : Int) - 1 - ((d + 1 : Nat) : Int) =
          (p : Int) - 1 - (d : Int) := by omega
      rw [heq]
      exact hlv'


/-- Loop optimality: the walk the loop returns has minimal penalty.
The invariant is walk-level — "every complete alignment has penalty at
least the current level" — maintained by completeness of each new
level plus its empty corner, so it survives history truncation. -/
theorem wfaLoop_opt (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char) :
    ∀ (fuel : Nat) (p : Nat) (hist : List WLevel),
      HistOK sc xs ys p hist → HistComplete sc xs ys p hist →
      1 ≤ p →
      hist.length = min p (max (wfaPe sc).toNat
        (max (wfaPo sc).toNat (wfaPx sc).toNat)) →
      (∀ w2, IsMonotoneWalk w2 xs ys →
        (p : Int) ≤ penOf sc w2 xs ys) →
      ∀ c, wfaLoop xs ys (xs.length + ys.length + 1) ys.length
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat fuel hist =
          some c →
      ∀ w', IsMonotoneWalk w' xs ys →
        penOf sc c.walk.reverse xs ys ≤ penOf sc w' xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hist _ _ _ _ _ c h
      simp [wfaLoop] at h
  | succ fuel ih =>
      intro p hist hh hhc hp1 hwin hinv c h w' hw'
      have hK1 : 1 ≤ max (wfaPe sc).toNat
          (max (wfaPo sc).toNat (wfaPx sc).toNat) := by omega
      have hlv := nextLevel_sound sc hr hpe1 hpx1 xs ys p hist hh
      have hlvC := nextLevel_complete sc hr hpe1 hpx1 xs ys p hist hh
        hhc hp1 hwin
      simp only [wfaLoop] at h
      cases hcorner : cornerOf ys.length
          (nextLevel xs ys (xs.length + ys.length + 1)
            (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist)
        with
      | some c0 =>
          rw [hcorner] at h
          simp at h
          subst h
          have hpenc := (cornerOf_sound sc xs ys _ _ hlv c0
            hcorner).2
          have := hinv w' hw'
          omega
      | none =>
          rw [hcorner] at h
          have hinv' : ∀ w2, IsMonotoneWalk w2 xs ys →
              ((p + 1 : Nat) : Int) ≤ penOf sc w2 xs ys := by
            intro w2 hw2
            have hge := hinv w2 hw2
            rcases Int.lt_or_le (p : Int) (penOf sc w2 xs ys) with
              hlt | hle
            · omega
            · exfalso
              have hpeq : penOf sc w2 xs ys = (p : Int) := by omega
              obtain ⟨hcM, _, _⟩ := hlvC w2 xs ys [] [] (by simp)
                (by simp) hw2 hpeq
              have ht : ys.length + (xs.length - xs.length) =
                  ys.length := by omega
              rw [ht] at hcM
              obtain ⟨cq, hcq⟩ := cornerOf_of_covered sc xs ys _ _
                hlv hcM
              rw [hcorner] at hcq
              simp at hcq
          exact ih (p + 1)
            ((nextLevel xs ys (xs.length + ys.length + 1)
                (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat
                hist :: hist).take
              (max (wfaPe sc).toNat (max (wfaPo sc).toNat
                (wfaPx sc).toNat)))
            (histOK_take sc xs ys (p + 1) _ _
              (histOK_cons sc xs ys p hist _ hh hlv))
            (histComplete_take sc xs ys (p + 1) _ _
              (histComplete_cons sc xs ys p hist _ hhc hlvC))
            (by omega)
            (by rw [List.length_take, List.length_cons, hwin]; omega)
            hinv' c h w' hw'

/-- Run optimality: the returned walk's penalty is minimal. -/
theorem wfaRun_opt (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaRun sc xs ys = some (w, s)) :
    ∀ w', IsMonotoneWalk w' xs ys →
      penOf sc w xs ys ≤ penOf sc w' xs ys := by
  intro w' hw'
  have hseed := seedLevel_sound sc xs ys
  simp only [wfaRun] at h
  cases hc0 : cornerOf ys.length
      (seedLevel xs.length (xs.length + ys.length + 1) xs ys) with
  | some c =>
      rw [hc0] at h
      simp at h
      obtain ⟨hw, _⟩ := h
      have hpen := (cornerOf_sound sc xs ys 0 _ hseed c hc0).2
      have hnn := penOf_nonneg sc hr w' xs ys hw'
      rw [← hw]
      omega
  | none =>
      rw [hc0] at h
      cases hl : wfaLoop xs ys (xs.length + ys.length + 1) ys.length
          (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat
          ((xs.length + ys.length + 2) * (wfaPo sc).toNat + 1)
          [seedLevel xs.length (xs.length + ys.length + 1) xs ys] with
      | none => rw [hl] at h; simp at h
      | some c =>
          rw [hl] at h
          simp at h
          obtain ⟨hw, _⟩ := h
          rw [← hw]
          exact wfaLoop_opt sc hr hpe1 hpx1 xs ys _ 1 _
            (histOK_singleton sc xs ys _ hseed)
            (histComplete_singleton sc xs ys _
              (seedLevel_complete sc hr hpe1 hpx1 xs ys))
            (by omega)
            (by simp; omega)
            (by intro w2 hw2
                have hnn := penOf_nonneg sc hr w2 xs ys hw2
                rcases Int.lt_or_le 0 (penOf sc w2 xs ys) with
                  hlt | hle
                · omega
                · exfalso
                  have hpeq : penOf sc w2 xs ys = 0 := by omega
                  obtain ⟨hcM, _, _⟩ := (seedLevel_complete sc hr
                    hpe1 hpx1 xs ys) w2 xs ys [] [] (by simp)
                    (by simp) hw2 hpeq
                  have ht : ys.length + (xs.length - xs.length) =
                      ys.length := by omega
                  rw [ht] at hcM
                  obtain ⟨cq, hcq⟩ := cornerOf_of_covered sc xs ys 0
                    _ hseed hcM
                  rw [hc0] at hcq
                  simp at hcq)
            c hl w' hw'

/-- THEOREM T2 (unconditional): the true WFA returns exactly the
frozen specification's optimal score. -/
theorem wfaAlign_score (sc : Scoring) (xs ys : List Char) :
    (wfaAlign sc xs ys).map (fun r => r.2) =
      (getBestAlignment sc xs ys).map (fun r => r.2) := by
  unfold wfaAlign
  rw [wfaRunT_eq]
  by_cases hg : wfaGateB sc
  · rw [if_pos hg]
    obtain ⟨hr, hpe1, hpx1⟩ := wfaGate_spec sc hg
    cases hrun : wfaRun sc xs ys with
    | none => rw [gotohFusedAlign_equals_getBestAlignment]
    | some r =>
        obtain ⟨w, s⟩ := r
        obtain ⟨hvalid, hscore⟩ := wfaRun_sound sc hr hpe1 hpx1 xs ys
          w s hrun
        obtain ⟨⟨bp, bs⟩, hbest⟩ := getBestAlignment_returns_some sc
          xs ys
        obtain ⟨hbvalid, hbscore⟩ :=
          getBestAlignment_returns_a_valid_walk sc xs ys bp bs hbest
        have h1 : walkScore sc xs ys w ≤ bs :=
          getBestAlignment_returns_a_maximum_score sc xs ys bp bs w
            hbest hvalid
        have h2 : penOf sc w xs ys ≤ penOf sc bp xs ys :=
          wfaRun_opt sc hr hpe1 hpx1 xs ys w s hrun bp hbvalid
        have hsbs : s = bs := by
          rw [penOf, penOf] at h2
          unfold walkScore at hscore hbscore h1
          omega
        rw [hbest]
        simp only [Option.map_some]
        rw [hsbs]
  · rw [if_neg hg]
    rw [gotohFusedAlign_equals_getBestAlignment]

/-- The adaptive algorithm never returns `none`. -/
theorem wfaAlign_isSome (sc : Scoring) (xs ys : List Char) :
    (wfaAlign sc xs ys).isSome := by
  obtain ⟨best, hbest⟩ := getBestAlignment_returns_some sc xs ys
  have := wfaAlign_score sc xs ys
  rw [hbest] at this
  cases hw : wfaAlign sc xs ys with
  | none => rw [hw] at this; simp at this
  | some r => rfl

-- ══════════════════════════════════════════════════════════════════
-- Compile-time witnesses
-- ══════════════════════════════════════════════════════════════════

#guard wfaGateB demoScoring
#guard wfaAlign demoScoring ['A','B','C'] ['A','B','B','C']
  == getBestAlignment demoScoring ['A','B','C'] ['A','B','B','C']
#guard wfaAlign demoScoring ['A','C','B'] ['A','C','B']
  == some ([.diag, .diag, .diag], 6)
#guard wfaAlign demoScoring [] ['A','B'] == some ([.gapX, .gapX], -5)
#guard wfaAlign demoScoring ['A','B'] [] == some ([.gapY, .gapY], -5)
#guard wfaAlign demoScoring [] [] == some ([], 0)
#guard wfaAlign demoScoring ['A','B','B','A'] ['A','A']
  == some ([.diag, .gapY, .gapY, .diag], -1)

end AlignmentSpec
