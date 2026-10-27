import AlignmentWfaRuns

/-!
SPEED PROBE — NOT A KERNEL, NOT PROVEN, NOT IN THE HARNESS.

Same forward offsets-only WFA recurrence as the proven `wfak` kernel
(`nextLevelP` in AlignmentWfaPoint.lean: pushX/pushY/pushD with boundary
demotion, left-biased `betterR`, free extension), re-implemented to
measure how much of the proven kernel's per-cell cost is representation:

* fronts are `Array UInt32` (a UInt32 is boxed as a tagged scalar on
  64-bit Lean: no allocation per cell) and all per-cell arithmetic is
  UInt32;
* every front is padded with `margin` zero cells on both sides, so a
  read from a source level needs no band test (an out-of-band read hits
  a padding zero = "no offset");
* the three fronts of a level are built in one recursion over the band
  (a `for` loop with several `let mut` variables allocates a state tuple
  per iteration; a recursion passes the state in registers);
* when the three penalties are equal (pa-bench's unit cost: pe = po = px)
  every source is the same level, the gap fronts are `pushX`/`pushY` of
  that level's M front (M ≥ X, Y pointwise and the pushes are monotone),
  so only the M front is stored and each cell reads one source value
  through a sliding window (`uFillSingle`); the traceback recomputes the
  gap-front values it needs;
* the first character comparison of the free extension is inline
  (`uextI`); the proven `lcpArr` loop is entered only after a match.

The result is checked at runtime exactly like `certifiedRuns` (the proven
run checker `checkRuns` + the offsets score identity 2 s + L = match·(m+n)),
so a wrong walk cannot be reported; optimality of the corner level L is
what a proof would have to add (by refinement to `nextLevelP`, as
AlignmentWfaOffR/AlignmentWfaPoint do for the current kernel).

Algorithm references: Marco-Sola et al. 2021 (WFA), WFA2-lib's packed
offsets and backtrace (github.com/smarco/WFA2-lib).  Profile that
motivated it (macOS `sample`, 2026-09-11, wfak on 10 kb / 5 %): ~75 % in
the three `arrayBuildGo` front builders, ~17 % in `lcpArrGo`.
-/
namespace AlignmentSpec

/-- One level: fronts sharing a band.  Index of diagonal `t` is
`t + margin - lo`; `w = 0` means the level is empty.  In single-source
mode `xf`/`yf` are empty and derived on demand. -/
structure ULevel where
  lo : Nat
  w  : Nat
  mf : Array UInt32
  xf : Array UInt32
  yf : Array UInt32
deriving Inhabited

def uEmpty : ULevel := ⟨0, 0, #[], #[], #[]⟩

/-- `0` = none, `k+1` = offset `k` (the `RFront` code). -/
@[inline] def ubetter (a b : UInt32) : UInt32 := if b ≤ a then a else b

@[inline] def upushX (m n t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := off + t - m
    if j < n then a else if 1 ≤ off && 1 ≤ j then off else 0

@[inline] def upushY (m t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    if off < m then a + 1 else if 1 ≤ off && 1 ≤ (off + t - m) then a else 0

@[inline] def upushD (m n t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := off + t - m
    if off < m && j < n then a + 1 else if 1 ≤ off && 1 ≤ j then a else 0

/-- Free extension with the first comparison inline; `lcpArr` is the proven
kernel's LCP loop. -/
@[inline] def uextI (m n : UInt32) (xa ya : Array Char) (t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := off + t - m
    if off < m && j < n && xa[off.toNat]! == ya[j.toNat]! then
      off + 2 + (lcpArr xa ya (off.toNat + 1) (j.toNat + 1)).toUInt32
    else a

def pushZeros : Nat → Array UInt32 → Array UInt32
  | 0, a => a
  | k + 1, a => pushZeros k (a.push 0)

/-- General cell loop: five source reads per cell, three fronts stored. -/
def uFillGo (xa ya : Array Char) (m32 n32 : UInt32) (len lo : Nat)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm : Nat) :
    Nat → Nat → UInt32 → Array UInt32 → Array UInt32 → Array UInt32 →
    Array UInt32 × Array UInt32 × Array UInt32
  | 0, _, _, mf, xf, yf => (mf, xf, yf)
  | k + 1, i, t32, mf, xf, yf =>
    let x : UInt32 :=
      if t32 = 0 then 0 else
        ubetter (upushX m32 n32 (t32 - 1) (xeA.getD (i + shXe - 1) 0))
                (upushX m32 n32 (t32 - 1) (xoA.getD (i + shXo - 1) 0))
    let y : UInt32 :=
      if lo + i + 1 < len then
        ubetter (upushY m32 (t32 + 1) (yeA.getD (i + shYe + 1) 0))
                (upushY m32 (t32 + 1) (yoA.getD (i + shYo + 1) 0))
      else 0
    let d := upushD m32 n32 t32 (dmA.getD (i + shDm) 0)
    let e := uextI m32 n32 xa ya t32 (ubetter (ubetter d x) y)
    uFillGo xa ya m32 n32 len lo xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm
      k (i + 1) (t32 + 1) (mf.push e) (xf.push x) (yf.push y)

/-- Single-source cell loop (pe = po = px): one read per cell through a
sliding window over the source M front; only the M front is stored. -/
def uFillSingle (xa ya : Array Char) (m32 n32 : UInt32) (len lo : Nat)
    (srcA : Array UInt32) (sh : Nat) :
    Nat → Nat → UInt32 → UInt32 → UInt32 → Array UInt32 → Array UInt32
  | 0, _, _, _, _, mf => mf
  | k + 1, i, t32, prev, cur, mf =>
    let next := srcA.getD (i + sh + 1) 0
    let x : UInt32 := if t32 = 0 then 0 else upushX m32 n32 (t32 - 1) prev
    let y : UInt32 := if lo + i + 1 < len then upushY m32 (t32 + 1) next else 0
    let d := upushD m32 n32 t32 cur
    let e := uextI m32 n32 xa ya t32 (ubetter (ubetter d x) y)
    uFillSingle xa ya m32 n32 len lo srcA sh k (i + 1) (t32 + 1) cur next (mf.push e)

/-- Band of the next level: union of the source bands, expanded by one,
clipped to `[0, len)`. -/
@[inline] def uBand (len : Nat) (srcs : List ULevel) : Nat × Nat :=
  let lo := srcs.foldl (fun lo s => if s.w > 0 then min lo (s.lo - 1) else lo) len
  let hi := srcs.foldl (fun hi s => if s.w > 0 then max hi (s.lo + s.w + 1) else hi) 0
  (lo, min hi len)

/-- Build level `L` from its sources (general path).  `margin ≥ maxDelta + 2`
makes every source read fall inside the source's padded array or its zero
padding. -/
def uLevel (m n len : Nat) (xa ya : Array Char) (margin : Nat)
    (xe xo ye yo dm : ULevel) : ULevel :=
  let (lo, hi) := uBand len [xe, xo, ye, yo, dm]
  if hi ≤ lo then uEmpty else
  let w := hi - lo
  let size := w + 2 * margin
  let (mf, xf, yf) := uFillGo xa ya m.toUInt32 n.toUInt32 len lo
    xe.xf xo.mf ye.yf yo.mf dm.mf
    (margin + lo - xe.lo) (margin + lo - xo.lo) (margin + lo - ye.lo) (margin + lo - yo.lo) (margin + lo - dm.lo)
    w 0 lo.toUInt32 (pushZeros margin (Array.mkEmpty size)) (pushZeros margin (Array.mkEmpty size))
    (pushZeros margin (Array.mkEmpty size))
  ⟨lo, w, pushZeros margin mf, pushZeros margin xf, pushZeros margin yf⟩

/-- Build level `L` when all three penalties are equal (single source). -/
def uLevelSingle (m n len : Nat) (xa ya : Array Char) (margin : Nat) (src : ULevel) : ULevel :=
  let (lo, hi) := uBand len [src]
  if hi ≤ lo then uEmpty else
  let w := hi - lo
  let sh := margin + lo - src.lo
  let mf := uFillSingle xa ya m.toUInt32 n.toUInt32 len lo src.mf sh
    w 0 lo.toUInt32 (src.mf.getD (sh - 1) 0) (src.mf.getD sh 0) (pushZeros margin (Array.mkEmpty (w + 2 * margin)))
  ⟨lo, w, pushZeros margin mf, #[], #[]⟩

/-- Value of a front at diagonal `t` (0 outside the band). -/
@[inline] def uget (margin : Nat) (lv : ULevel) (sel : ULevel → Array UInt32) (t : Nat) : UInt32 :=
  if lv.w = 0 then 0 else (sel lv).getD (t + margin - lv.lo) 0

/-- Forward run: level history and the corner level `L`. -/
def uRun (m n : Nat) (xa ya : Array Char) (pe po px : Nat) (fuel : Nat) :
    Option (Nat × Array ULevel) := Id.run do
  let len := m + n + 1
  let margin := max pe (max po px) + 2
  let single := pe == po && po == px
  let seed : ULevel :=
    let mf := pushZeros margin ((pushZeros margin (Array.mkEmpty (2 * margin + 1))).push
      ((lcpArr xa ya 0 0).toUInt32 + 1))
    let z : Array UInt32 := if single then #[] else Array.replicate (2 * margin + 1) 0
    ⟨m, 1, mf, z, z⟩
  let corner := fun (lv : ULevel) => uget margin lv (·.mf) n == m.toUInt32 + 1
  if corner seed then return some (0, #[seed])
  let mut hist : Array ULevel := #[seed]
  let mut L := 1
  let mut f := fuel
  while f > 0 do
    let src := fun (d : Nat) => if d ≤ L then hist[L - d]! else uEmpty
    let lv := if single then uLevelSingle m n len xa ya margin (src pe)
              else uLevel m n len xa ya margin (src pe) (src po) (src pe) (src po) (src px)
    hist := hist.push lv
    if corner lv then return some (L, hist)
    L := L + 1
    f := f - 1
  return none

/-- Direct run traceback over the U32 history: the same predecessor rules
and tie order as `traceRuns` (AlignmentTraceRuns.lean).  In single-source
mode the gap-front values are recomputed from the M fronts.  Returns `[]`
to request the proven fallback when boundary surgery would be needed. -/
def uTraceRuns (m n : Nat) (pe po px margin : Nat) (single : Bool) (hist : Array ULevel)
    (L : Nat) : List (Step × Nat) := Id.run do
  let mI : Int := m
  let nI : Int := n
  let len := m + n + 1
  let m32 := m.toUInt32
  let n32 := n.toUInt32
  let code (a : UInt32) : Int := (a.toNat : Int) - 1
  let getM (L' t : Nat) : UInt32 := if L' < hist.size then uget margin hist[L']! (·.mf) t else 0
  let getX (L' t : Nat) : Int :=
    if single then
      code (if pe ≤ L' && t ≥ 1 then upushX m32 n32 (t - 1).toUInt32 (getM (L' - pe) (t - 1)) else 0)
    else code (if L' < hist.size then uget margin hist[L']! (·.xf) t else 0)
  let getY (L' t : Nat) : Int :=
    if single then
      code (if pe ≤ L' && t + 1 < len then upushY m32 (t + 1).toUInt32 (getM (L' - pe) (t + 1)) else 0)
    else code (if L' < hist.size then uget margin hist[L']! (·.yf) t else 0)
  let mut w : List (Step × Nat) := []
  let mut L := L
  let mut t := n
  let mut front : Nat := 0
  let mut off : Int := code (getM L n)
  let mut fuel := 4 * (m + n) + 8
  while fuel > 0 do
    fuel := fuel - 1
    if front == 0 then
      let x := getX L t
      let y := getY L t
      let s := if px ≤ L then code (getM (L - px) t) else -1
      let j := traceJoff mI t s
      let e : Int := if s < 0 then -1 else if s < mI && j < nI then s + 1
                     else if s ≥ 1 && j ≥ 1 then s else -1
      let b1 := if x ≤ e then e else x
      let b := if L == 0 then (0 : Int) else if y ≤ b1 then b1 else y
      let k := off - b
      if k > 0 then w := (.diag, k.toNat) :: w
      if L == 0 then break
      if b == e && (x ≤ e) && (y ≤ b1) then
        if s < mI && j < nI then w := (.diag, 1) :: w
        else return []
        L := L - px; front := 0; off := s
      else if b == b1 then
        front := 1; off := x
      else
        front := 2; off := y
    else if front == 1 then
      let sa := if pe ≤ L && t ≥ 1 then getX (L - pe) (t - 1) else -1
      let sb := if po ≤ L && t ≥ 1 then code (getM (L - po) (t - 1)) else -1
      let ja := traceJoff mI (t - 1 : Nat) sa
      let jb := traceJoff mI (t - 1 : Nat) sb
      let a : Int := if sa < 0 then -1 else if ja < nI then sa else if sa ≥ 1 && ja ≥ 1 then sa - 1 else -1
      let b : Int := if sb < 0 then -1 else if jb < nI then sb else if sb ≥ 1 && jb ≥ 1 then sb - 1 else -1
      if b ≤ a then
        L := L - pe; front := 1; off := sa
      else
        L := L - po; front := 0; off := sb
      w := (.gapX, 1) :: w
      t := t - 1
    else
      let sa := if pe ≤ L && t + 1 < len then getY (L - pe) (t + 1) else -1
      let sb := if po ≤ L && t + 1 < len then code (getM (L - po) (t + 1)) else -1
      let ja := traceJoff mI (t + 1) sa
      let jb := traceJoff mI (t + 1) sb
      let a : Int := if sa < 0 then -1 else if sa < mI then sa + 1 else if sa ≥ 1 && ja ≥ 1 then sa else -1
      let b : Int := if sb < 0 then -1 else if sb < mI then sb + 1 else if sb ≥ 1 && jb ≥ 1 then sb else -1
      if b ≤ a then
        L := L - pe; front := 2; off := sa
      else
        L := L - po; front := 0; off := sb
      w := (.gapY, 1) :: w
      t := t + 1
  return w

/-- Runtime-checked result (walk valid, score exact, offsets score identity);
optimality of the corner level is NOT proven.  Falls back to the proven
`wfaAlignK` whenever the check fails. -/
def probeU32Align (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  let m := xa.size
  let n := ya.size
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let margin := max pe (max po px) + 2
  let fast : Option (Array (Step × Nat) × Int) :=
    if wfaGateB sc && m + n + 2 < 2 ^ 30 then
      match uRun m n xa ya pe po px ((m + n + 2) * po + 1) with
      | none => none
      | some (L, hist) =>
        let runs := uTraceRuns m n pe po px margin (pe == po && po == px) hist L
        match checkRuns sc xa ya runs ⟨0,0,none,0⟩ with
        | none => none
        | some s =>
          if 2 * s + (L : Int) == sc.matchScore * ((m : Int) + n) then some (runs.toArray, s)
          else none
    else none
  match fast with
  | some r => some r
  | none => wfaAlignK sc xa ya

end AlignmentSpec
