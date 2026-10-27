import AlignmentWfaU32Fill
import AlignmentWfaU32FillS
import AlignmentWfaU32Loop
import AlignmentWfaRunsFast
import AlignmentWfaU32Lattice

/-!
# The second UInt32 kernel: loop, run, traceback, kernel (definitions)

`uLoop2`/`uRun2` are `uLoop`/`uRun` (AlignmentWfaU32Loop.lean) with the
level builder `uLevel2` (AlignmentWfaU32Fill.lean) and the penalties divided
by their gcd (the level lattice of probe idea 2: with the pa-bench cost
models every odd level of the original run is empty and is never built).
The corner level of the original run is `g` times the returned level.

`uTraceRuns2` is the direct run-length traceback of the probes as a tail
recursion (idea 3); its output is only ever accepted after `checkRunsFast3`
(proven equal to `checkRuns`) accepts it with the certified score.

Proofs: AlignmentWfaU32Kernel2.lean (`uRun2_eq`, `certifiedRunsU2_spec`,
`wfaAlignU2_score/_sound/_isSome`).
-/
namespace AlignmentSpec.U32Proof

def uLoop2 (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size)
    (m n pe po px : Nat) :
    Nat → List ULevel → Nat → Array ULevel → Option (Nat × Array ULevel)
  | 0, _, _, _ => none
  | fuel + 1, hist, p, trace =>
    match uLevel2 len margin m32 n32 len32 xa ya hm hn (frontAtU hist pe) (frontAtU hist po)
        (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px) with
    | none => none
    | some lv =>
      let trace := trace.push lv
      if cornerU margin m n lv then some (p, trace)
      else uLoop2 len margin m32 n32 len32 xa ya hm hn m n pe po px fuel
        ((lv :: hist).take (max pe (max po px))) (p + 1) trace

/-- The run with the (already divided) penalties `pe po px` and explicit fuel. -/
def uRun2 (m n : Nat) (xa ya : Array Char) (m32 n32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (pe po px fuel : Nat) : Option (Nat × Array ULevel) :=
  let len := m + n + 1
  let margin := max pe (max po px) + 2
  let lv := seedU m margin xa ya
  if cornerU margin m n lv then some (0, #[lv])
  else uLoop2 len margin m32 n32 len.toUInt32 xa ya hm hn m n pe po px fuel [lv] 1
    ((Array.emptyWithCapacity 64).push lv)

/-- The single-source run (all divided penalties 1; margin `max 1 (max 1 1) + 2 = 3`). -/
def uRunS (m n : Nat) (xa ya : Array Char) (m32 n32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (fuel : Nat) : Option (Nat × Array ULevel) :=
  let len := m + n + 1
  let lv := seedU m 3 xa ya
  if cornerU 3 m n lv then some (0, #[lv])
  else uLoopS len 3 m32 n32 len.toUInt32 xa ya hm hn m n fuel lv 1
    ((Array.emptyWithCapacity 64).push lv)

/-- Dispatch: the single-source loop when all divided penalties are 1. -/
def uRunD (m n : Nat) (xa ya : Array Char) (m32 n32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (pe po px fuel : Nat) : Option (Nat × Array ULevel) :=
  if pe == 1 && po == 1 && px == 1 then uRunS m n xa ya m32 n32 hm hn fuel
  else uRun2 m n xa ya m32 n32 hm hn pe po px fuel

-- ══════════════════════════════════════════════════════════════════
-- Traceback (not trusted: its output is checked)
-- ══════════════════════════════════════════════════════════════════

@[inline] def ucode2 (a : UInt32) : Int := (a.toNat : Int) - 1

/-- Code of front `sel` of level `L'` at diagonal `t` (`0` = none). -/
@[inline] def tbGet2 (margin : Nat) (hist : Array ULevel) (sel : ULevel → Array UInt32) (L' t : Nat) : UInt32 :=
  uget margin (hist.getD L' uEmpty) sel t

/-- X front of level `L` at diagonal `t`: stored (general path), or the push
of the previous M front (single-source path, where X = pushX(M at t-1)). -/
@[inline] def tbX2 (single : Bool) (m32 n32 : UInt32) (margin : Nat) (hist : Array ULevel) (L t : Nat) : UInt32 :=
  if single then
    (if 1 ≤ L ∧ 1 ≤ t then upushX m32 n32 (t - 1).toUInt32 (tbGet2 margin hist (·.mf) (L - 1) (t - 1)) else 0)
  else tbGet2 margin hist (·.xf) L t

@[inline] def tbY2 (single : Bool) (m32 : UInt32) (margin len : Nat) (hist : Array ULevel) (L t : Nat) : UInt32 :=
  if single then
    (if 1 ≤ L ∧ t + 1 < len then upushY m32 (t + 1).toUInt32 (tbGet2 margin hist (·.mf) (L - 1) (t + 1)) else 0)
  else tbGet2 margin hist (·.yf) L t

/-- The traceback loop: the predecessor rules and tie order of `traceRuns`
(AlignmentTraceRuns.lean), as in ProbeU32/ProbeCombo.  Arguments after
`hist`: fuel, `L`, `t`, front (0 = M, 1 = X, 2 = Y), current offset, reversed
walk so far.  Returns `[]` to request the proven fallback. -/
def uTraceGo2 (single : Bool) (m32 n32 : UInt32) (mI nI : Int) (len : Nat) (pe po px margin : Nat) (hist : Array ULevel) :
    Nat → Nat → Nat → Nat → Int → List (Step × Nat) → List (Step × Nat)
  | 0, _, _, _, _, w => w
  | fuel + 1, L, t, front, off, w =>
    if front == 0 then
      let x := ucode2 (tbX2 single m32 n32 margin hist L t)
      let y := ucode2 (tbY2 single m32 margin len hist L t)
      let s := if px ≤ L then ucode2 (tbGet2 margin hist (·.mf) (L - px) t) else -1
      let j := traceJoff mI t s
      let e : Int := if s < 0 then -1 else if s < mI && j < nI then s + 1
                     else if s ≥ 1 && j ≥ 1 then s else -1
      let b1 := if x ≤ e then e else x
      let b := if L == 0 then (0 : Int) else if y ≤ b1 then b1 else y
      let k := off - b
      let w := if k > 0 then (.diag, k.toNat) :: w else w
      if L == 0 then w
      else if b == e && (x ≤ e) && (y ≤ b1) then
        if s < mI && j < nI then
          uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel (L - px) t 0 s ((.diag, 1) :: w)
        else []
      else if b == b1 then
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel L t 1 x w
      else
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel L t 2 y w
    else if front == 1 then
      let sa := if pe ≤ L && t ≥ 1 then ucode2 (tbX2 single m32 n32 margin hist (L - pe) (t - 1)) else -1
      let sb := if po ≤ L && t ≥ 1 then ucode2 (tbGet2 margin hist (·.mf) (L - po) (t - 1)) else -1
      let ja := traceJoff mI (t - 1 : Nat) sa
      let jb := traceJoff mI (t - 1 : Nat) sb
      let a : Int := if sa < 0 then -1 else if ja < nI then sa else if sa ≥ 1 && ja ≥ 1 then sa - 1 else -1
      let b : Int := if sb < 0 then -1 else if jb < nI then sb else if sb ≥ 1 && jb ≥ 1 then sb - 1 else -1
      let w := (.gapX, 1) :: w
      if b ≤ a then
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel (L - pe) (t - 1) 1 sa w
      else
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel (L - po) (t - 1) 0 sb w
    else
      let sa := if pe ≤ L && t + 1 < len then ucode2 (tbY2 single m32 margin len hist (L - pe) (t + 1)) else -1
      let sb := if po ≤ L && t + 1 < len then ucode2 (tbGet2 margin hist (·.mf) (L - po) (t + 1)) else -1
      let ja := traceJoff mI (t + 1) sa
      let jb := traceJoff mI (t + 1) sb
      let a : Int := if sa < 0 then -1 else if sa < mI then sa + 1 else if sa ≥ 1 && ja ≥ 1 then sa else -1
      let b : Int := if sb < 0 then -1 else if sb < mI then sb + 1 else if sb ≥ 1 && jb ≥ 1 then sb else -1
      let w := (.gapY, 1) :: w
      if b ≤ a then
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel (L - pe) (t + 1) 2 sa w
      else
        uTraceGo2 single m32 n32 mI nI len pe po px margin hist fuel (L - po) (t + 1) 0 sb w

def uTraceRuns2 (single : Bool) (m32 n32 : UInt32) (m n pe po px margin : Nat) (hist : Array ULevel) (L : Nat) :
    List (Step × Nat) :=
  uTraceGo2 single m32 n32 (m : Int) (n : Int) (m + n + 1) pe po px margin hist
    (4 * (m + n) + 8) L n 0 (ucode2 (tbGet2 margin hist (·.mf) L n)) []

-- ══════════════════════════════════════════════════════════════════
-- Kernel
-- ══════════════════════════════════════════════════════════════════

/-- Fast path: divided penalties, `uRun2`, direct traceback, proven fast run
checker, offsets score identity with the original corner level `g * k`. -/
def certifiedRunsU2 (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  let pe0 := (wfaPe sc).toNat
  let po0 := (wfaPo sc).toNat
  let px0 := (wfaPx sc).toNat
  let g := gcdU pe0 (gcdU po0 px0)
  let pe := pe0 / g
  let po := po0 / g
  let px := px0 / g
  if h : wfaGateB sc = true ∧ xa.size + ya.size + 2 < 2 ^ 30 ∧ 1 ≤ po0 then
    match uRunD xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32
        (toNat_toUInt32_of_lt xa.size (by omega)) (toNat_toUInt32_of_lt ya.size (by omega))
        pe po px ((xa.size + ya.size + 2) * po) with
    | none => none
    | some (k, hist) =>
      let L := g * k
      let runs := uTraceRuns2 (pe == 1 && po == 1 && px == 1) xa.size.toUInt32 ya.size.toUInt32
        xa.size ya.size pe po px (max pe (max po px) + 2) hist k
      match checkRunsFast3 sc xa ya runs ⟨0,0,none,0⟩ with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then some (runs.toArray, s)
        else none
  else none

/-- The kernel: exact shortcut, UInt32 fast path, proven fallback. -/
def wfaAlignU2 (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none =>
    match certifiedRunsU2 sc xa ya with
    | some r => some r
    | none => wfaAlignK sc xa ya

end AlignmentSpec.U32Proof

namespace AlignmentSpec
export U32Proof (wfaAlignU2 certifiedRunsU2)
end AlignmentSpec
