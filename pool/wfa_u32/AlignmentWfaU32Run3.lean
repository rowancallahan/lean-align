import AlignmentWfaU32Fill3
import AlignmentWfaU32Run2

/-!
# The third UInt32 kernel: general path in the block layout (definitions)

`wfaAlignU3` (codecs/WfaU3.lean) is `wfaAlignU2` with the general (five-source) path replaced by
the block-layout builder `uLevel3` (AlignmentWfaU32Fill3.lean): one array of
three blocks `M | X | Y` per level, one allocation per level, array history.
The single-source path (all divided penalties 1) is unchanged.

The traceback of the general path reads the blocks; as before its output is
only accepted after `checkRunsFast3` accepts it with the certified score.

Proofs: AlignmentWfaU32Level3.lean (block level views to `uLevel`),
AlignmentWfaU32Kernel3.lean (`uRun3_some`, `certifiedRunsU3_spec`,
`wfaAlignU3_score/_sound/_isSome`).
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- Traceback on block levels (not trusted: its output is checked)
-- ══════════════════════════════════════════════════════════════════

/-- Code of block `blk` (0 = M, 1 = X, 2 = Y) of level `L'` at diagonal `t`
(`0` outside the level's band). -/
@[inline] def tbGet3 (margin : Nat) (hist : Array BLevel) (blk L' t : Nat) : UInt32 :=
  let lv := hist.getD L' bEmpty
  if lv.w = 0 then 0 else
    let size := lv.w + 2 * margin
    let idx := t + margin - lv.lo
    if idx < size then lv.blk.getD (blk * size + idx) 0 else 0

def uTraceGo3 (mI nI : Int) (len : Nat) (pe po px margin : Nat) (hist : Array BLevel) :
    Nat → Nat → Nat → Nat → Int → List (Step × Nat) → List (Step × Nat)
  | 0, _, _, _, _, w => w
  | fuel + 1, L, t, front, off, w =>
    if front == 0 then
      let x := ucode2 (tbGet3 margin hist 1 L t)
      let y := ucode2 (tbGet3 margin hist 2 L t)
      let s := if px ≤ L then ucode2 (tbGet3 margin hist 0 (L - px) t) else -1
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
          uTraceGo3 mI nI len pe po px margin hist fuel (L - px) t 0 s ((.diag, 1) :: w)
        else []
      else if b == b1 then
        uTraceGo3 mI nI len pe po px margin hist fuel L t 1 x w
      else
        uTraceGo3 mI nI len pe po px margin hist fuel L t 2 y w
    else if front == 1 then
      let sa := if pe ≤ L && t ≥ 1 then ucode2 (tbGet3 margin hist 1 (L - pe) (t - 1)) else -1
      let sb := if po ≤ L && t ≥ 1 then ucode2 (tbGet3 margin hist 0 (L - po) (t - 1)) else -1
      let ja := traceJoff mI (t - 1 : Nat) sa
      let jb := traceJoff mI (t - 1 : Nat) sb
      let a : Int := if sa < 0 then -1 else if ja < nI then sa else if sa ≥ 1 && ja ≥ 1 then sa - 1 else -1
      let b : Int := if sb < 0 then -1 else if jb < nI then sb else if sb ≥ 1 && jb ≥ 1 then sb - 1 else -1
      let w := (.gapX, 1) :: w
      if b ≤ a then
        uTraceGo3 mI nI len pe po px margin hist fuel (L - pe) (t - 1) 1 sa w
      else
        uTraceGo3 mI nI len pe po px margin hist fuel (L - po) (t - 1) 0 sb w
    else
      let sa := if pe ≤ L && t + 1 < len then ucode2 (tbGet3 margin hist 2 (L - pe) (t + 1)) else -1
      let sb := if po ≤ L && t + 1 < len then ucode2 (tbGet3 margin hist 0 (L - po) (t + 1)) else -1
      let ja := traceJoff mI (t + 1) sa
      let jb := traceJoff mI (t + 1) sb
      let a : Int := if sa < 0 then -1 else if sa < mI then sa + 1 else if sa ≥ 1 && ja ≥ 1 then sa else -1
      let b : Int := if sb < 0 then -1 else if sb < mI then sb + 1 else if sb ≥ 1 && jb ≥ 1 then sb else -1
      let w := (.gapY, 1) :: w
      if b ≤ a then
        uTraceGo3 mI nI len pe po px margin hist fuel (L - pe) (t + 1) 2 sa w
      else
        uTraceGo3 mI nI len pe po px margin hist fuel (L - po) (t + 1) 0 sb w

def uTraceRuns3 (m n pe po px margin : Nat) (hist : Array BLevel) (L : Nat) : List (Step × Nat) :=
  uTraceGo3 (m : Int) (n : Int) (m + n + 1) pe po px margin hist
    (4 * (m + n) + 8) L n 0 (ucode2 (tbGet3 margin hist 0 L n)) []

-- ══════════════════════════════════════════════════════════════════
-- Kernel
-- ══════════════════════════════════════════════════════════════════

/-- Accept a walk from a run: proven fast run checker, offsets score identity
with the original corner level `L`. -/
@[inline] def acceptRuns (sc : Scoring) (xa ya : Array Char) (L : Nat) (runs : List (Step × Nat)) :
    Option (Array (Step × Nat) × Int) :=
  match checkRunsFast3 sc xa ya runs ⟨0,0,none,0⟩ with
  | none => none
  | some s =>
    if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then some (runs.toArray, s)
    else none

/-- Fast path: single-source run when the divided penalties are (1,1,1),
otherwise the block-layout general run. -/
def certifiedRunsU3 (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  let pe0 := (wfaPe sc).toNat
  let po0 := (wfaPo sc).toNat
  let px0 := (wfaPx sc).toNat
  let g := gcdU pe0 (gcdU po0 px0)
  let pe := pe0 / g
  let po := po0 / g
  let px := px0 / g
  if h : wfaGateB sc = true ∧ xa.size + ya.size + 2 < 2 ^ 30 ∧ 1 ≤ po0 then
    let m32 := xa.size.toUInt32
    let n32 := ya.size.toUInt32
    have hm : m32.toNat = xa.size := toNat_toUInt32_of_lt xa.size (by omega)
    have hn : n32.toNat = ya.size := toNat_toUInt32_of_lt ya.size (by omega)
    let fuel := (xa.size + ya.size + 2) * po
    if pe == 1 && po == 1 && px == 1 then
      match uRunS xa.size ya.size xa ya m32 n32 hm hn fuel with
      | none => none
      | some (k, hist) =>
        acceptRuns sc xa ya (g * k) (uTraceRuns2 true m32 n32 xa.size ya.size 1 1 1 3 hist k)
    else
      match uRun3 xa.size ya.size xa ya m32 n32 hm hn pe po px fuel with
      | none => none
      | some (k, hist) =>
        acceptRuns sc xa ya (g * k) (uTraceRuns3 xa.size ya.size pe po px (max pe (max po px) + 2) hist k)
  else none

end AlignmentSpec.U32Proof

namespace AlignmentSpec
export U32Proof (certifiedRunsU3)
end AlignmentSpec
