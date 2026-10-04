import AlignmentWfaU32Fill
import AlignmentWfaU32Loop

/-!
# Block-layout level builder (definitions)

The general (five-source) path of the third kernel, with the level layout of
the combo probe (alignment/probes/ProbeCombo.lean): the three fronts of a
level live in ONE array of three blocks of `size = w + 2·margin` cells,
`M | X | Y`, so a level is one allocation, and the history is one array
indexed by level (no list window).  The cell loop is `uFillGo3`
(AlignmentWfaU32Fill.lean, next to the LCP loop it calls).

Proof strategy (AlignmentWfaU32Level3.lean): the view `toU margin b` cuts
the block array into the three padded fronts of a `ULevel`; a level the block
builder returns views to exactly `uLevel …` of the views of its sources, so
everything proven about `uLevel` (AlignmentWfaU32Step.lean) transfers.
The once-per-level check bounds every read by the END OF ITS BLOCK (a read
past a block would land in the next block silently) and by the array size.
-/
namespace AlignmentSpec.U32Proof

structure BLevel where
  lo  : Nat
  w   : Nat
  blk : Array UInt32
deriving Inhabited

def bEmpty : BLevel := ⟨0, 0, #[]⟩

/-- Block `b` (0 = M, 1 = X, 2 = Y) of a block level as a padded front. -/
def blockOf (margin b : Nat) (s : BLevel) : Array UInt32 :=
  s.blk.extract (b * (s.w + 2 * margin)) ((b + 1) * (s.w + 2 * margin))

/-- The three-array view of a block level. -/
def toU (margin : Nat) (b : BLevel) : ULevel :=
  ⟨b.lo, b.w, blockOf margin 0 b, blockOf margin 1 b, blockOf margin 2 b⟩

-- ── band and sources ──

@[inline] def bandLo3 (s : BLevel) (acc : Nat) : Nat := if 0 < s.w then min acc (s.lo - 1) else acc
@[inline] def bandHi3 (s : BLevel) (acc : Nat) : Nat := if 0 < s.w then max acc (s.lo + s.w + 1) else acc
@[inline] def uBandLo3 (len : Nat) (xe xo ye yo dm : BLevel) : Nat :=
  bandLo3 dm (bandLo3 yo (bandLo3 ye (bandLo3 xo (bandLo3 xe len))))
@[inline] def uBandHi3 (xe xo ye yo dm : BLevel) : Nat :=
  bandHi3 dm (bandHi3 yo (bandHi3 ye (bandHi3 xo (bandHi3 xe 0))))

/-- Source array of a read: an empty source reads the run-wide zero array. -/
@[inline] def srcArr3 (zeros : Array UInt32) (s : BLevel) : Array UInt32 :=
  if s.w = 0 then zeros else s.blk

/-- Base read shift of block `b` of source `s` for a level starting at `lo`:
cell `i` (diagonal `lo + i`) reads diagonal `lo + i` of the block at index
`i + shift`; X reads (diagonal `t - 1`) use `shift - 1`, Y reads (`t + 1`)
use `shift + 1`.  An empty source reads the zero array at shift `margin + 1`. -/
@[inline] def srcSh3 (margin lo b : Nat) (s : BLevel) : Nat :=
  if s.w = 0 then margin + 1 else b * (s.w + 2 * margin) + margin + lo - s.lo

/-- End (exclusive) of the block read from. -/
@[inline] def srcEnd3 (zeros : Array UInt32) (margin b : Nat) (s : BLevel) : Nat :=
  if s.w = 0 then zeros.size else (b + 1) * (s.w + 2 * margin)

/-- Per-source part of the once-per-level check: no truncation of the shift
arithmetic, every read `i + sh` with `i < w` inside the block and the array,
shift below `2^32`. -/
def SrcOK3 (margin lo w : Nat) (zeros : Array UInt32) (s : BLevel) (b : Nat) (sh : Nat) : Prop :=
  (0 < s.w → s.lo + 1 ≤ margin + lo) ∧ w + sh ≤ srcEnd3 zeros margin b s
    ∧ srcEnd3 zeros margin b s ≤ (srcArr3 zeros s).size ∧ (srcArr3 zeros s).size < 2 ^ 32 ∧ sh < UInt32.size

/-- The runtime form of `SrcOK3` (short-circuit Bool, scalar bounds). -/
@[inline] def srcOKB3 (margin lo w : Nat) (zeros : Array UInt32) (s : BLevel) (b : Nat) (sh : Nat) : Bool :=
  (s.w == 0 || s.lo + 1 ≤ margin + lo) && w + sh ≤ srcEnd3 zeros margin b s
    && srcEnd3 zeros margin b s ≤ (srcArr3 zeros s).size && lt32 (srcArr3 zeros s).size && lt32 sh

theorem srcOKB3_true (margin lo w : Nat) (zeros : Array UInt32) (s : BLevel) (b sh : Nat)
    (h : srcOKB3 margin lo w zeros s b sh = true) : SrcOK3 margin lo w zeros s b sh := by
  unfold srcOKB3 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, lt32_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun hw => ?_, h2, h3, h4, h5⟩
  rcases h1 with h1 | h1
  · omega
  · exact h1

/-- The once-per-level check of `uLevel3`: the array and the three write
offsets fit, and every source read is inside its block. -/
def LevelCheck3 (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : BLevel) : Prop :=
  w < UInt32.size ∧ margin < UInt32.size ∧ 3 * (w + 2 * margin) < 2 ^ 32
    ∧ w + margin ≤ 3 * (w + 2 * margin)
    ∧ w + (margin + (w + 2 * margin)) ≤ 3 * (w + 2 * margin)
    ∧ w + (margin + 2 * (w + 2 * margin)) ≤ 3 * (w + 2 * margin)
    ∧ margin + (w + 2 * margin) < UInt32.size ∧ margin + 2 * (w + 2 * margin) < UInt32.size
    ∧ SrcOK3 margin lo w zeros xe 1 (srcSh3 margin lo 1 xe - 1)
    ∧ SrcOK3 margin lo w zeros xo 0 (srcSh3 margin lo 0 xo - 1)
    ∧ SrcOK3 margin lo w zeros ye 2 (srcSh3 margin lo 2 ye + 1)
    ∧ SrcOK3 margin lo w zeros yo 0 (srcSh3 margin lo 0 yo + 1)
    ∧ SrcOK3 margin lo w zeros dm 0 (srcSh3 margin lo 0 dm)

@[inline] def levelCheckB3 (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : BLevel) : Bool :=
  lt32 w && lt32 margin && lt32 (3 * (w + 2 * margin))
    && w + margin ≤ 3 * (w + 2 * margin)
    && w + (margin + (w + 2 * margin)) ≤ 3 * (w + 2 * margin)
    && w + (margin + 2 * (w + 2 * margin)) ≤ 3 * (w + 2 * margin)
    && lt32 (margin + (w + 2 * margin)) && lt32 (margin + 2 * (w + 2 * margin))
    && srcOKB3 margin lo w zeros xe 1 (srcSh3 margin lo 1 xe - 1)
    && srcOKB3 margin lo w zeros xo 0 (srcSh3 margin lo 0 xo - 1)
    && srcOKB3 margin lo w zeros ye 2 (srcSh3 margin lo 2 ye + 1)
    && srcOKB3 margin lo w zeros yo 0 (srcSh3 margin lo 0 yo + 1)
    && srcOKB3 margin lo w zeros dm 0 (srcSh3 margin lo 0 dm)

theorem levelCheckB3_true (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : BLevel)
    (h : levelCheckB3 margin lo w zeros xe xo ye yo dm = true) : LevelCheck3 margin lo w zeros xe xo ye yo dm := by
  unfold levelCheckB3 at h
  simp only [Bool.and_eq_true, lt32_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, srcOKB3_true _ _ _ _ _ _ _ h9, srcOKB3_true _ _ _ _ _ _ _ h10,
    srcOKB3_true _ _ _ _ _ _ _ h11, srcOKB3_true _ _ _ _ _ _ _ h12, srcOKB3_true _ _ _ _ _ _ _ h13⟩

/-- The level body once the check holds: one array of three blocks. -/
def uLevel3Body (margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (zeros : Array UInt32)
    (xe xo ye yo dm : BLevel) (lo w : Nat) (h : LevelCheck3 margin lo w zeros xe xo ye yo dm) : BLevel :=
  have hxe := h.2.2.2.2.2.2.2.2.1
  have hxo := h.2.2.2.2.2.2.2.2.2.1
  have hye := h.2.2.2.2.2.2.2.2.2.2.1
  have hyo := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hdm := h.2.2.2.2.2.2.2.2.2.2.2.2
  let f := uFillGo3 xa ya m32 n32 len32 hm hn (UInt32.ofNatLT w h.1)
    (srcArr3 zeros xe) (srcArr3 zeros xo) (srcArr3 zeros ye) (srcArr3 zeros yo) (srcArr3 zeros dm)
    (UInt32.ofNatLT (srcSh3 margin lo 1 xe - 1) hxe.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 xo - 1) hxo.2.2.2.2)
    (UInt32.ofNatLT (srcSh3 margin lo 2 ye + 1) hye.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 yo + 1) hyo.2.2.2.2)
    (UInt32.ofNatLT (srcSh3 margin lo 0 dm) hdm.2.2.2.2)
    (UInt32.ofNatLT margin h.2.1) (UInt32.ofNatLT (margin + (w + 2 * margin)) h.2.2.2.2.2.2.1)
    (UInt32.ofNatLT (margin + 2 * (w + 2 * margin)) h.2.2.2.2.2.2.2.1) (3 * (w + 2 * margin))
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans hxe.2.1 hxe.2.2.1) hxe.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans hxo.2.1 hxo.2.2.1) hxo.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans hye.2.1 hye.2.2.1) hye.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans hyo.2.1 hyo.2.2.1) hyo.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans hdm.2.1 hdm.2.2.1) hdm.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.1)
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.2.1)
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.2.2.1) h.2.2.1
    0 lo.toUInt32 (Array.replicate (3 * (w + 2 * margin)) 0) Array.size_replicate
  ⟨lo, w, f⟩

/-- Build a level from its five sources; `none` if the once-per-level check
fails (the kernel then falls back).  `zeros` is the run-wide zero array read
by empty sources (size at least `len + 2 * margin + 2`). -/
def uLevel3 (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (zeros : Array UInt32)
    (xe xo ye yo dm : BLevel) : Option BLevel :=
  let lo := uBandLo3 len xe xo ye yo dm
  let hi := min (uBandHi3 xe xo ye yo dm) len
  if hi ≤ lo then some bEmpty else
  let w := hi - lo
  if h : levelCheckB3 margin lo w zeros xe xo ye yo dm then
    some (uLevel3Body margin m32 n32 len32 xa ya hm hn zeros xe xo ye yo dm lo w
      (levelCheckB3_true margin lo w zeros xe xo ye yo dm h))
  else none

/-- Source `d` levels back in the array history (levels `0 … p-1`). -/
@[inline] def srcOf3 (trace : Array BLevel) (p d : Nat) : BLevel :=
  if d ≤ p then trace.getD (p - d) bEmpty else bEmpty

/-- Corner test on the M block: diagonal `n` holds offset `m` (code `m + 1`);
the read is guarded to the block. -/
@[inline] def corner3 (margin m n : Nat) (lv : BLevel) : Bool :=
  lv.w != 0 && (let idx := n + margin - lv.lo
    idx < lv.w + 2 * margin && lv.blk.getD idx 0 == m.toUInt32 + 1)

def uLoop3 (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (m n pe po px : Nat) (zeros : Array UInt32) :
    Nat → Nat → Array BLevel → Option (Nat × Array BLevel)
  | 0, _, _ => none
  | fuel + 1, p, trace =>
    match uLevel3 len margin m32 n32 len32 xa ya hm hn zeros (srcOf3 trace p pe) (srcOf3 trace p po)
        (srcOf3 trace p pe) (srcOf3 trace p po) (srcOf3 trace p px) with
    | none => none
    | some lv =>
      let trace := trace.push lv
      if corner3 margin m n lv then some (p, trace)
      else uLoop3 len margin m32 n32 len32 xa ya hm hn m n pe po px zeros fuel (p + 1) trace

/-- The seed as a block level: the three arrays of `seedU` concatenated
(band `[m, m+1)`, code `lcp + 1` at the M block's cell). -/
def seedB (m margin : Nat) (xa ya : Array Char) : BLevel :=
  let s := seedU m margin xa ya
  ⟨m, 1, s.mf ++ s.xf ++ s.yf⟩

def uRun3 (m n : Nat) (xa ya : Array Char) (m32 n32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (pe po px fuel : Nat) : Option (Nat × Array BLevel) :=
  let len := m + n + 1
  let margin := max pe (max po px) + 2
  let lv := seedB m margin xa ya
  if corner3 margin m n lv then some (0, #[lv])
  else uLoop3 len margin m32 n32 len.toUInt32 xa ya hm hn m n pe po px
    (Array.replicate (len + 2 * margin + 2) 0) fuel 1 ((Array.emptyWithCapacity 64).push lv)

end AlignmentSpec.U32Proof
