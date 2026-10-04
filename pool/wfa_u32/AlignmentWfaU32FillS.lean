import AlignmentWfaU32Fill

/-!
# Single-source level builder (definitions)

The cell loop `uFillS` itself lives in AlignmentWfaU32Fill.lean, next to the
LCP loop it calls (same translation unit, so the C compiler inlines the call:
measured at about 25 % of the general path's time when it could not).

When the three (divided) penalties are all 1, every source of a level is the
previous level, and by the invariant X ≤ M, Y ≤ M on every level
(AlignmentWfaU32Single.lean) the X and Y cells are pushes of the previous
M front alone.  The builder `uLevelS` therefore reads ONE array (the
previous M front) through a sliding window `prev / cur / next` — one `uget`
per cell — and stores only the M front (`xf = yf = #[]`).

Lemmas: AlignmentWfaU32FillSSpec.lean (the values the loop writes),
AlignmentWfaU32LevelS.lean (the built M front denotes `nextLevelR`'s).
-/
namespace AlignmentSpec.U32Proof

/-- The once-per-level check of the single-source builder. -/
def LevelCheckS (margin lo w : Nat) (src : ULevel) : Prop :=
  w < UInt32.size ∧ margin < UInt32.size ∧ w + 2 * margin < 2 ^ 32 ∧ w + margin ≤ w + 2 * margin
    ∧ src.lo + 1 ≤ margin + lo ∧ w + (margin + lo - src.lo + 1) ≤ src.mf.size
    ∧ src.mf.size < 2 ^ 32 ∧ margin + lo - src.lo + 1 < UInt32.size ∧ w + 1 < 2 ^ 32

/-- The runtime form of `LevelCheckS` (short-circuit Bool, scalar bounds). -/
@[inline] def levelCheckSB (margin lo w : Nat) (src : ULevel) : Bool :=
  lt32 w && lt32 margin && lt32 (w + 2 * margin) && w + margin ≤ w + 2 * margin
    && src.lo + 1 ≤ margin + lo && w + (margin + lo - src.lo + 1) ≤ src.mf.size
    && lt32 src.mf.size && lt32 (margin + lo - src.lo + 1) && lt32 (w + 1)

theorem levelCheckSB_true (margin lo w : Nat) (src : ULevel) (h : levelCheckSB margin lo w src = true) :
    LevelCheckS margin lo w src := by
  unfold levelCheckSB at h
  simp only [Bool.and_eq_true, lt32_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The body once the check holds. -/
def uLevelSBody (margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (src : ULevel) (lo w : Nat)
    (h : LevelCheckS margin lo w src) : ULevel :=
  let base := margin + lo - src.lo
  let mf := uFillS xa ya m32 n32 len32 hm hn (UInt32.ofNatLT w h.1)
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.2.2.2.2.2) src.mf
    (UInt32.ofNatLT (base + 1) h.2.2.2.2.2.2.2.1) (UInt32.ofNatLT margin h.2.1) (w + 2 * margin)
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.2.2.1) h.2.2.2.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.1) h.2.2.1
    0 (by simp [UInt32.le_iff_toNat_le]) lo.toUInt32 (src.mf.getD (base - 1) 0) (src.mf.getD base 0)
    (Array.replicate (w + 2 * margin) 0) Array.size_replicate
  ⟨lo, w, mf, #[], #[]⟩

/-- Build the next level from the previous one (all penalties 1): the band is
the source band expanded by one, clipped to `[0, len)`; only the M front is stored. -/
def uLevelS (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (src : ULevel) : Option ULevel :=
  if src.w = 0 then some uEmpty else
  let lo := src.lo - 1
  let hi := min (src.lo + src.w + 1) len
  if hi ≤ lo then some uEmpty else
  let w := hi - lo
  if h : levelCheckSB margin lo w src then
    some (uLevelSBody margin m32 n32 len32 xa ya hm hn src lo w (levelCheckSB_true margin lo w src h))
  else none

/-- Single-source level loop: the previous level is the only source. -/
def uLoopS (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (m n : Nat) :
    Nat → ULevel → Nat → Array ULevel → Option (Nat × Array ULevel)
  | 0, _, _, _ => none
  | fuel + 1, prev, p, trace =>
    match uLevelS len margin m32 n32 len32 xa ya hm hn prev with
    | none => none
    | some lv =>
      let trace := trace.push lv
      if cornerU margin m n lv then some (p, trace)
      else uLoopS len margin m32 n32 len32 xa ya hm hn m n fuel lv (p + 1) trace

end AlignmentSpec.U32Proof
