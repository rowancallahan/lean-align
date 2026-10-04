import AlignmentWfaU32Level

/-!
# The padded UInt32 level step denotes `nextLevelR`

`uLevel` builds one wavefront level from its five source fronts by a
single recursion over the band (`uFillGo`), storing `UInt32` codes in
arrays padded with `margin` zeros on both sides.  Reads from a source
front need no band test: `ugetA margin lo f t = f.getD (t + margin - lo) 0`
is the code stored on diagonal `t`, or `0` outside the band (`uget_out`).

Denotation: a padded front is read as the `RFront` `toRF` (band start
`lo`, the `w` stored codes), and `rget_toRF` shows `rget` on it equals the
padded read.  The main result `rdenL_toRLevel_uLevel`: on well-formed
sources (`WF`), the level `uLevel` builds denotes exactly the level
`nextLevelR` (AlignmentWfaOffR.lean, proven = the wavefront model) builds
from the same sources, and the new level is well-formed again.
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- The executed level step
-- ══════════════════════════════════════════════════════════════════

def pushZeros : Nat → Array UInt32 → Array UInt32
  | 0, a => a
  | k + 1, a => pushZeros k (a.push 0)

/-- The code stored on diagonal `t` of a padded front whose band starts at
`lo`; `0` outside the band. -/
@[inline] def ugetA (margin lo : Nat) (f : Array UInt32) (t : Nat) : UInt32 :=
  f.getD (t + margin - lo) 0

/-- One cell of the X front (source diagonal `t - 1`). -/
@[inline] def cellX (m32 n32 : UInt32) (margin : Nat) (xeA xoA : Array UInt32) (loXe loXo : Nat)
    (t : Nat) : UInt32 :=
  if t = 0 then 0 else
    ubetter (upushX m32 n32 (t - 1).toUInt32 (ugetA margin loXe xeA (t - 1)))
            (upushX m32 n32 (t - 1).toUInt32 (ugetA margin loXo xoA (t - 1)))

/-- One cell of the Y front (source diagonal `t + 1`). -/
@[inline] def cellY (m32 : UInt32) (len margin : Nat) (yeA yoA : Array UInt32) (loYe loYo : Nat)
    (t : Nat) : UInt32 :=
  if t + 1 < len then
    ubetter (upushY m32 (t + 1).toUInt32 (ugetA margin loYe yeA (t + 1)))
            (upushY m32 (t + 1).toUInt32 (ugetA margin loYo yoA (t + 1)))
  else 0

/-- One cell of the M front from the diagonal source and this level's X, Y cells. -/
@[inline] def cellM (m32 n32 : UInt32) (xa ya : Array Char) (margin : Nat) (dmA : Array UInt32)
    (loDm : Nat) (t : Nat) (x y : UInt32) : UInt32 :=
  uext m32 xa ya t.toUInt32
    (ubetter (ubetter (upushD m32 n32 t.toUInt32 (ugetA margin loDm dmA t)) x) y)

/-- The cell loop: `k` cells from diagonal `t` on, appended to the three
accumulators.  Written as a recursion so the state stays in registers. -/
def uFillGo (xa ya : Array Char) (m32 n32 : UInt32) (len margin : Nat)
    (xeA xoA yeA yoA dmA : Array UInt32) (loXe loXo loYe loYo loDm : Nat) :
    Nat → Nat → Array UInt32 → Array UInt32 → Array UInt32 →
    Array UInt32 × Array UInt32 × Array UInt32
  | 0, _, mf, xf, yf => (mf, xf, yf)
  | k + 1, t, mf, xf, yf =>
    let x := cellX m32 n32 margin xeA xoA loXe loXo t
    let y := cellY m32 len margin yeA yoA loYe loYo t
    let e := cellM m32 n32 xa ya margin dmA loDm t x y
    uFillGo xa ya m32 n32 len margin xeA xoA yeA yoA dmA loXe loXo loYe loYo loDm
      k (t + 1) (mf.push e) (xf.push x) (yf.push y)

/-- Band accumulation: a non-empty source lowers the band start to `s.lo - 1`
and raises the raw end to `s.lo + s.w + 1`. -/
@[inline] def bandLo (s : ULevel) (acc : Nat) : Nat := if 0 < s.w then min acc (s.lo - 1) else acc
@[inline] def bandHi (s : ULevel) (acc : Nat) : Nat := if 0 < s.w then max acc (s.lo + s.w + 1) else acc

/-- Band of the next level: union of the five source bands, expanded by one;
the end is clipped to `len` by the caller. -/
@[inline] def uBandLo (len : Nat) (xe xo ye yo dm : ULevel) : Nat :=
  bandLo dm (bandLo yo (bandLo ye (bandLo xo (bandLo xe len))))
@[inline] def uBandHi (xe xo ye yo dm : ULevel) : Nat :=
  bandHi dm (bandHi yo (bandHi ye (bandHi xo (bandHi xe 0))))

/-- Build a level from its five sources (`xe`/`xo` feed X, `ye`/`yo` feed Y,
`dm` feeds the diagonal). -/
def uLevel (m n len margin : Nat) (xa ya : Array Char) (xe xo ye yo dm : ULevel) : ULevel :=
  let lo := uBandLo len xe xo ye yo dm
  let hi := min (uBandHi xe xo ye yo dm) len
  if hi ≤ lo then uEmpty else
  let w := hi - lo
  let size := w + 2 * margin
  let r := uFillGo xa ya m.toUInt32 n.toUInt32 len margin xe.xf xo.mf ye.yf yo.mf dm.mf
    xe.lo xo.lo ye.lo yo.lo dm.lo w lo
    (pushZeros margin (Array.emptyWithCapacity size)) (pushZeros margin (Array.emptyWithCapacity size))
    (pushZeros margin (Array.emptyWithCapacity size))
  ⟨lo, w, pushZeros margin r.1, pushZeros margin r.2.1, pushZeros margin r.2.2⟩

/-- Source at delta `d` of a most-recent-first history (the `frontAtR` shape). -/
def frontAtU (hist : List ULevel) (d : Nat) : ULevel :=
  match hist[d - 1]? with
  | some lv => lv
  | none => uEmpty

-- ══════════════════════════════════════════════════════════════════
-- Denotation
-- ══════════════════════════════════════════════════════════════════

def uget (margin : Nat) (lv : ULevel) (sel : ULevel → Array UInt32) (t : Nat) : UInt32 :=
  ugetA margin lv.lo (sel lv) t

def toRF (margin : Nat) (lv : ULevel) (sel : ULevel → Array UInt32) : RFront :=
  ⟨lv.lo, ((sel lv).extract margin (margin + lv.w)).map UInt32.toNat⟩

def toRLevel (margin : Nat) (lv : ULevel) : RLevel :=
  ⟨toRF margin lv (·.mf), toRF margin lv (·.xf), toRF margin lv (·.yf)⟩

/-- A well-formed padded front: zero padding on both sides, exact size when
the band is non-empty (an empty band may be any all-zero array), and every
code at most `m + 1`. -/
structure WFA (m margin w : Nat) (f : Array UInt32) : Prop where
  pad : ∀ i (h : i < f.size), (i < margin ∨ margin + w ≤ i) → f[i] = 0
  size : 0 < w → f.size = w + 2 * margin
  bound : ∀ i (h : i < f.size), (f[i]).toNat ≤ m + 1

structure WF (m margin : Nat) (lv : ULevel) : Prop where
  mf : WFA m margin lv.w lv.mf
  xf : WFA m margin lv.w lv.xf
  yf : WFA m margin lv.w lv.yf

theorem wf_uEmpty (m margin : Nat) : WF m margin uEmpty :=
  ⟨⟨fun i h _ => absurd h (by simp [uEmpty]), fun h => absurd h (by simp [uEmpty]),
     fun i h => absurd h (by simp [uEmpty])⟩,
   ⟨fun i h _ => absurd h (by simp [uEmpty]), fun h => absurd h (by simp [uEmpty]),
     fun i h => absurd h (by simp [uEmpty])⟩,
   ⟨fun i h _ => absurd h (by simp [uEmpty]), fun h => absurd h (by simp [uEmpty]),
     fun i h => absurd h (by simp [uEmpty])⟩⟩

theorem ugetA_eq (margin lo : Nat) (f : Array UInt32) (t : Nat) :
    ugetA margin lo f t = (f[t + margin - lo]?).getD 0 := by
  simp [ugetA]

/-- Outside the band a well-formed padded front reads `0`. -/
theorem ugetA_out (m margin lo w : Nat) (f : Array UInt32) (hwf : WFA m margin w f)
    (hm : 1 ≤ margin) (t : Nat) (ht : t < lo ∨ lo + w ≤ t) : ugetA margin lo f t = 0 := by
  rw [ugetA_eq]
  cases hi : f[t + margin - lo]? with
  | none => rfl
  | some v =>
    have hlt : t + margin - lo < f.size := by
      rcases Nat.lt_or_ge (t + margin - lo) f.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hi; cases hi
    have hv : f[t + margin - lo] = v := by
      rw [Array.getElem?_eq_getElem hlt] at hi; cases hi; rfl
    rw [← hv]
    apply hwf.pad _ hlt
    rcases ht with h | h
    · left; omega
    · right; omega

theorem ugetA_bound (m margin lo w : Nat) (f : Array UInt32) (hwf : WFA m margin w f) (t : Nat) :
    (ugetA margin lo f t).toNat ≤ m + 1 := by
  rw [ugetA_eq]
  cases hi : f[t + margin - lo]? with
  | none => simp
  | some v =>
    have hlt : t + margin - lo < f.size := by
      rcases Nat.lt_or_ge (t + margin - lo) f.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hi; cases hi
    have hv : f[t + margin - lo] = v := by
      rw [Array.getElem?_eq_getElem hlt] at hi; cases hi; rfl
    simp only [Option.getD_some]
    rw [← hv]
    exact hwf.bound _ hlt

/-- `rget` on the denoted front is the padded read. -/
theorem rget_toRF (m margin : Nat) (lv : ULevel) (sel : ULevel → Array UInt32)
    (hwf : WFA m margin lv.w (sel lv)) (hm : 1 ≤ margin) (t : Nat) :
    rget (toRF margin lv sel) t = (uget margin lv sel t).toNat := by
  unfold rget toRF uget
  simp only
  by_cases hlo : t < lv.lo
  · rw [if_pos hlo]
    rw [ugetA_out m margin lv.lo lv.w (sel lv) hwf hm t (Or.inl hlo)]
    rfl
  · rw [if_neg hlo, ugetA_eq, Array.getElem?_map, Array.getElem?_extract]
    have hidx : t + margin - lv.lo = margin + (t - lv.lo) := by omega
    rw [hidx]
    by_cases hw : t - lv.lo < min (margin + lv.w) (sel lv).size - margin
    · rw [if_pos hw]
      have hmin := Nat.min_le_right (margin + lv.w) (sel lv).size
      have hlt : margin + (t - lv.lo) < (sel lv).size := by omega
      rw [Array.getElem?_eq_getElem hlt]
      rfl
    · rw [if_neg hw]
      have hout : margin + lv.w ≤ margin + (t - lv.lo) := by
        rcases Nat.eq_zero_or_pos lv.w with h0 | hpos
        · omega
        · have hs := hwf.size hpos
          have hmin : min (margin + lv.w) (sel lv).size = margin + lv.w := Nat.min_eq_left (by omega)
          omega
      simp only [Option.map_none, Option.getD_none]
      cases hi : (sel lv)[margin + (t - lv.lo)]? with
      | none => rfl
      | some v =>
        have hlt : margin + (t - lv.lo) < (sel lv).size := by
          rcases Nat.lt_or_ge (margin + (t - lv.lo)) (sel lv).size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hi; cases hi
        have hv : (sel lv)[margin + (t - lv.lo)] = v := by
          rw [Array.getElem?_eq_getElem hlt] at hi; cases hi; rfl
        simp only [Option.getD_some]
        rw [← hv, hwf.pad _ hlt (Or.inr hout)]
        rfl

/-- The denotation of an empty history slot is the empty banded front. -/
theorem toRF_uEmpty (margin : Nat) (sel : ULevel → Array UInt32) (h : sel uEmpty = #[]) :
    toRF margin uEmpty sel = ⟨0, #[]⟩ := by
  unfold toRF
  rw [h]
  simp [uEmpty]

theorem frontAtR_map_toRLevel (margin : Nat) (hist : List ULevel) (d : Nat)
    (selR : RLevel → RFront) (selU : ULevel → Array UInt32)
    (hsel : ∀ lv, selR (toRLevel margin lv) = toRF margin lv selU) (hE : selU uEmpty = #[]) :
    frontAtR (hist.map (toRLevel margin)) d selR = toRF margin (frontAtU hist d) selU := by
  simp only [frontAtR, frontAtU, List.getElem?_map]
  cases hist[d - 1]? with
  | some lv => simp [hsel]
  | none => simp [toRF_uEmpty margin selU hE]

-- ══════════════════════════════════════════════════════════════════
-- The cell loop appends the cell values
-- ══════════════════════════════════════════════════════════════════

theorem pushZeros_size (k : Nat) (a : Array UInt32) : (pushZeros k a).size = a.size + k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [pushZeros, ih]; omega

theorem pushZeros_getElem? (k : Nat) (a : Array UInt32) (i : Nat) :
    (pushZeros k a)[i]? = if i < a.size then a[i]? else if i < a.size + k then some 0 else none := by
  induction k generalizing a with
  | zero =>
    simp only [pushZeros, Nat.add_zero]
    by_cases h : i < a.size
    · rw [if_pos h]
    · rw [if_neg h, if_neg h, Array.getElem?_eq_none (by omega)]
  | succ k ih =>
    simp only [pushZeros]
    rw [ih, Array.getElem?_push, Array.size_push]
    by_cases h : i < a.size
    · rw [if_pos (by omega), if_neg (by omega), if_pos h]
    · by_cases h2 : i = a.size
      · rw [if_pos (by omega), if_pos h2, if_neg h, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg h, show a.size + 1 + k = a.size + (k + 1) from by omega]

theorem uFillGo_spec (xa ya : Array Char) (m32 n32 : UInt32) (len margin : Nat)
    (xeA xoA yeA yoA dmA : Array UInt32) (loXe loXo loYe loYo loDm : Nat) :
    ∀ (k t : Nat) (mf xf yf : Array UInt32),
      let r := uFillGo xa ya m32 n32 len margin xeA xoA yeA yoA dmA loXe loXo loYe loYo loDm k t mf xf yf
      r.1.size = mf.size + k ∧ r.2.1.size = xf.size + k ∧ r.2.2.size = yf.size + k ∧
      (∀ i, r.2.1[i]? = if i < xf.size then xf[i]? else if i < xf.size + k then
          some (cellX m32 n32 margin xeA xoA loXe loXo (t + (i - xf.size))) else none) ∧
      (∀ i, r.2.2[i]? = if i < yf.size then yf[i]? else if i < yf.size + k then
          some (cellY m32 len margin yeA yoA loYe loYo (t + (i - yf.size))) else none) ∧
      (∀ i, r.1[i]? = if i < mf.size then mf[i]? else if i < mf.size + k then
          some (cellM m32 n32 xa ya margin dmA loDm (t + (i - mf.size))
            (cellX m32 n32 margin xeA xoA loXe loXo (t + (i - mf.size)))
            (cellY m32 len margin yeA yoA loYe loYo (t + (i - mf.size)))) else none) := by
  intro k
  induction k with
  | zero =>
    intro t mf xf yf
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro i
      simp only [uFillGo, Nat.add_zero]
      by_cases h : i < xf.size
      · rw [if_pos h]
      · rw [if_neg h, if_neg h, Array.getElem?_eq_none (by omega)]
    · intro i
      simp only [uFillGo, Nat.add_zero]
      by_cases h : i < yf.size
      · rw [if_pos h]
      · rw [if_neg h, if_neg h, Array.getElem?_eq_none (by omega)]
    · intro i
      simp only [uFillGo, Nat.add_zero]
      by_cases h : i < mf.size
      · rw [if_pos h]
      · rw [if_neg h, if_neg h, Array.getElem?_eq_none (by omega)]
  | succ k ih =>
    intro t mf xf yf
    simp only [uFillGo]
    obtain ⟨h1, h2, h3, hx, hy, hm⟩ := ih (t + 1) (mf.push _) (xf.push _) (yf.push _)
    refine ⟨by rw [h1, Array.size_push]; omega, by rw [h2, Array.size_push]; omega,
      by rw [h3, Array.size_push]; omega, ?_, ?_, ?_⟩
    · intro i
      rw [hx i, Array.getElem?_push, Array.size_push]
      by_cases h : i < xf.size
      · rw [if_pos (by omega), if_neg (by omega), if_pos h]
      · by_cases h2 : i = xf.size
        · rw [if_pos (by omega), if_pos h2, if_neg h, if_pos (by omega), h2, Nat.sub_self, Nat.add_zero]
        · rw [if_neg (by omega), if_neg h]
          by_cases h3 : i < xf.size + (k + 1)
          · rw [if_pos (by omega), if_pos h3]
            congr 2; omega
          · rw [if_neg (by omega), if_neg h3]
    · intro i
      rw [hy i, Array.getElem?_push, Array.size_push]
      by_cases h : i < yf.size
      · rw [if_pos (by omega), if_neg (by omega), if_pos h]
      · by_cases h2 : i = yf.size
        · rw [if_pos (by omega), if_pos h2, if_neg h, if_pos (by omega), h2, Nat.sub_self, Nat.add_zero]
        · rw [if_neg (by omega), if_neg h]
          by_cases h3 : i < yf.size + (k + 1)
          · rw [if_pos (by omega), if_pos h3]
            congr 2; omega
          · rw [if_neg (by omega), if_neg h3]
    · intro i
      rw [hm i, Array.getElem?_push, Array.size_push]
      by_cases h : i < mf.size
      · rw [if_pos (by omega), if_neg (by omega), if_pos h]
      · by_cases h2 : i = mf.size
        · rw [if_pos (by omega), if_pos h2, if_neg h, if_pos (by omega), h2, Nat.sub_self, Nat.add_zero]
        · rw [if_neg (by omega), if_neg h]
          by_cases h3 : i < mf.size + (k + 1)
          · rw [if_pos (by omega), if_pos h3]
            have e : t + 1 + (i - (mf.size + 1)) = t + (i - mf.size) := by omega
            rw [e]
          · rw [if_neg (by omega), if_neg h3]


-- ══════════════════════════════════════════════════════════════════
-- Band facts
-- ══════════════════════════════════════════════════════════════════

theorem bandLo_le (s : ULevel) (acc : Nat) : bandLo s acc ≤ acc := by
  unfold bandLo; split <;> omega
theorem bandLo_le_src (s : ULevel) (acc : Nat) (h : 0 < s.w) : bandLo s acc ≤ s.lo - 1 := by
  unfold bandLo; rw [if_pos h]; omega
theorem bandHi_ge (s : ULevel) (acc : Nat) : acc ≤ bandHi s acc := by
  unfold bandHi; split <;> omega
theorem bandHi_ge_src (s : ULevel) (acc : Nat) (h : 0 < s.w) : s.lo + s.w + 1 ≤ bandHi s acc := by
  unfold bandHi; rw [if_pos h]; omega

/-- The band contains every non-empty source band, expanded by one. -/
def SrcBand (lo hiRaw : Nat) (s : ULevel) : Prop :=
  0 < s.w → lo ≤ s.lo - 1 ∧ s.lo + s.w + 1 ≤ hiRaw

theorem uBand_src (len : Nat) (xe xo ye yo dm : ULevel) :
    SrcBand (uBandLo len xe xo ye yo dm) (uBandHi xe xo ye yo dm) xe ∧
    SrcBand (uBandLo len xe xo ye yo dm) (uBandHi xe xo ye yo dm) xo ∧
    SrcBand (uBandLo len xe xo ye yo dm) (uBandHi xe xo ye yo dm) ye ∧
    SrcBand (uBandLo len xe xo ye yo dm) (uBandHi xe xo ye yo dm) yo ∧
    SrcBand (uBandLo len xe xo ye yo dm) (uBandHi xe xo ye yo dm) dm := by
  unfold uBandLo uBandHi SrcBand
  have l1 := bandLo_le dm (bandLo yo (bandLo ye (bandLo xo (bandLo xe len))))
  have l2 := bandLo_le yo (bandLo ye (bandLo xo (bandLo xe len)))
  have l3 := bandLo_le ye (bandLo xo (bandLo xe len))
  have l4 := bandLo_le xo (bandLo xe len)
  have h1 := bandHi_ge dm (bandHi yo (bandHi ye (bandHi xo (bandHi xe 0))))
  have h2 := bandHi_ge yo (bandHi ye (bandHi xo (bandHi xe 0)))
  have h3 := bandHi_ge ye (bandHi xo (bandHi xe 0))
  have h4 := bandHi_ge xo (bandHi xe 0)
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · have := bandLo_le_src xe len h; omega
  · have := bandHi_ge_src xe 0 h; omega
  · have := bandLo_le_src xo (bandLo xe len) h; omega
  · have := bandHi_ge_src xo (bandHi xe 0) h; omega
  · have := bandLo_le_src ye (bandLo xo (bandLo xe len)) h; omega
  · have := bandHi_ge_src ye (bandHi xo (bandHi xe 0)) h; omega
  · have := bandLo_le_src yo (bandLo ye (bandLo xo (bandLo xe len))) h; omega
  · have := bandHi_ge_src yo (bandHi ye (bandHi xo (bandHi xe 0))) h; omega
  · have := bandLo_le_src dm (bandLo yo (bandLo ye (bandLo xo (bandLo xe len)))) h; omega
  · have := bandHi_ge_src dm (bandHi yo (bandHi ye (bandHi xo (bandHi xe 0)))) h; omega

/-- A diagonal outside the new band reads `0` on every source, at `t - 1`,
`t` and `t + 1`. -/
theorem src_out (s : ULevel) (lo hiRaw t t' : Nat) (hs : SrcBand lo hiRaw s)
    (ht : t < lo ∨ hiRaw ≤ t) (h1 : t ≤ t' + 1) (h2 : t' ≤ t + 1) :
    t' < s.lo ∨ s.lo + s.w ≤ t' := by
  rcases Nat.eq_zero_or_pos s.w with h0 | hpos
  · omega
  · have := hs hpos; omega

-- ══════════════════════════════════════════════════════════════════
-- Nat-level bounds on codes (every stored code is at most m + 1)
-- ══════════════════════════════════════════════════════════════════

theorem pushXR_le (m n t a : Nat) (h : a ≤ m + 1) : pushXR m n t a ≤ m + 1 := by
  unfold pushXR
  split
  · omega
  · dsimp only
    split
    · omega
    · split <;> omega

theorem pushYR_le (m n t a : Nat) (h : a ≤ m + 1) : pushYR m n t a ≤ m + 1 := by
  unfold pushYR
  split
  · omega
  · dsimp only
    split
    · omega
    · split <;> omega

theorem pushDR_le (m n t a : Nat) (h : a ≤ m + 1) : pushDR m n t a ≤ m + 1 := by
  unfold pushDR
  split
  · omega
  · dsimp only
    split
    · omega
    · split <;> omega

theorem betterR_le (m a b : Nat) (ha : a ≤ m + 1) (hb : b ≤ m + 1) : betterR a b ≤ m + 1 := by
  unfold betterR; split <;> omega

theorem lcpArr_le_sub (xa ya : Array Char) (i j : Nat) : lcpArr xa ya i j ≤ xa.size - i := by
  have h := lcpArrGo_le_fuel xa ya (xa.size - i) i j 0
  unfold lcpArr; omega

theorem extR_le (m : Nat) (xa ya : Array Char) (hxa : xa.size = m) (t a : Nat) (h : a ≤ m + 1) :
    extR m xa ya t a ≤ m + 1 := by
  unfold extR
  split
  · omega
  · dsimp only
    have := lcpArr_le_sub xa ya (a - 1) (joffOf m t (a - 1))
    omega

-- ══════════════════════════════════════════════════════════════════
-- Cells denote the pointwise recurrence of AlignmentWfaPoint.lean
-- ══════════════════════════════════════════════════════════════════

theorem toNat_toUInt32_of_lt (k : Nat) (h : k < 2 ^ 30) : k.toUInt32.toNat = k :=
  UInt32.toNat_ofNat_of_lt' (by change k < 4294967296; omega)

theorem cellX_toNat (m n margin : Nat) (xe xo : ULevel)
    (hxe : WFA m margin xe.w xe.xf) (hxo : WFA m margin xo.w xo.mf) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (t : Nat) (ht : t < 2 ^ 30) :
    (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t).toNat =
      pointX m n (toRF margin xe (·.xf)) (toRF margin xo (·.mf)) t := by
  unfold cellX pointX
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    have hmN := toNat_toUInt32_of_lt m (by omega)
    have hnN := toNat_toUInt32_of_lt n (by omega)
    have htN := toNat_toUInt32_of_lt (t - 1) (by omega)
    have bxe := ugetA_bound m margin xe.lo xe.w xe.xf hxe (t - 1)
    have bxo := ugetA_bound m margin xo.lo xo.w xo.mf hxo (t - 1)
    rw [ubetter_toNat, upushX_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩,
      upushX_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩, hmN, hnN, htN,
      rget_toRF m margin xe (·.xf) hxe hm, rget_toRF m margin xo (·.mf) hxo hm]
    rfl

theorem cellY_toNat (m n len margin : Nat) (ye yo : ULevel)
    (hye : WFA m margin ye.w ye.yf) (hyo : WFA m margin yo.w yo.mf) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (t : Nat) :
    (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t).toNat =
      pointY m n len (toRF margin ye (·.yf)) (toRF margin yo (·.mf)) t := by
  unfold cellY pointY
  by_cases h0 : t + 1 < len
  · rw [if_pos h0, if_pos h0]
    have hmN := toNat_toUInt32_of_lt m (by omega)
    have htN := toNat_toUInt32_of_lt (t + 1) (by omega)
    have bye := ugetA_bound m margin ye.lo ye.w ye.yf hye (t + 1)
    have byo := ugetA_bound m margin yo.lo yo.w yo.mf hyo (t + 1)
    rw [ubetter_toNat, upushY_toNat _ n.toUInt32 _ _ ⟨by omega, by rw [toNat_toUInt32_of_lt n (by omega)]; omega, by omega, by omega⟩,
      upushY_toNat _ n.toUInt32 _ _ ⟨by omega, by rw [toNat_toUInt32_of_lt n (by omega)]; omega, by omega, by omega⟩,
      hmN, htN, toNat_toUInt32_of_lt n (by omega),
      rget_toRF m margin ye (·.yf) hye hm, rget_toRF m margin yo (·.mf) hyo hm]
    rfl
  · rw [if_neg h0, if_neg h0]; rfl

theorem cellM_toNat (m n margin : Nat) (xa ya : Array Char) (dm : ULevel)
    (hdm : WFA m margin dm.w dm.mf) (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30)
    (hxa : xa.size = m) (t : Nat) (ht : t < 2 ^ 30) (x y : UInt32)
    (hx : x.toNat ≤ m + 1) (hy : y.toNat ≤ m + 1) :
    (cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo t x y).toNat =
      extR m xa ya t (betterR (betterR (pushDR m n t (rget (toRF margin dm (·.mf)) t)) x.toNat) y.toNat) := by
  unfold cellM
  have hmN := toNat_toUInt32_of_lt m (by omega)
  have hnN := toNat_toUInt32_of_lt n (by omega)
  have htN := toNat_toUInt32_of_lt t ht
  have bdm := ugetA_bound m margin dm.lo dm.w dm.mf hdm t
  have hd : (upushD m.toUInt32 n.toUInt32 t.toUInt32 (ugetA margin dm.lo dm.mf t)).toNat =
      pushDR m n t (rget (toRF margin dm (·.mf)) t) := by
    rw [upushD_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩, hmN, hnN, htN,
      rget_toRF m margin dm (·.mf) hdm hm]
    rfl
  have hdl : (upushD m.toUInt32 n.toUInt32 t.toUInt32 (ugetA margin dm.lo dm.mf t)).toNat ≤ m + 1 := by
    rw [hd]; exact pushDR_le m n t _ (by rw [rget_toRF m margin dm (·.mf) hdm hm]; exact bdm)
  have hb1 : (ubetter (upushD m.toUInt32 n.toUInt32 t.toUInt32 (ugetA margin dm.lo dm.mf t)) x).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hdl hx
  have hb2 : (ubetter (ubetter (upushD m.toUInt32 n.toUInt32 t.toUInt32 (ugetA margin dm.lo dm.mf t)) x) y).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hb1 hy
  rw [uext_toNat _ n.toUInt32 _ _ xa ya ⟨by omega, by omega, by omega, by omega⟩ (by omega),
    hmN, htN, ubetter_toNat, ubetter_toNat, hd]


-- ══════════════════════════════════════════════════════════════════
-- Padded fronts built by the fill loop
-- ══════════════════════════════════════════════════════════════════

/-- Reading a diagonal of `pushZeros margin arr` where `arr` holds `margin`
zeros followed by the `w` cell values. -/
theorem ugetA_padded (margin lo w : Nat) (arr : Array UInt32) (g : Nat → UInt32)
    (hsz : arr.size = margin + w)
    (harr : ∀ i, arr[i]? = if i < margin then some 0
      else if i < margin + w then some (g (lo + (i - margin))) else none)
    (hm : 1 ≤ margin) (t : Nat) :
    ugetA margin lo (pushZeros margin arr) t = if lo ≤ t ∧ t < lo + w then g t else 0 := by
  rw [ugetA_eq, pushZeros_getElem?, hsz]
  by_cases hin : lo ≤ t ∧ t < lo + w
  · rw [if_pos hin, if_pos (by omega), harr, if_neg (by omega), if_pos (by omega)]
    have e : lo + (t + margin - lo - margin) = t := by omega
    rw [e]; rfl
  · rw [if_neg hin]
    by_cases h1 : t + margin - lo < margin + w
    · rw [if_pos h1, harr, if_pos (by omega)]; rfl
    · rw [if_neg h1]
      by_cases h2 : t + margin - lo < margin + w + margin
      · rw [if_pos h2]; rfl
      · rw [if_neg h2]; rfl

/-- The array holding `margin` zeros then `w` values `g (lo + i)` that the
fill loop produces from `pushZeros margin (Array.emptyWithCapacity size)`. -/
theorem fill_prefix_spec (margin w lo : Nat) (arr : Array UInt32) (g : Nat → UInt32) (size : Nat)
    (hsz : arr.size = (pushZeros margin (Array.emptyWithCapacity size)).size + w)
    (harr : ∀ i, arr[i]? = if i < (pushZeros margin (Array.emptyWithCapacity size)).size then
        (pushZeros margin (Array.emptyWithCapacity size))[i]?
      else if i < (pushZeros margin (Array.emptyWithCapacity size)).size + w then
        some (g (lo + (i - (pushZeros margin (Array.emptyWithCapacity size)).size))) else none) :
    arr.size = margin + w ∧
    ∀ i, arr[i]? = if i < margin then some 0
      else if i < margin + w then some (g (lo + (i - margin))) else none := by
  have h0 : (Array.emptyWithCapacity size : Array UInt32).size = 0 := rfl
  have hs : (pushZeros margin (Array.emptyWithCapacity size : Array UInt32)).size = margin := by
    rw [pushZeros_size, h0, Nat.zero_add]
  refine ⟨by rw [hsz, hs], ?_⟩
  intro i
  rw [harr, hs]
  by_cases h : i < margin
  · rw [if_pos h, if_pos h, pushZeros_getElem?, h0, Nat.zero_add]
    rw [if_neg (by omega), if_pos h]
  · rw [if_neg h, if_neg h]

/-- `WFA` for a padded front built from cell values bounded by `m + 1`. -/
theorem wfa_padded (m margin lo w : Nat) (arr : Array UInt32) (g : Nat → UInt32)
    (hsz : arr.size = margin + w)
    (harr : ∀ i, arr[i]? = if i < margin then some 0
      else if i < margin + w then some (g (lo + (i - margin))) else none)
    (hg : ∀ t, lo ≤ t → t < lo + w → (g t).toNat ≤ m + 1) :
    WFA m margin w (pushZeros margin arr) := by
  have hsize : (pushZeros margin arr).size = w + 2 * margin := by
    rw [pushZeros_size, hsz]; omega
  refine ⟨?_, fun _ => hsize, ?_⟩
  · intro i hi hout
    have hq : (pushZeros margin arr)[i]? = some 0 := by
      rw [pushZeros_getElem?, hsz]
      by_cases h1 : i < margin + w
      · rw [if_pos h1, harr]
        rcases hout with h | h
        · rw [if_pos h]
        · omega
      · rw [if_neg h1, if_pos (by omega)]
    have h2 := Array.getElem?_eq_getElem hi
    rw [hq] at h2
    exact (Option.some.inj h2).symm
  · intro i hi
    have hq : (pushZeros margin arr)[i]? = some ((pushZeros margin arr)[i]) :=
      Array.getElem?_eq_getElem hi
    rw [pushZeros_getElem?, hsz] at hq
    by_cases h1 : i < margin + w
    · rw [if_pos h1, harr] at hq
      by_cases h2 : i < margin
      · rw [if_pos h2] at hq; rw [← Option.some.inj hq]; simp
      · rw [if_neg h2, if_pos h1] at hq
        rw [← Option.some.inj hq]
        exact hg _ (by omega) (by omega)
    · rw [if_neg h1, if_pos (by omega)] at hq
      rw [← Option.some.inj hq]; simp


-- ══════════════════════════════════════════════════════════════════
-- The pointwise recurrence reads 0 outside the new band
-- ══════════════════════════════════════════════════════════════════

theorem pointX_zero (m n margin lo hiRaw : Nat) (xe xo : ULevel)
    (hxe : WFA m margin xe.w xe.xf) (hxo : WFA m margin xo.w xo.mf) (hm : 1 ≤ margin)
    (sxe : SrcBand lo hiRaw xe) (sxo : SrcBand lo hiRaw xo) (t : Nat) (ht : t < lo ∨ hiRaw ≤ t) :
    pointX m n (toRF margin xe (·.xf)) (toRF margin xo (·.mf)) t = 0 := by
  unfold pointX
  by_cases h0 : t = 0
  · rw [if_pos h0]
  · rw [if_neg h0, rget_toRF m margin xe _ hxe hm, rget_toRF m margin xo _ hxo hm]
    unfold uget
    rw [ugetA_out m margin xe.lo xe.w xe.xf hxe hm (t - 1)
          (src_out xe lo hiRaw t (t - 1) sxe ht (by omega) (by omega)),
        ugetA_out m margin xo.lo xo.w xo.mf hxo hm (t - 1)
          (src_out xo lo hiRaw t (t - 1) sxo ht (by omega) (by omega))]
    rfl

theorem pointY_zero (m n len margin lo hiRaw : Nat) (ye yo : ULevel)
    (hye : WFA m margin ye.w ye.yf) (hyo : WFA m margin yo.w yo.mf) (hm : 1 ≤ margin)
    (sye : SrcBand lo hiRaw ye) (syo : SrcBand lo hiRaw yo) (t : Nat) (ht : t < lo ∨ hiRaw ≤ t) :
    pointY m n len (toRF margin ye (·.yf)) (toRF margin yo (·.mf)) t = 0 := by
  unfold pointY
  by_cases h0 : t + 1 < len
  · rw [if_pos h0, rget_toRF m margin ye _ hye hm, rget_toRF m margin yo _ hyo hm]
    unfold uget
    rw [ugetA_out m margin ye.lo ye.w ye.yf hye hm (t + 1)
          (src_out ye lo hiRaw t (t + 1) sye ht (by omega) (by omega)),
        ugetA_out m margin yo.lo yo.w yo.mf hyo hm (t + 1)
          (src_out yo lo hiRaw t (t + 1) syo ht (by omega) (by omega))]
    rfl
  · rw [if_neg h0]

theorem pointM_zero (m n : Nat) (xa ya : Array Char) (dm xf yf : RFront) (t : Nat)
    (h1 : rget dm t = 0) (h2 : rget xf t = 0) (h3 : rget yf t = 0) :
    pointM m n xa ya dm xf yf t = 0 := by
  unfold pointM
  rw [h1, h2, h3]
  rfl

-- ── code bounds of the pointwise values ──

theorem pointX_le (m n margin : Nat) (xe xo : ULevel)
    (hxe : WFA m margin xe.w xe.xf) (hxo : WFA m margin xo.w xo.mf) (hm : 1 ≤ margin) (t : Nat) :
    pointX m n (toRF margin xe (·.xf)) (toRF margin xo (·.mf)) t ≤ m + 1 := by
  unfold pointX
  split
  · omega
  · apply betterR_le
    · apply pushXR_le
      rw [rget_toRF m margin xe _ hxe hm]; exact ugetA_bound m margin _ _ _ hxe _
    · apply pushXR_le
      rw [rget_toRF m margin xo _ hxo hm]; exact ugetA_bound m margin _ _ _ hxo _

theorem pointY_le (m n len margin : Nat) (ye yo : ULevel)
    (hye : WFA m margin ye.w ye.yf) (hyo : WFA m margin yo.w yo.mf) (hm : 1 ≤ margin) (t : Nat) :
    pointY m n len (toRF margin ye (·.yf)) (toRF margin yo (·.mf)) t ≤ m + 1 := by
  unfold pointY
  split
  · apply betterR_le
    · apply pushYR_le
      rw [rget_toRF m margin ye _ hye hm]; exact ugetA_bound m margin _ _ _ hye _
    · apply pushYR_le
      rw [rget_toRF m margin yo _ hyo hm]; exact ugetA_bound m margin _ _ _ hyo _
  · omega

-- ══════════════════════════════════════════════════════════════════
-- Structure of the built level
-- ══════════════════════════════════════════════════════════════════

/-- In the non-empty case the three fronts of `uLevel` are padded fill arrays. -/
theorem uLevel_fronts (m n len margin : Nat) (xa ya : Array Char) (xe xo ye yo dm : ULevel)
    (hne : ¬ min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm) :
    let lo := uBandLo len xe xo ye yo dm
    let w := min (uBandHi xe xo ye yo dm) len - lo
    let lv := uLevel m n len margin xa ya xe xo ye yo dm
    lv.lo = lo ∧ lv.w = w ∧
    ∃ arrX arrY arrM : Array UInt32,
      lv.xf = pushZeros margin arrX ∧ lv.yf = pushZeros margin arrY ∧ lv.mf = pushZeros margin arrM ∧
      arrX.size = margin + w ∧ arrY.size = margin + w ∧ arrM.size = margin + w ∧
      (∀ i, arrX[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (i - margin))) else none) ∧
      (∀ i, arrY[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (i - margin))) else none) ∧
      (∀ i, arrM[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo (lo + (i - margin))
          (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (i - margin)))
          (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (i - margin)))) else none) := by
  intro lo w lv
  have hlv : lv = ⟨lo, w, pushZeros margin (uFillGo xa ya m.toUInt32 n.toUInt32 len margin xe.xf xo.mf ye.yf yo.mf dm.mf
      xe.lo xo.lo ye.lo yo.lo dm.lo w lo (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))
      (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin))) (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))).1,
      pushZeros margin (uFillGo xa ya m.toUInt32 n.toUInt32 len margin xe.xf xo.mf ye.yf yo.mf dm.mf
      xe.lo xo.lo ye.lo yo.lo dm.lo w lo (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))
      (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin))) (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))).2.1,
      pushZeros margin (uFillGo xa ya m.toUInt32 n.toUInt32 len margin xe.xf xo.mf ye.yf yo.mf dm.mf
      xe.lo xo.lo ye.lo yo.lo dm.lo w lo (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))
      (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin))) (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))).2.2⟩ := by
    show uLevel m n len margin xa ya xe xo ye yo dm = _
    unfold uLevel
    simp only
    rw [if_neg hne]
  have hspec := uFillGo_spec xa ya m.toUInt32 n.toUInt32 len margin xe.xf xo.mf ye.yf yo.mf dm.mf
      xe.lo xo.lo ye.lo yo.lo dm.lo w lo (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))
      (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin))) (pushZeros margin (Array.emptyWithCapacity (w + 2 * margin)))
  simp only at hspec
  obtain ⟨h1, h2, h3, hx, hy, hmf⟩ := hspec
  obtain ⟨sx, gx⟩ := fill_prefix_spec margin w lo _ (fun t => cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t)
    (w + 2 * margin) h2 hx
  obtain ⟨sy, gy⟩ := fill_prefix_spec margin w lo _ (fun t => cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t)
    (w + 2 * margin) h3 hy
  obtain ⟨sm, gm⟩ := fill_prefix_spec margin w lo _ (fun t => cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo t
      (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t)
      (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t)) (w + 2 * margin) h1 hmf
  rw [hlv]
  exact ⟨rfl, rfl, _, _, _, rfl, rfl, rfl, sx, sy, sm, gx, gy, gm⟩


theorem uLevel_empty (m n len margin : Nat) (xa ya : Array Char) (xe xo ye yo dm : ULevel)
    (he : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm) :
    uLevel m n len margin xa ya xe xo ye yo dm = uEmpty := by
  unfold uLevel
  simp only
  rw [if_pos he]

theorem uget_uEmpty (margin : Nat) (sel : ULevel → Array UInt32) (h : sel uEmpty = #[]) (t : Nat) :
    uget margin uEmpty sel t = 0 := by
  unfold uget ugetA
  rw [h]
  simp

-- ══════════════════════════════════════════════════════════════════
-- Well-formedness of the built level and its pointwise reads
-- ══════════════════════════════════════════════════════════════════

section Level
variable (m n len margin : Nat) (xa ya : Array Char) (xe xo ye yo dm : ULevel)

theorem uget_uLevel_xf (wxe : WF m margin xe) (wxo : WF m margin xo) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (t : Nat) (ht : t < len) :
    (uget margin (uLevel m n len margin xa ya xe xo ye yo dm) (·.xf) t).toNat =
      pointX m n (toRF margin xe (·.xf)) (toRF margin xo (·.mf)) t := by
  obtain ⟨sxe, sxo, _, _, _⟩ := uBand_src len xe xo ye yo dm
  by_cases he : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm
  · rw [uLevel_empty m n len margin xa ya xe xo ye yo dm he, uget_uEmpty margin _ rfl,
      pointX_zero m n margin _ _ xe xo wxe.xf wxo.mf hm sxe sxo t (by omega)]
    rfl
  · have hf := uLevel_fronts m n len margin xa ya xe xo ye yo dm he
    simp only at hf
    obtain ⟨hlo, hw, arrX, arrY, arrM, hX, hY, hM, sX, sY, sM, gX, gY, gM⟩ := hf
    simp only [uget]
    rw [hlo, hX, ugetA_padded margin _ _ arrX (fun t => cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t) sX gX hm]
    by_cases hin : uBandLo len xe xo ye yo dm ≤ t ∧ t < uBandLo len xe xo ye yo dm + (min (uBandHi xe xo ye yo dm) len - uBandLo len xe xo ye yo dm)
    · rw [if_pos hin]
      exact cellX_toNat m n margin xe xo wxe.xf wxo.mf hm hb t (by omega)
    · rw [if_neg hin, pointX_zero m n margin _ _ xe xo wxe.xf wxo.mf hm sxe sxo t (by omega)]
      rfl

theorem uget_uLevel_yf (wye : WF m margin ye) (wyo : WF m margin yo) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (t : Nat) (ht : t < len) :
    (uget margin (uLevel m n len margin xa ya xe xo ye yo dm) (·.yf) t).toNat =
      pointY m n len (toRF margin ye (·.yf)) (toRF margin yo (·.mf)) t := by
  obtain ⟨_, _, sye, syo, _⟩ := uBand_src len xe xo ye yo dm
  by_cases he : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm
  · rw [uLevel_empty m n len margin xa ya xe xo ye yo dm he, uget_uEmpty margin _ rfl,
      pointY_zero m n len margin _ _ ye yo wye.yf wyo.mf hm sye syo t (by omega)]
    rfl
  · have hf := uLevel_fronts m n len margin xa ya xe xo ye yo dm he
    simp only at hf
    obtain ⟨hlo, hw, arrX, arrY, arrM, hX, hY, hM, sX, sY, sM, gX, gY, gM⟩ := hf
    simp only [uget]
    rw [hlo, hY, ugetA_padded margin _ _ arrY (fun t => cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t) sY gY hm]
    by_cases hin : uBandLo len xe xo ye yo dm ≤ t ∧ t < uBandLo len xe xo ye yo dm + (min (uBandHi xe xo ye yo dm) len - uBandLo len xe xo ye yo dm)
    · rw [if_pos hin]
      exact cellY_toNat m n len margin ye yo wye.yf wyo.mf hm hb hlen t
    · rw [if_neg hin, pointY_zero m n len margin _ _ ye yo wye.yf wyo.mf hm sye syo t (by omega)]
      rfl

theorem wf_uLevel (wxe : WF m margin xe) (wxo : WF m margin xo) (wye : WF m margin ye)
    (wyo : WF m margin yo) (wdm : WF m margin dm) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m) :
    WF m margin (uLevel m n len margin xa ya xe xo ye yo dm) := by
  by_cases he : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm
  · rw [uLevel_empty m n len margin xa ya xe xo ye yo dm he]; exact wf_uEmpty m margin
  · have hf := uLevel_fronts m n len margin xa ya xe xo ye yo dm he
    simp only at hf
    obtain ⟨hlo, hw, arrX, arrY, arrM, hX, hY, hM, sX, sY, sM, gX, gY, gM⟩ := hf
    have bx : ∀ t, t < len → (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t).toNat ≤ m + 1 := by
      intro t ht
      rw [cellX_toNat m n margin xe xo wxe.xf wxo.mf hm hb t (by omega)]
      exact pointX_le m n margin xe xo wxe.xf wxo.mf hm t
    have by' : ∀ t, (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t).toNat ≤ m + 1 := by
      intro t
      rw [cellY_toNat m n len margin ye yo wye.yf wyo.mf hm hb hlen t]
      exact pointY_le m n len margin ye yo wye.yf wyo.mf hm t
    refine ⟨?_, ?_, ?_⟩
    · rw [hM, hw]
      apply wfa_padded m margin _ _ arrM (fun t => cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo t
        (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t)
        (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t)) sM gM
      intro t h1 h2
      rw [cellM_toNat m n margin xa ya dm wdm.mf hm hb hxa t (by omega) _ _ (bx t (by omega)) (by' t)]
      apply extR_le m xa ya hxa
      apply betterR_le
      · apply betterR_le
        · apply pushDR_le
          rw [rget_toRF m margin dm _ wdm.mf hm]; exact ugetA_bound m margin _ _ _ wdm.mf _
        · exact bx t (by omega)
      · exact by' t
    · rw [hX, hw]
      apply wfa_padded m margin _ _ arrX (fun t => cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t) sX gX
      intro t h1 h2
      exact bx t (by omega)
    · rw [hY, hw]
      apply wfa_padded m margin _ _ arrY (fun t => cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t) sY gY
      intro t _ _
      exact by' t

theorem uget_uLevel_mf (wxe : WF m margin xe) (wxo : WF m margin xo) (wye : WF m margin ye)
    (wyo : WF m margin yo) (wdm : WF m margin dm) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m) (t : Nat) (ht : t < len) :
    (uget margin (uLevel m n len margin xa ya xe xo ye yo dm) (·.mf) t).toNat =
      pointM m n xa ya (toRF margin dm (·.mf))
        (toRF margin (uLevel m n len margin xa ya xe xo ye yo dm) (·.xf))
        (toRF margin (uLevel m n len margin xa ya xe xo ye yo dm) (·.yf)) t := by
  have wl := wf_uLevel m n len margin xa ya xe xo ye yo dm wxe wxo wye wyo wdm hm hb hlen hxa
  obtain ⟨_, _, _, _, sdm⟩ := uBand_src len xe xo ye yo dm
  have hxf := uget_uLevel_xf m n len margin xa ya xe xo ye yo dm wxe wxo hm hb hlen t ht
  have hyf := uget_uLevel_yf m n len margin xa ya xe xo ye yo dm wye wyo hm hb hlen t ht
  by_cases he : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm
  · rw [uLevel_empty m n len margin xa ya xe xo ye yo dm he] at *
    rw [uget_uEmpty margin _ rfl]
    rw [pointM_zero]
    · rfl
    · rw [rget_toRF m margin dm _ wdm.mf hm]
      unfold uget
      rw [ugetA_out m margin dm.lo dm.w dm.mf wdm.mf hm t (src_out dm _ _ t t sdm (by omega) (by omega) (by omega))]
      rfl
    · rw [rget_toRF m margin uEmpty (fun x => x.xf) wl.xf hm, uget_uEmpty margin _ rfl]; rfl
    · rw [rget_toRF m margin uEmpty (fun x => x.yf) wl.yf hm, uget_uEmpty margin _ rfl]; rfl
  · have hf := uLevel_fronts m n len margin xa ya xe xo ye yo dm he
    simp only at hf
    obtain ⟨hlo, hw, arrX, arrY, arrM, hX, hY, hM, sX, sY, sM, gX, gY, gM⟩ := hf
    unfold pointM
    rw [rget_toRF m margin (uLevel m n len margin xa ya xe xo ye yo dm) (fun x => x.xf) wl.xf hm,
      rget_toRF m margin (uLevel m n len margin xa ya xe xo ye yo dm) (fun x => x.yf) wl.yf hm,
      rget_toRF m margin dm (fun x => x.mf) wdm.mf hm]
    simp only [uget] at hxf hyf ⊢
    rw [hlo, hM, hX, hY, ugetA_padded margin _ _ arrM (fun t => cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo t (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t) (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t)) sM gM hm,
      ugetA_padded margin _ _ arrX (fun t => cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t) sX gX hm, ugetA_padded margin _ _ arrY (fun t => cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t) sY gY hm]
    rw [hlo, hX, ugetA_padded margin _ _ arrX (fun t => cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t) sX gX hm] at hxf
    rw [hlo, hY, ugetA_padded margin _ _ arrY (fun t => cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t) sY gY hm] at hyf
    by_cases hin : uBandLo len xe xo ye yo dm ≤ t ∧ t < uBandLo len xe xo ye yo dm + (min (uBandHi xe xo ye yo dm) len - uBandLo len xe xo ye yo dm)
    · rw [if_pos hin] at hxf
      rw [if_pos hin] at hyf
      rw [if_pos hin, if_pos hin, if_pos hin]
      rw [cellM_toNat m n margin xa ya dm wdm.mf hm hb hxa t (by omega) _ _
        (by rw [hxf]; exact pointX_le m n margin xe xo wxe.xf wxo.mf hm t)
        (by rw [hyf]; exact pointY_le m n len margin ye yo wye.yf wyo.mf hm t),
        rget_toRF m margin dm (fun x => x.mf) wdm.mf hm]
      rfl
    · rw [if_neg hin] at hxf
      rw [if_neg hin] at hyf
      rw [if_neg hin, if_neg hin, if_neg hin]
      rw [ugetA_out m margin dm.lo dm.w dm.mf wdm.mf hm t
        (src_out dm _ _ t t sdm (by omega) (by omega) (by omega))]
      rfl

end Level


-- ══════════════════════════════════════════════════════════════════
-- The built level denotes `nextLevelR`
-- ══════════════════════════════════════════════════════════════════

/-- Two banded fronts with the same `rget` on every diagonal below `len` have
the same full-width denotation. -/
theorem rdenF_ext (len : Nat) (f g : RFront) (h : ∀ t, t < len → rget f t = rget g t) :
    rdenF len f = rdenF len g := by
  show bden len (rtob f) = bden len (rtob g)
  apply List.ext_getElem?
  intro i
  by_cases hi : i < len
  · rw [bget_den len i _ hi, bget_den len i _ hi, ← decodeR_rget, ← decodeR_rget, h i hi]
  · rw [List.getElem?_eq_none (by rw [bden_length]; omega),
      List.getElem?_eq_none (by rw [bden_length]; omega)]

theorem rdenL_toRLevel_uLevel (m n len margin pe po px : Nat) (xa ya : Array Char)
    (xe xo ye yo dm : ULevel) (hist' : List RLevel)
    (hxe : frontAtR hist' pe (·.xf) = toRF margin xe (·.xf))
    (hxo : frontAtR hist' po (·.mf) = toRF margin xo (·.mf))
    (hyo : frontAtR hist' po (·.mf) = toRF margin yo (·.mf))
    (hye : frontAtR hist' pe (·.yf) = toRF margin ye (·.yf))
    (hdm : frontAtR hist' px (·.mf) = toRF margin dm (·.mf))
    (wxe : WF m margin xe) (wxo : WF m margin xo) (wye : WF m margin ye)
    (wyo : WF m margin yo) (wdm : WF m margin dm) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m) :
    rdenL len (toRLevel margin (uLevel m n len margin xa ya xe xo ye yo dm)) =
      rdenL len (nextLevelR m n xa ya len pe po px hist') := by
  have wl := wf_uLevel m n len margin xa ya xe xo ye yo dm wxe wxo wye wyo wdm hm hb hlen hxa
  have hyo' : toRF margin yo (·.mf) = toRF margin xo (·.mf) := hyo.symm.trans hxo
  rw [← nextLevelP_eq]
  simp only [nextLevelP, hxe, hxo, hye, hdm]
  simp only [rdenL, toRLevel]
  congr 1
  · apply rdenF_ext
    intro t ht
    rw [packPointM_eq, ← pointM_eq,
      rget_toRF m margin _ (fun x => x.mf) wl.mf hm,
      uget_uLevel_mf m n len margin xa ya xe xo ye yo dm wxe wxo wye wyo wdm hm hb hlen hxa t ht]
    unfold pointM
    rw [packPointX_eq, packPointY_eq, ← pointX_eq, ← pointY_eq,
      rget_toRF m margin _ (fun x => x.xf) wl.xf hm,
      rget_toRF m margin _ (fun x => x.yf) wl.yf hm,
      uget_uLevel_xf m n len margin xa ya xe xo ye yo dm wxe wxo hm hb hlen t ht,
      uget_uLevel_yf m n len margin xa ya xe xo ye yo dm wye wyo hm hb hlen t ht, hyo']
  · apply rdenF_ext
    intro t ht
    rw [packPointX_eq, ← pointX_eq,
      rget_toRF m margin _ (fun x => x.xf) wl.xf hm,
      uget_uLevel_xf m n len margin xa ya xe xo ye yo dm wxe wxo hm hb hlen t ht]
  · apply rdenF_ext
    intro t ht
    rw [packPointY_eq, ← pointY_eq,
      rget_toRF m margin _ (fun x => x.yf) wl.yf hm,
      uget_uLevel_yf m n len margin xa ya xe xo ye yo dm wye wyo hm hb hlen t ht, hyo']

-- ══════════════════════════════════════════════════════════════════
-- The corner test
-- ══════════════════════════════════════════════════════════════════

def cornerU (margin m n : Nat) (lv : ULevel) : Bool :=
  uget margin lv (·.mf) n == m.toUInt32 + 1

theorem cornerU_eq (m n margin : Nat) (lv : ULevel) (wl : WF m margin lv) (hm : 1 ≤ margin)
    (hb : m + 2 < 2 ^ 30) :
    cornerU margin m n lv = cornerR m n (toRLevel margin lv) := by
  unfold cornerU cornerR toRLevel
  simp only
  rw [rget_toRF m margin lv (fun x => x.mf) wl.mf hm]
  have hs : (m.toUInt32 + 1).toNat = m + 1 := by
    rw [UInt32.toNat_succ _ (by rw [toNat_toUInt32_of_lt m (by omega)]; omega),
      toNat_toUInt32_of_lt m (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [h, hs]
  · intro h; exact UInt32.toNat_inj.mp (by rw [h, hs])

theorem cornerU_eq_cornerO (m n len margin : Nat) (lv : ULevel) (wl : WF m margin lv)
    (hm : 1 ≤ margin) (hb : m + 2 < 2 ^ 30) (hn : n < len) :
    cornerU margin m n lv = cornerO m n (rdenL len (toRLevel margin lv)) := by
  rw [cornerU_eq m n margin lv wl hm hb, cornerR_eq m n len hn]

end AlignmentSpec.U32Proof
