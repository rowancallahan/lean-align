import AlignmentWfaU32Step

/-!
# Hot cell loop of the second UInt32 kernel (definitions)

The level builder `uLevel2` computes exactly the arrays `uLevel`
(AlignmentWfaU32Step.lean, proven to denote `nextLevelR`) computes, but
with the loop shape of the measured probes (alignment/probes/ProbeCombo.lean,
ideas 1 and 4):

* `UInt32` loop counter and diagonal, `Array.uget`/`Array.uset` with the
  index bounds decided ONCE per level (`uLevel2` returns `none` if the check
  fails; the kernel then falls back to the proven `wfaAlignK`);
* three preallocated output arrays written by `uset` instead of `push`;
* an empty source reads a zero array (`srcArr`), allocated per level only
  when some source is empty;
* free extension `uext2`: two inline character comparisons, then the
  `USize` loop `lcpU` from `(off + 2, j + 2)`.

Every read shift is a `UInt32` fixed per level: cell `i` (diagonal
`lo + i`) reads index `i + sh` of the source array.  The arithmetic on codes
(`upushX`, `upushY`, `upushD`, `ubetter`, saturating `ujoff`) is the proven
one of AlignmentWfaU32Level.lean.

Lemmas about these definitions live in AlignmentWfaU32Ext.lean (`uext2 =
uext`), AlignmentWfaU32FillSpec.lean (the values the loop writes),
AlignmentWfaU32Level2.lean (`uLevel2 = some lv → lv = uLevel …` on
well-formed sources).
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- USize helpers
-- ══════════════════════════════════════════════════════════════════

theorem usize_toNat_add_one {i : USize} {s : Nat} (h : i.toNat < s) (hs : s < USize.size) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_one]
  exact Nat.mod_eq_of_lt (by unfold USize.size at hs; omega)

theorem usize_toNat_sub_one {f : USize} (h : f ≠ 0) : (f - 1).toNat = f.toNat - 1 ∧ 0 < f.toNat := by
  have hne : f.toNat ≠ 0 := fun h0 => h (USize.toNat_inj.mp (by rw [h0, USize.toNat_zero]))
  have hle : (1 : USize) ≤ f := by rw [USize.le_iff_toNat_le, USize.toNat_one]; omega
  have hs := USize.toNat_sub_of_le f 1 hle
  rw [USize.toNat_one] at hs
  exact ⟨hs, by omega⟩

/-- Tight LCP loop (probe idea 1).  Compares `xa[i]` with `ya[j]` for at
most `fuel` positions, all in bounds by `hi`/`hj`; returns the first index
`i'` of `xa` where the comparison fails (or `i + fuel`). -/
def lcpU (xa ya : Array Char) (i j fuel : USize)
    (hi : i.toNat + fuel.toNat ≤ xa.size) (hj : j.toNat + fuel.toNat ≤ ya.size)
    (hsx : xa.size < USize.size) (hsy : ya.size < USize.size) : USize :=
  if h0 : fuel = 0 then i else
    have hf := usize_toNat_sub_one h0
    have hi' : i.toNat < xa.size := by omega
    have hj' : j.toNat < ya.size := by omega
    if xa.uget i hi' == ya.uget j hj' then
      lcpU xa ya (i + 1) (j + 1) (fuel - 1)
        (by rw [usize_toNat_add_one hi' hsx, hf.1]; omega)
        (by rw [usize_toNat_add_one hj' hsy, hf.1]; omega) hsx hsy
    else i
termination_by fuel.toNat
decreasing_by all_goals (rw [hf.1]; omega)

/-- `lcpU` computes the spec `lcp` when `fuel` covers the shorter remaining suffix. -/
theorem lcpU_toNat (xa ya : Array Char) (i j fuel : USize)
    (hi : i.toNat + fuel.toNat ≤ xa.size) (hj : j.toNat + fuel.toNat ≤ ya.size)
    (hsx : xa.size < USize.size) (hsy : ya.size < USize.size)
    (hfull : fuel.toNat = min (xa.size - i.toNat) (ya.size - j.toNat)) :
    (lcpU xa ya i j fuel hi hj hsx hsy).toNat =
      i.toNat + lcp (xa.toList.drop i.toNat) (ya.toList.drop j.toNat) := by
  revert hfull
  induction i, j, fuel, hi, hj using lcpU.induct xa ya hsx hsy with
  | case1 i j hi hj =>
    intro hfull
    rw [lcpU, dif_pos rfl]
    rw [USize.toNat_zero] at hfull
    rcases Nat.le_total (xa.size - i.toNat) (ya.size - j.toNat) with h | h
    · rw [Nat.min_eq_left h] at hfull
      have : xa.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp; omega)
      simp [this, lcp]
    · rw [Nat.min_eq_right h] at hfull
      have : ya.toList.drop j.toNat = [] := List.drop_eq_nil_of_le (by simp; omega)
      cases hx : xa.toList.drop i.toNat <;> simp [this, lcp]
  | case2 i j fuel hi hj h0 hf hi' hj' heq ih =>
    intro hfull
    have hfull' : (fuel - 1).toNat = min (xa.size - (i + 1).toNat) (ya.size - (j + 1).toNat) := by
      rw [usize_toNat_add_one hi' hsx, usize_toNat_add_one hj' hsy, hf.1, hfull]; omega
    rw [lcpU, dif_neg h0, if_pos heq, ih hfull',
        usize_toNat_add_one hi' hsx, usize_toNat_add_one hj' hsy]
    have hxl : xa.toList.drop i.toNat = xa[i.toNat] :: xa.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi')]; simp
    have hyl : ya.toList.drop j.toNat = ya[j.toNat] :: ya.toList.drop (j.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj')]; simp
    have hc : xa[i.toNat] = ya[j.toNat] := by
      have := heq; simp only [Array.uget, beq_iff_eq] at this; exact this
    rw [hxl, hyl, lcp, if_pos hc]; omega
  | case3 i j fuel hi hj h0 hf hi' hj' hne =>
    intro hfull
    rw [lcpU, dif_neg h0, if_neg hne]
    have hxl : xa.toList.drop i.toNat = xa[i.toNat] :: xa.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi')]; simp
    have hyl : ya.toList.drop j.toNat = ya[j.toNat] :: ya.toList.drop (j.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj')]; simp
    have hc : ¬ xa[i.toNat] = ya[j.toNat] := by
      intro h; apply hne; simp only [Array.uget, beq_iff_eq]; exact h
    rw [hxl, hyl, lcp, if_neg hc]; omega

theorem lt_toNat_of_lt {a m : UInt32} {s : Nat} (h : a < m) (hm : m.toNat = s) :
    a.toUSize.toNat < s := by
  have := UInt32.lt_iff_toNat_lt.mp h; simp only [UInt32.toNat_toUSize]; omega

theorem size_lt_usize_of_uint32 {m : UInt32} {s : Nat} (hm : m.toNat = s) : s < USize.size :=
  Nat.lt_of_lt_of_le (hm ▸ UInt32.toNat_lt_size m) USize.le_size

-- ══════════════════════════════════════════════════════════════════
-- Free extension with two inline comparisons (idea 4) and `lcpU` (idea 1)
-- ══════════════════════════════════════════════════════════════════

/-- Free extension on codes, value `uext m xa ya t a` (AlignmentWfaU32Level.lean):
`a = 0 ↦ 0`; otherwise `off = a - 1`, `j = ujoff m t off` (saturating), and the
result is `off + lcp(off, j) + 1`, computed as: first comparison inline; if it
matches, second comparison inline; if both match, `lcpU` from `(off+2, j+2)`
returns `off + 2 + lcp(off+2, j+2)` and the result is that plus one. -/
@[inline] def uext2 (m n : UInt32) (xa ya : Array Char) (hm : m.toNat = xa.size)
    (hn : n.toNat = ya.size) (t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := ujoff m t off
    if h : off < m ∧ j < n then
      let c0 := (xa.uget off.toUSize (lt_toNat_of_lt h.1 hm) == ya.uget j.toUSize (lt_toNat_of_lt h.2 hn)).toUInt32
      let off1 := off + 1
      let j1 := j + 1
      if h1 : off1 < m ∧ j1 < n then
        let c1 := (xa.uget off1.toUSize (lt_toNat_of_lt h1.1 hm) == ya.uget j1.toUSize (lt_toNat_of_lt h1.2 hn)).toUInt32
        let c01 := c0 &&& c1
        if c01 = 1 then
          let i2 := off1 + 1
          let j2 := j1 + 1
          let fuel : UInt32 := if m - i2 ≤ n - j2 then m - i2 else n - j2
          have h1' : off1.toNat < m.toNat := UInt32.lt_iff_toNat_lt.mp h1.1
          have h2' : j1.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp h1.2
          have hm2 : m.toNat < 4294967296 := UInt32.toNat_lt_size m
          have hn2 : n.toNat < 4294967296 := UInt32.toNat_lt_size n
          have hi2 : i2.toNat = off1.toNat + 1 := by
            show (off1 + 1).toNat = _
            rw [UInt32.toNat_add, UInt32.toNat_one]
            exact Nat.mod_eq_of_lt (by omega)
          have hj2 : j2.toNat = j1.toNat + 1 := by
            show (j1 + 1).toNat = _
            rw [UInt32.toNat_add, UInt32.toNat_one]
            exact Nat.mod_eq_of_lt (by omega)
          have hf : fuel.toNat ≤ m.toNat - i2.toNat ∧ fuel.toNat ≤ n.toNat - j2.toNat := by
            have hle1 : i2 ≤ m := by rw [UInt32.le_iff_toNat_le]; omega
            have hle2 : j2 ≤ n := by rw [UInt32.le_iff_toNat_le]; omega
            have e1 := UInt32.toNat_sub_of_le m i2 hle1
            have e2 := UInt32.toNat_sub_of_le n j2 hle2
            show (if m - i2 ≤ n - j2 then m - i2 else n - j2).toNat ≤ _ ∧
                 (if m - i2 ≤ n - j2 then m - i2 else n - j2).toNat ≤ _
            split
            · rename_i hc; rw [UInt32.le_iff_toNat_le] at hc; omega
            · rename_i hc; rw [UInt32.le_iff_toNat_le] at hc; omega
          (lcpU xa ya i2.toUSize j2.toUSize fuel.toUSize
            (by simp only [UInt32.toNat_toUSize]; omega)
            (by simp only [UInt32.toNat_toUSize]; omega)
            (size_lt_usize_of_uint32 hm) (size_lt_usize_of_uint32 hn)).toUInt32 + 1
        else a + c0 + c01
      else a + c0
    else a

-- ══════════════════════════════════════════════════════════════════
-- The cell loop
-- ══════════════════════════════════════════════════════════════════

/-- Index bound for a read/write at `i + sh` with `i < w`, from
`w + sh ≤ size < 2^32` (decided once per level). -/
theorem idx2 {i w sh : UInt32} {size : Nat} (hi : i < w) (hw : w.toNat + sh.toNat ≤ size)
    (hs : size < 2 ^ 32) : (i + sh).toUSize.toNat < size := by
  have := UInt32.lt_iff_toNat_lt.mp hi
  simp only [UInt32.toNat_toUSize, UInt32.toNat_add]
  omega

theorem succ_lt_toNat2 {i w : UInt32} (hi : i < w) : w.toNat - (i + 1).toNat < w.toNat - i.toNat := by
  have := UInt32.lt_iff_toNat_lt.mp hi
  have := UInt32.toNat_lt_size w
  have h1 : (1 : UInt32).toNat = 1 := rfl
  simp only [UInt32.toNat_add, UInt32.size, h1] at *
  omega

/-- The values the loop writes, as functions of the cell index `i` and the
diagonal `t32 = lo + i` (reads written with `getD`, no proofs; the loop
below reads with `uget`, which is the same value in bounds). -/
@[inline] def cellX2 (m32 n32 : UInt32) (xeA xoA : Array UInt32) (shXe shXo i t32 : UInt32) : UInt32 :=
  if t32 = 0 then 0 else
    ubetter (upushX m32 n32 (t32 - 1) (xeA.getD (i + shXe).toNat 0))
            (upushX m32 n32 (t32 - 1) (xoA.getD (i + shXo).toNat 0))

@[inline] def cellY2 (m32 len32 : UInt32) (yeA yoA : Array UInt32) (shYe shYo i t32 : UInt32) : UInt32 :=
  if t32 + 1 < len32 then
    ubetter (upushY m32 (t32 + 1) (yeA.getD (i + shYe).toNat 0))
            (upushY m32 (t32 + 1) (yoA.getD (i + shYo).toNat 0))
  else 0

@[inline] def cellM2 (m32 n32 : UInt32) (xa ya : Array Char) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (dmA : Array UInt32) (shDm i t32 : UInt32) (x y : UInt32) : UInt32 :=
  uext2 m32 n32 xa ya hm hn t32
    (ubetter (ubetter (upushD m32 n32 t32 (dmA.getD (i + shDm).toNat 0)) x) y)

/-- The cell loop: cells `i, i+1, …, w-1` (diagonals `t32, t32+1, …`), five
source reads per cell, written at `i + mg` of the three preallocated output
arrays (all of size `size`).  The reads: X sources at index `i + shXe` /
`i + shXo` (diagonal `t - 1`), Y sources at `i + shYe` / `i + shYo`
(diagonal `t + 1`), the diagonal source at `i + shDm`. -/
def uFillGo2 (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm mg : UInt32) (size : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32)
    (i t32 : UInt32) (mf xf yf : Array UInt32)
    (hmf : mf.size = size) (hxf : xf.size = size) (hyf : yf.size = size) :
    Array UInt32 × Array UInt32 × Array UInt32 :=
  if h : i < w then
    let x : UInt32 :=
      if t32 = 0 then 0 else
        ubetter (upushX m32 n32 (t32 - 1) (xeA.uget (i + shXe).toUSize (idx2 h hxe hxe')))
                (upushX m32 n32 (t32 - 1) (xoA.uget (i + shXo).toUSize (idx2 h hxo hxo')))
    let y : UInt32 :=
      if t32 + 1 < len32 then
        ubetter (upushY m32 (t32 + 1) (yeA.uget (i + shYe).toUSize (idx2 h hye hye')))
                (upushY m32 (t32 + 1) (yoA.uget (i + shYo).toUSize (idx2 h hyo hyo')))
      else 0
    let d := upushD m32 n32 t32 (dmA.uget (i + shDm).toUSize (idx2 h hdm hdm'))
    let e := uext2 m32 n32 xa ya hm hn t32 (ubetter (ubetter d x) y)
    uFillGo2 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm mg size
      hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hout hsz (i + 1) (t32 + 1)
      (mf.uset (i + mg).toUSize e (by rw [hmf]; exact idx2 h hout hsz))
      (xf.uset (i + mg).toUSize x (by rw [hxf]; exact idx2 h hout hsz))
      (yf.uset (i + mg).toUSize y (by rw [hyf]; exact idx2 h hout hsz))
      (by rw [Array.size_uset]; exact hmf) (by rw [Array.size_uset]; exact hxf)
      (by rw [Array.size_uset]; exact hyf)
  else (mf, xf, yf)
termination_by w.toNat - i.toNat
decreasing_by exact succ_lt_toNat2 h

-- ══════════════════════════════════════════════════════════════════
-- The level builder
-- ══════════════════════════════════════════════════════════════════

/-- Source array of a read: an empty source reads the shared zero array. -/
@[inline] def srcArr (zeros : Array UInt32) (s : ULevel) (sel : ULevel → Array UInt32) : Array UInt32 :=
  if s.w = 0 then zeros else sel s

/-- Base read shift of a source for a level whose band starts at `lo`: cell
`i` (diagonal `lo + i`) reads diagonal `lo + i` of the source at index
`i + base`; X reads (diagonal `t - 1`) use `base - 1`, Y reads (`t + 1`) use
`base + 1`.  An empty source reads the zero array at any shift. -/
@[inline] def srcBase (margin lo : Nat) (s : ULevel) : Nat :=
  if s.w = 0 then margin + 1 else margin + lo - s.lo

/-- Per-source part of the once-per-level check: a non-empty source starts
at most `margin - 1` diagonals after the new band (so the shift arithmetic
never truncates), every read `i + sh` with `i < w` is inside the source array,
and the shift fits a `UInt32`. -/
def SrcOK (margin lo w : Nat) (zeros : Array UInt32) (s : ULevel) (sel : ULevel → Array UInt32)
    (sh : Nat) : Prop :=
  (0 < s.w → s.lo + 1 ≤ margin + lo) ∧ w + sh ≤ (srcArr zeros s sel).size
    ∧ (srcArr zeros s sel).size < 2 ^ 32 ∧ sh < UInt32.size

/-- `a < 2^32` as a scalar test.  The literal `4294967296` does not fit the
compiler's 32-bit immediate form, so a runtime comparison against it goes
through `lean_cstr_to_nat` (string → bignum) on every evaluation — measured
at about a microsecond per level with six such comparisons; the shift test
is one scalar operation. -/
@[inline] def lt32 (a : Nat) : Bool := a >>> 32 == 0

theorem lt32_iff (a : Nat) : lt32 a = true ↔ a < 2 ^ 32 := by
  unfold lt32
  rw [beq_iff_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 32))
    · exact h
  · intro h; exact Or.inr h

/-- The runtime form of `SrcOK` (short-circuit Bool, scalar bounds). -/
@[inline] def srcOKB (margin lo w : Nat) (zeros : Array UInt32) (s : ULevel) (sel : ULevel → Array UInt32)
    (sh : Nat) : Bool :=
  (s.w == 0 || s.lo + 1 ≤ margin + lo) && w + sh ≤ (srcArr zeros s sel).size
    && lt32 (srcArr zeros s sel).size && lt32 sh

theorem srcOKB_true (margin lo w : Nat) (zeros : Array UInt32) (s : ULevel) (sel : ULevel → Array UInt32)
    (sh : Nat) (h : srcOKB margin lo w zeros s sel sh = true) : SrcOK margin lo w zeros s sel sh := by
  unfold srcOKB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, lt32_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun hw => ?_, h2, h3, h4⟩
  rcases h1 with h1 | h1
  · omega
  · exact h1

/-- The once-per-level index check of `uLevel2` (decidable).  X sources are
read at diagonal `t - 1` (shift `base - 1`), Y sources at `t + 1` (`base + 1`),
the diagonal source at `t` (`base`). -/
def LevelCheck (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : ULevel) : Prop :=
  w < UInt32.size ∧ margin < UInt32.size ∧ w + 2 * margin < 2 ^ 32 ∧ w + margin ≤ w + 2 * margin
    ∧ SrcOK margin lo w zeros xe (·.xf) (srcBase margin lo xe - 1)
    ∧ SrcOK margin lo w zeros xo (·.mf) (srcBase margin lo xo - 1)
    ∧ SrcOK margin lo w zeros ye (·.yf) (srcBase margin lo ye + 1)
    ∧ SrcOK margin lo w zeros yo (·.mf) (srcBase margin lo yo + 1)
    ∧ SrcOK margin lo w zeros dm (·.mf) (srcBase margin lo dm)

/-- The runtime form of `LevelCheck`. -/
@[inline] def levelCheckB (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : ULevel) : Bool :=
  lt32 w && lt32 margin && lt32 (w + 2 * margin) && w + margin ≤ w + 2 * margin
    && srcOKB margin lo w zeros xe (·.xf) (srcBase margin lo xe - 1)
    && srcOKB margin lo w zeros xo (·.mf) (srcBase margin lo xo - 1)
    && srcOKB margin lo w zeros ye (·.yf) (srcBase margin lo ye + 1)
    && srcOKB margin lo w zeros yo (·.mf) (srcBase margin lo yo + 1)
    && srcOKB margin lo w zeros dm (·.mf) (srcBase margin lo dm)

theorem levelCheckB_true (margin lo w : Nat) (zeros : Array UInt32) (xe xo ye yo dm : ULevel)
    (h : levelCheckB margin lo w zeros xe xo ye yo dm = true) : LevelCheck margin lo w zeros xe xo ye yo dm := by
  unfold levelCheckB at h
  simp only [Bool.and_eq_true, lt32_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, srcOKB_true _ _ _ _ _ _ _ h5, srcOKB_true _ _ _ _ _ _ _ h6,
    srcOKB_true _ _ _ _ _ _ _ h7, srcOKB_true _ _ _ _ _ _ _ h8, srcOKB_true _ _ _ _ _ _ _ h9⟩

/-- The level body once the check `h` holds: the three arrays the loop fills. -/
def uLevel2Body (margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size) (zeros : Array UInt32)
    (xe xo ye yo dm : ULevel) (lo w : Nat) (h : LevelCheck margin lo w zeros xe xo ye yo dm) : ULevel :=
  have hxe := h.2.2.2.2.1
  have hxo := h.2.2.2.2.2.1
  have hye := h.2.2.2.2.2.2.1
  have hyo := h.2.2.2.2.2.2.2.1
  have hdm := h.2.2.2.2.2.2.2.2
  let r := uFillGo2 xa ya m32 n32 len32 hm hn (UInt32.ofNatLT w h.1)
    (srcArr zeros xe (·.xf)) (srcArr zeros xo (·.mf)) (srcArr zeros ye (·.yf))
    (srcArr zeros yo (·.mf)) (srcArr zeros dm (·.mf))
    (UInt32.ofNatLT (srcBase margin lo xe - 1) hxe.2.2.2) (UInt32.ofNatLT (srcBase margin lo xo - 1) hxo.2.2.2)
    (UInt32.ofNatLT (srcBase margin lo ye + 1) hye.2.2.2) (UInt32.ofNatLT (srcBase margin lo yo + 1) hyo.2.2.2)
    (UInt32.ofNatLT (srcBase margin lo dm) hdm.2.2.2) (UInt32.ofNatLT margin h.2.1) (w + 2 * margin)
    (by simp only [UInt32.toNat_ofNatLT]; exact hxe.2.1) hxe.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hxo.2.1) hxo.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hye.2.1) hye.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hyo.2.1) hyo.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hdm.2.1) hdm.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact h.2.2.2.1) h.2.2.1
    0 lo.toUInt32 (Array.replicate (w + 2 * margin) 0) (Array.replicate (w + 2 * margin) 0)
    (Array.replicate (w + 2 * margin) 0)
    Array.size_replicate Array.size_replicate Array.size_replicate
  ⟨lo, w, r.1, r.2.1, r.2.2⟩

/-- Build a level from its five sources; `none` if the once-per-level index
check fails (the kernel then falls back).  Whenever the result is `some lv`
and the sources are well-formed, `lv = uLevel m n len margin xa ya xe xo ye yo dm`
(AlignmentWfaU32Level2.lean). -/
def uLevel2 (len margin : Nat) (m32 n32 len32 : UInt32) (xa ya : Array Char)
    (hm : m32.toNat = xa.size) (hn : n32.toNat = ya.size)
    (xe xo ye yo dm : ULevel) : Option ULevel :=
  let lo := uBandLo len xe xo ye yo dm
  let hi := min (uBandHi xe xo ye yo dm) len
  if hi ≤ lo then some uEmpty else
  let w := hi - lo
  -- the shared zero array for empty sources, allocated only when one is empty
  let zeros : Array UInt32 :=
    if xe.w = 0 || xo.w = 0 || ye.w = 0 || yo.w = 0 || dm.w = 0 then Array.replicate (w + 2 * margin + 2) 0 else #[]
  if h : levelCheckB margin lo w zeros xe xo ye yo dm then
    some (uLevel2Body margin m32 n32 len32 xa ya hm hn zeros xe xo ye yo dm lo w
      (levelCheckB_true margin lo w zeros xe xo ye yo dm h))
  else none


-- ══════════════════════════════════════════════════════════════════
-- The single-source cell loop (level builder: AlignmentWfaU32FillS.lean)
-- ══════════════════════════════════════════════════════════════════

/-- One single-source cell: `prev / cur / next` are the previous M front at
diagonals `t - 1`, `t`, `t + 1`. -/
@[inline] def uCellS (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (t32 prev cur next : UInt32) : UInt32 :=
  let x : UInt32 := if t32 = 0 then 0 else upushX m32 n32 (t32 - 1) prev
  let y : UInt32 := if t32 + 1 < len32 then upushY m32 (t32 + 1) next else 0
  let d := upushD m32 n32 t32 cur
  uext2 m32 n32 xa ya hm hn t32 (ubetter (ubetter d x) y)

/-- The value written for cell `i` (diagonal `t32`), reads written with `getD`:
`prev` is the source at index `i + sh1 - 2`, `cur` at `i + sh1 - 1`, `next` at `i + sh1`. -/
@[inline] def cellS (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (srcA : Array UInt32) (sh1 : UInt32) (i t32 : UInt32) : UInt32 :=
  uCellS xa ya m32 n32 len32 hm hn t32
    (srcA.getD (i.toNat + sh1.toNat - 2) 0) (srcA.getD (i.toNat + sh1.toNat - 1) 0)
    (srcA.getD (i.toNat + sh1.toNat) 0)

theorem lt_of_succ_lt2 {i w : UInt32} (hi : i ≤ w) (hw : w.toNat + 1 < 2 ^ 32) (h : i + 1 < w) :
    i < w := by
  have h1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.lt_iff_toNat_lt] at *
  rw [UInt32.le_iff_toNat_le] at hi
  rw [UInt32.toNat_add, h1] at h
  omega

theorem succ_le_of_lt2 {i w : UInt32} (h : i < w) : i + 1 ≤ w := by
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have := UInt32.toNat_lt_size w
  rw [UInt32.lt_iff_toNat_lt] at h
  rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, h1]
  simp only [UInt32.size] at this
  omega

/-- Single-source cell loop: cells `i, …, w-1`; `prev`/`cur` are the source at
`i + sh1 - 2` and `i + sh1 - 1`, the loop reads `next` at `i + sh1` and writes
the cell at `i + mg`.  Two cells per iteration while `i + 1 < w`, one in the tail. -/
def uFillS (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32) (hw : w.toNat + 1 < 2 ^ 32) (srcA : Array UInt32)
    (sh1 mg : UInt32) (size : Nat)
    (hsrc : w.toNat + sh1.toNat ≤ srcA.size) (hsrc' : srcA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32)
    (i : UInt32) (hi : i ≤ w) (t32 prev cur : UInt32) (mf : Array UInt32) (hmf : mf.size = size) :
    Array UInt32 :=
  if h2 : i + 1 < w then
    have h : i < w := lt_of_succ_lt2 hi hw h2
    let next := srcA.uget (i + sh1).toUSize (idx2 h hsrc hsrc')
    let next2 := srcA.uget (i + 1 + sh1).toUSize (idx2 h2 hsrc hsrc')
    let e1 := uCellS xa ya m32 n32 len32 hm hn t32 prev cur next
    let e2 := uCellS xa ya m32 n32 len32 hm hn (t32 + 1) cur next next2
    let mf1 := mf.uset (i + mg).toUSize e1 (by rw [hmf]; exact idx2 h hout hsz)
    uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
      (i + 1 + 1) (succ_le_of_lt2 h2) (t32 + 1 + 1) next next2
      (mf1.uset (i + 1 + mg).toUSize e2 (by rw [Array.size_uset, hmf]; exact idx2 h2 hout hsz))
      (by rw [Array.size_uset, Array.size_uset]; exact hmf)
  else if h : i < w then
    let next := srcA.uget (i + sh1).toUSize (idx2 h hsrc hsrc')
    let e := uCellS xa ya m32 n32 len32 hm hn t32 prev cur next
    uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
      (i + 1) (succ_le_of_lt2 h) (t32 + 1) cur next
      (mf.uset (i + mg).toUSize e (by rw [hmf]; exact idx2 h hout hsz))
      (by rw [Array.size_uset]; exact hmf)
  else mf
termination_by w.toNat - i.toNat
decreasing_by
  · exact Nat.lt_trans (succ_lt_toNat2 h2) (succ_lt_toNat2 h)
  · exact succ_lt_toNat2 h

-- ══════════════════════════════════════════════════════════════════
-- The block-layout cell loop (level builder: AlignmentWfaU32Fill3.lean)
-- ══════════════════════════════════════════════════════════════════

/-- General cell loop in the block layout: the same reads and cell values as
`uFillGo2` (`cellX2`/`cellY2`/`cellM2` on the source arrays with their
shifts, the source's block offset folded into the shift), the three fronts
written into ONE array at `i + oM` (M), `i + oX` (X), `i + oY` (Y).
This loop must stay in this file: `lcpU` is inlined by the C compiler only
within its translation unit. -/
def uFillGo3 (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm oM oX oY : UInt32) (size3 : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hoM : w.toNat + oM.toNat ≤ size3) (hoX : w.toNat + oX.toNat ≤ size3)
    (hoY : w.toNat + oY.toNat ≤ size3) (hsz : size3 < 2 ^ 32)
    (i t32 : UInt32) (f : Array UInt32) (hf : f.size = size3) : Array UInt32 :=
  if h : i < w then
    let x : UInt32 :=
      if t32 = 0 then 0 else
        ubetter (upushX m32 n32 (t32 - 1) (xeA.uget (i + shXe).toUSize (idx2 h hxe hxe')))
                (upushX m32 n32 (t32 - 1) (xoA.uget (i + shXo).toUSize (idx2 h hxo hxo')))
    let y : UInt32 :=
      if t32 + 1 < len32 then
        ubetter (upushY m32 (t32 + 1) (yeA.uget (i + shYe).toUSize (idx2 h hye hye')))
                (upushY m32 (t32 + 1) (yoA.uget (i + shYo).toUSize (idx2 h hyo hyo')))
      else 0
    let d := upushD m32 n32 t32 (dmA.uget (i + shDm).toUSize (idx2 h hdm hdm'))
    let e := uext2 m32 n32 xa ya hm hn t32 (ubetter (ubetter d x) y)
    let f1 := f.uset (i + oM).toUSize e (by rw [hf]; exact idx2 h hoM hsz)
    let f2 := f1.uset (i + oX).toUSize x (by rw [Array.size_uset, hf]; exact idx2 h hoX hsz)
    let f3 := f2.uset (i + oY).toUSize y (by rw [Array.size_uset, Array.size_uset, hf]; exact idx2 h hoY hsz)
    uFillGo3 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm oM oX oY size3
      hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hoM hoX hoY hsz (i + 1) (t32 + 1) f3
      (by simp only [f3, f2, f1, Array.size_uset]; exact hf)
  else f
termination_by w.toNat - i.toNat
decreasing_by exact succ_lt_toNat2 h

end AlignmentSpec.U32Proof
