import AlignmentWfaU32Fill
import AlignmentWfaU32FillSpec
import AlignmentWfaU32Ext

/-!
# The hot-loop level builder computes the proven builder's arrays

`uLevel2_some`: whenever `uLevel2` (AlignmentWfaU32Fill.lean) returns a
level from well-formed sources, that level is exactly
`uLevel m n len margin xa ya xe xo ye yo dm` (AlignmentWfaU32Step.lean, proven
to denote `nextLevelR`).  Array for array: the same band, and on every index
the same code — the once-per-level check guarantees that every `uget` read of
the new loop is the `getD` read of the old one, and `uext2_eq` that the
inline-compare extension is the old extension.
-/
namespace AlignmentSpec.U32Proof

theorem wfa_empty_getD (m margin : Nat) (f : Array UInt32) (h : WFA m margin 0 f) (idx : Nat) :
    f.getD idx 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?]
  cases hi : f[idx]? with
  | none => rfl
  | some v =>
    have hlt : idx < f.size := by
      rcases Nat.lt_or_ge idx f.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hi; cases hi
    have hv : f[idx] = v := by rw [Array.getElem?_eq_getElem hlt] at hi; cases hi; rfl
    simp only [Option.getD_some]
    rw [← hv]
    exact h.pad idx hlt (by omega)

theorem replicate_getD (k idx : Nat) : (Array.replicate k (0 : UInt32)).getD idx 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem arr_ext? (a b : Array UInt32) (h : ∀ i : Nat, a[i]? = b[i]?) : a = b := by
  have hs : a.size = b.size := by
    rcases Nat.lt_trichotomy a.size b.size with h1 | h1 | h1
    · have := h a.size
      rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h1] at this
      cases this
    · exact h1
    · have := h b.size
      rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h1] at this
      cases this
  apply Array.ext hs
  intro i h1 h2
  have := h i
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this
  exact Option.some.inj this

theorem toUInt32_add_of_lt (a b : Nat) (h : a + b < 2 ^ 32) : a.toUInt32 + b.toUInt32 = (a + b).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by change a < 4294967296; omega),
    UInt32.toNat_ofNat_of_lt' (by change b < 4294967296; omega),
    UInt32.toNat_ofNat_of_lt' (by change a + b < 4294967296; omega)]
  exact Nat.mod_eq_of_lt (by change a + b < 4294967296; omega)

theorem toUInt32_eq_zero_iff (t : Nat) (ht : t < 2 ^ 30) : t.toUInt32 = 0 ↔ t = 0 := by
  rw [UInt32.toNat_eq_zero_iff, toNat_toUInt32_of_lt t ht]

theorem toUInt32_pred (t : Nat) (ht : t < 2 ^ 30) (h0 : t ≠ 0) : t.toUInt32 - 1 = (t - 1).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_pred _ (fun h => h0 ((toUInt32_eq_zero_iff t ht).mp h)),
    toNat_toUInt32_of_lt t ht, toNat_toUInt32_of_lt (t - 1) (by omega)]

theorem toUInt32_lt_iff (a b : Nat) (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) : a.toUInt32 < b.toUInt32 ↔ a < b := by
  rw [UInt32.lt_iff_toNat_lt, toNat_toUInt32_of_lt a ha, toNat_toUInt32_of_lt b hb]

/-- The read index of the new loop is the read index of the old one. -/
theorem read_index (k sh : Nat) (hk : k + sh < 2 ^ 32) :
    (k.toUInt32 + UInt32.ofNatLT sh (by change sh < 4294967296; omega)).toNat = k + sh := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNatLT, UInt32.toNat_ofNat_of_lt' (by change k < 4294967296; omega)]
  exact Nat.mod_eq_of_lt (by change k + sh < 4294967296; omega)


/-- X read: cell `k` at shift `base - 1` reads diagonal `lo + k - 1` of the source. -/
theorem read_X (m margin lo k : Nat) (zeros : Array UInt32) (hz : ∀ i, zeros.getD i 0 = 0)
    (s : ULevel) (sel : ULevel → Array UInt32) (hw : WFA m margin s.w (sel s))
    (hok : 0 < s.w → s.lo + 1 ≤ margin + lo) (hk1 : 1 ≤ lo + k)
    (hb : k + (srcBase margin lo s - 1) < 2 ^ 32) :
    (srcArr zeros s sel).getD (k.toUInt32 + UInt32.ofNatLT (srcBase margin lo s - 1)
        (by change _ < 4294967296; omega)).toNat 0 =
      ugetA margin s.lo (sel s) (lo + k - 1) := by
  rw [read_index k _ hb]
  unfold srcArr srcBase ugetA
  by_cases h0 : s.w = 0
  · rw [if_pos h0, if_pos h0, hz]
    exact (wfa_empty_getD m margin (sel s) (h0 ▸ hw) _).symm
  · rw [if_neg h0, if_neg h0]
    have := hok (Nat.pos_of_ne_zero h0)
    congr 1; omega

/-- Y read: shift `base + 1` reads diagonal `lo + k + 1`. -/
theorem read_Y (m margin lo k : Nat) (zeros : Array UInt32) (hz : ∀ i, zeros.getD i 0 = 0)
    (s : ULevel) (sel : ULevel → Array UInt32) (hw : WFA m margin s.w (sel s))
    (hok : 0 < s.w → s.lo + 1 ≤ margin + lo)
    (hb : k + (srcBase margin lo s + 1) < 2 ^ 32) :
    (srcArr zeros s sel).getD (k.toUInt32 + UInt32.ofNatLT (srcBase margin lo s + 1)
        (by change _ < 4294967296; omega)).toNat 0 =
      ugetA margin s.lo (sel s) (lo + k + 1) := by
  rw [read_index k _ hb]
  unfold srcArr srcBase ugetA
  by_cases h0 : s.w = 0
  · rw [if_pos h0, if_pos h0, hz]
    exact (wfa_empty_getD m margin (sel s) (h0 ▸ hw) _).symm
  · rw [if_neg h0, if_neg h0]
    have := hok (Nat.pos_of_ne_zero h0)
    congr 1; omega

/-- Diagonal read: shift `base` reads diagonal `lo + k`. -/
theorem read_D (m margin lo k : Nat) (zeros : Array UInt32) (hz : ∀ i, zeros.getD i 0 = 0)
    (s : ULevel) (sel : ULevel → Array UInt32) (hw : WFA m margin s.w (sel s))
    (hok : 0 < s.w → s.lo + 1 ≤ margin + lo)
    (hb : k + srcBase margin lo s < 2 ^ 32) :
    (srcArr zeros s sel).getD (k.toUInt32 + UInt32.ofNatLT (srcBase margin lo s)
        (by change _ < 4294967296; omega)).toNat 0 =
      ugetA margin s.lo (sel s) (lo + k) := by
  rw [read_index k _ hb]
  unfold srcArr srcBase ugetA
  by_cases h0 : s.w = 0
  · rw [if_pos h0, if_pos h0, hz]
    exact (wfa_empty_getD m margin (sel s) (h0 ▸ hw) _).symm
  · rw [if_neg h0, if_neg h0]
    have := hok (Nat.pos_of_ne_zero h0)
    congr 1; omega

section Level2
variable (m n len margin : Nat) (xa ya : Array Char) (zeros : Array UInt32) (xe xo ye yo dm : ULevel)

theorem cellX2_eq (wxe : WF m margin xe) (wxo : WF m margin xo)
    (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat) (hb : m + n + 2 < 2 ^ 30) (ht : lo + k < 2 ^ 30)
    (hxe : SrcOK margin lo (k + 1) zeros xe (·.xf) (srcBase margin lo xe - 1))
    (hxo : SrcOK margin lo (k + 1) zeros xo (·.mf) (srcBase margin lo xo - 1)) :
    cellX2 m.toUInt32 n.toUInt32 (srcArr zeros xe (·.xf)) (srcArr zeros xo (·.mf))
        (UInt32.ofNatLT (srcBase margin lo xe - 1) hxe.2.2.2) (UInt32.ofNatLT (srcBase margin lo xo - 1) hxo.2.2.2)
        k.toUInt32 (lo + k).toUInt32 =
      cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + k) := by
  unfold cellX2 cellX
  by_cases h0 : lo + k = 0
  · rw [if_pos ((toUInt32_eq_zero_iff _ ht).mpr h0), if_pos h0]
  · rw [if_neg (fun h => h0 ((toUInt32_eq_zero_iff _ ht).mp h)), if_neg h0, toUInt32_pred _ ht h0]
    have e1 := read_X m margin lo k zeros hz xe (·.xf) wxe.xf hxe.1 (by omega) (by have := hxe.2.1; have := hxe.2.2.1; omega)
    have e2 := read_X m margin lo k zeros hz xo (·.mf) wxo.mf hxo.1 (by omega) (by have := hxo.2.1; have := hxo.2.2.1; omega)
    rw [e1, e2]

theorem cellY2_eq (wye : WF m margin ye) (wyo : WF m margin yo)
    (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1)
    (ht : lo + k + 1 < 2 ^ 30)
    (hye : SrcOK margin lo (k + 1) zeros ye (·.yf) (srcBase margin lo ye + 1))
    (hyo : SrcOK margin lo (k + 1) zeros yo (·.mf) (srcBase margin lo yo + 1)) :
    cellY2 m.toUInt32 len.toUInt32 (srcArr zeros ye (·.yf)) (srcArr zeros yo (·.mf))
        (UInt32.ofNatLT (srcBase margin lo ye + 1) hye.2.2.2) (UInt32.ofNatLT (srcBase margin lo yo + 1) hyo.2.2.2)
        k.toUInt32 (lo + k).toUInt32 =
      cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + k) := by
  unfold cellY2 cellY
  have hs : (lo + k).toUInt32 + 1 = (lo + k + 1).toUInt32 := toUInt32_add_of_lt (lo + k) 1 (by omega)
  rw [hs]
  by_cases h0 : lo + k + 1 < len
  · rw [if_pos ((toUInt32_lt_iff _ _ (by omega) (by omega)).mpr h0), if_pos h0]
    have e1 := read_Y m margin lo k zeros hz ye (·.yf) wye.yf hye.1 (by have := hye.2.1; have := hye.2.2.1; omega)
    have e2 := read_Y m margin lo k zeros hz yo (·.mf) wyo.mf hyo.1 (by have := hyo.2.1; have := hyo.2.2.1; omega)
    rw [e1, e2]
  · rw [if_neg (fun h => h0 ((toUInt32_lt_iff _ _ (by omega) (by omega)).mp h)), if_neg h0]

theorem cellM2_eq (wdm : WF m margin dm) (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat)
    (hb : m + n + 2 < 2 ^ 30) (ht : lo + k < 2 ^ 30) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size)
    (hdm : SrcOK margin lo (k + 1) zeros dm (·.mf) (srcBase margin lo dm))
    (x y : UInt32) (hx : x.toNat ≤ m + 1) (hy : y.toNat ≤ m + 1) :
    cellM2 m.toUInt32 n.toUInt32 xa ya hm32 hn32 (srcArr zeros dm (·.mf))
        (UInt32.ofNatLT (srcBase margin lo dm) hdm.2.2.2) k.toUInt32 (lo + k).toUInt32 x y =
      cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo (lo + k) x y := by
  unfold cellM2 cellM
  have e := read_D m margin lo k zeros hz dm (·.mf) wdm.mf hdm.1 (by have := hdm.2.1; have := hdm.2.2.1; omega)
  rw [e]
  apply uext2_eq
  have hmN := toNat_toUInt32_of_lt m (by omega)
  have hnN := toNat_toUInt32_of_lt n (by omega)
  have htN := toNat_toUInt32_of_lt (lo + k) ht
  have bdm := ugetA_bound m margin dm.lo dm.w dm.mf wdm.mf (lo + k)
  have hd : (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32 (ugetA margin dm.lo dm.mf (lo + k))).toNat ≤ m + 1 := by
    rw [upushD_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩, hmN, hnN, htN]
    exact pushDR_le m n _ _ bdm
  have hb1 : (ubetter (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32 (ugetA margin dm.lo dm.mf (lo + k))) x).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hd hx
  have hb2 : (ubetter (ubetter (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32 (ugetA margin dm.lo dm.mf (lo + k))) x) y).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hb1 hy
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Code bounds of the old cells (they denote `pointX`/`pointY`, which are ≤ m + 1). -/
theorem cellX_le (wxe : WF m margin xe) (wxo : WF m margin xo) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (t : Nat) (ht : t < 2 ^ 30) :
    (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo t).toNat ≤ m + 1 := by
  rw [cellX_toNat m n margin xe xo wxe.xf wxo.mf hm hb t ht]
  exact pointX_le m n margin xe xo wxe.xf wxo.mf hm t

theorem cellY_le (wye : WF m margin ye) (wyo : WF m margin yo) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (t : Nat) :
    (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo t).toNat ≤ m + 1 := by
  rw [cellY_toNat m n len margin ye yo wye.yf wyo.mf hm hb hlen t]
  exact pointY_le m n len margin ye yo wye.yf wyo.mf hm t

/-- `SrcOK` for the whole band gives `SrcOK` for the prefix up to any cell. -/
theorem srcOK_mono (lo w k : Nat) (s : ULevel) (sel : ULevel → Array UInt32) (sh : Nat)
    (h : SrcOK margin lo w zeros s sel sh) (hk : k < w) : SrcOK margin lo (k + 1) zeros s sel sh :=
  ⟨h.1, by have := h.2.1; omega, h.2.2.1, h.2.2.2⟩

/-- The filled body equals the padded arrays of the proven builder. -/
theorem uLevel2Body_eq (wxe : WF m margin xe) (wxo : WF m margin xo) (wye : WF m margin ye)
    (wyo : WF m margin yo) (wdm : WF m margin dm) (hz : ∀ i, zeros.getD i 0 = 0)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size)
    (lo w : Nat) (hc : LevelCheck margin lo w zeros xe xo ye yo dm) (hlolen : lo + w ≤ len)
    (arrX arrY arrM : Array UInt32)
    (sx : arrX.size = margin + w) (sy : arrY.size = margin + w) (sm : arrM.size = margin + w)
    (gx : ∀ i, arrX[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (i - margin))) else none)
    (gy : ∀ i, arrY[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (i - margin))) else none)
    (gm : ∀ i, arrM[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo (lo + (i - margin))
          (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (i - margin)))
          (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (i - margin)))) else none) :
    uLevel2Body margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros xe xo ye yo dm lo w hc =
      ⟨lo, w, pushZeros margin arrM, pushZeros margin arrX, pushZeros margin arrY⟩ := by
  obtain ⟨hcw, hcm, hcs, hco, cxe, cxo, cye, cyo, cdm⟩ := hc
  unfold uLevel2Body
  simp only
  have hspec := uFillGo2_spec xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 (UInt32.ofNatLT w hcw)
    (srcArr zeros xe (·.xf)) (srcArr zeros xo (·.mf)) (srcArr zeros ye (·.yf))
    (srcArr zeros yo (·.mf)) (srcArr zeros dm (·.mf))
    (UInt32.ofNatLT (srcBase margin lo xe - 1) cxe.2.2.2) (UInt32.ofNatLT (srcBase margin lo xo - 1) cxo.2.2.2)
    (UInt32.ofNatLT (srcBase margin lo ye + 1) cye.2.2.2) (UInt32.ofNatLT (srcBase margin lo yo + 1) cyo.2.2.2)
    (UInt32.ofNatLT (srcBase margin lo dm) cdm.2.2.2) (UInt32.ofNatLT margin hcm) (w + 2 * margin)
    (by simp only [UInt32.toNat_ofNatLT]; exact cxe.2.1) cxe.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact cxo.2.1) cxo.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact cye.2.1) cye.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact cyo.2.1) cyo.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact cdm.2.1) cdm.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hco) hcs
    0 lo.toUInt32 (Array.replicate (w + 2 * margin) 0) (Array.replicate (w + 2 * margin) 0)
    (Array.replicate (w + 2 * margin) 0)
    Array.size_replicate Array.size_replicate Array.size_replicate
  simp only at hspec
  obtain ⟨s1, s2, s3, fx, fy, fm⟩ := hspec
  simp only [UInt32.toNat_ofNatLT, UInt32.toNat_zero, Nat.add_zero, UInt32.sub_zero] at fx fy fm
  -- the cell equality on every band index
  have cellsX : ∀ j, margin ≤ j → j < margin + w →
      cellX2 m.toUInt32 n.toUInt32 (srcArr zeros xe (·.xf)) (srcArr zeros xo (·.mf))
        (UInt32.ofNatLT (srcBase margin lo xe - 1) cxe.2.2.2) (UInt32.ofNatLT (srcBase margin lo xo - 1) cxo.2.2.2)
        (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32) =
      cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (j - margin)) := by
    intro j hj1 hj2
    rw [toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellX2_eq m n margin zeros xe xo wxe wxo hz lo (j - margin) hb (by omega)
      (srcOK_mono margin zeros lo w _ xe _ _ cxe (by omega)) (srcOK_mono margin zeros lo w _ xo _ _ cxo (by omega))
  have cellsY : ∀ j, margin ≤ j → j < margin + w →
      cellY2 m.toUInt32 len.toUInt32 (srcArr zeros ye (·.yf)) (srcArr zeros yo (·.mf))
        (UInt32.ofNatLT (srcBase margin lo ye + 1) cye.2.2.2) (UInt32.ofNatLT (srcBase margin lo yo + 1) cyo.2.2.2)
        (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32) =
      cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (j - margin)) := by
    intro j hj1 hj2
    rw [toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellY2_eq m n len margin zeros ye yo wye wyo hz lo (j - margin) hb hlen (by omega)
      (srcOK_mono margin zeros lo w _ ye _ _ cye (by omega)) (srcOK_mono margin zeros lo w _ yo _ _ cyo (by omega))
  have cellsM : ∀ j, margin ≤ j → j < margin + w →
      cellM2 m.toUInt32 n.toUInt32 xa ya hm32 hn32 (srcArr zeros dm (·.mf))
        (UInt32.ofNatLT (srcBase margin lo dm) cdm.2.2.2) (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32)
        (cellX2 m.toUInt32 n.toUInt32 (srcArr zeros xe (·.xf)) (srcArr zeros xo (·.mf))
          (UInt32.ofNatLT (srcBase margin lo xe - 1) cxe.2.2.2) (UInt32.ofNatLT (srcBase margin lo xo - 1) cxo.2.2.2)
          (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32))
        (cellY2 m.toUInt32 len.toUInt32 (srcArr zeros ye (·.yf)) (srcArr zeros yo (·.mf))
          (UInt32.ofNatLT (srcBase margin lo ye + 1) cye.2.2.2) (UInt32.ofNatLT (srcBase margin lo yo + 1) cyo.2.2.2)
          (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32)) =
      cellM m.toUInt32 n.toUInt32 xa ya margin dm.mf dm.lo (lo + (j - margin))
        (cellX m.toUInt32 n.toUInt32 margin xe.xf xo.mf xe.lo xo.lo (lo + (j - margin)))
        (cellY m.toUInt32 len margin ye.yf yo.mf ye.lo yo.lo (lo + (j - margin))) := by
    intro j hj1 hj2
    rw [cellsX j hj1 hj2, cellsY j hj1 hj2, toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellM2_eq m n margin xa ya zeros dm wdm hz lo (j - margin) hb (by omega) hxa hm32 hn32
      (srcOK_mono margin zeros lo w _ dm _ _ cdm (by omega)) _ _
      (cellX_le m n margin xe xo wxe wxo hm hb _ (by omega))
      (cellY_le m n len margin ye yo wye wyo hm hb hlen _)
  congr 1
  · apply arr_ext?
    intro j
    rw [fm j, pushZeros_getElem?, sm, gm j]
    by_cases j1 : j < margin
    · rw [if_neg (by omega), if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
    · by_cases j2 : j < margin + w
      · rw [if_pos ⟨by omega, j2⟩, if_pos j2, if_neg j1, if_pos j2, cellsM j (by omega) j2]
      · rw [if_neg (by omega), if_neg j2, Array.getElem?_replicate]
        by_cases j3 : j < margin + w + margin
        · rw [if_pos j3, if_pos (by omega)]
        · rw [if_neg j3, if_neg (by omega)]
  · apply arr_ext?
    intro j
    rw [fx j, pushZeros_getElem?, sx, gx j]
    by_cases j1 : j < margin
    · rw [if_neg (by omega), if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
    · by_cases j2 : j < margin + w
      · rw [if_pos ⟨by omega, j2⟩, if_pos j2, if_neg j1, if_pos j2, cellsX j (by omega) j2]
      · rw [if_neg (by omega), if_neg j2, Array.getElem?_replicate]
        by_cases j3 : j < margin + w + margin
        · rw [if_pos j3, if_pos (by omega)]
        · rw [if_neg j3, if_neg (by omega)]
  · apply arr_ext?
    intro j
    rw [fy j, pushZeros_getElem?, sy, gy j]
    by_cases j1 : j < margin
    · rw [if_neg (by omega), if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
    · by_cases j2 : j < margin + w
      · rw [if_pos ⟨by omega, j2⟩, if_pos j2, if_neg j1, if_pos j2, cellsY j (by omega) j2]
      · rw [if_neg (by omega), if_neg j2, Array.getElem?_replicate]
        by_cases j3 : j < margin + w + margin
        · rw [if_pos j3, if_pos (by omega)]
        · rw [if_neg j3, if_neg (by omega)]

/-- Main theorem: a level returned by the hot-loop builder from well-formed
sources is the level of the proven builder. -/
theorem uLevel2_some (wxe : WF m margin xe) (wxo : WF m margin xo) (wye : WF m margin ye)
    (wyo : WF m margin yo) (wdm : WF m margin dm)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size) (lv : ULevel)
    (h : uLevel2 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 xe xo ye yo dm = some lv) :
    lv = uLevel m n len margin xa ya xe xo ye yo dm := by
  unfold uLevel2 at h
  dsimp only at h
  by_cases hne : min (uBandHi xe xo ye yo dm) len ≤ uBandLo len xe xo ye yo dm
  · rw [if_pos hne] at h
    rw [uLevel_empty m n len margin xa ya xe xo ye yo dm hne]
    exact (Option.some.inj h).symm
  · rw [if_neg hne] at h
    obtain ⟨hlo, hw, arrX, arrY, arrM, hxf, hyf, hmf, sx, sy, sm, gx, gy, gm⟩ :=
      uLevel_fronts m n len margin xa ya xe xo ye yo dm hne
    -- the zero array of this level
    generalize hzd : (if (decide (xe.w = 0) || decide (xo.w = 0) || decide (ye.w = 0) || decide (yo.w = 0)
        || decide (dm.w = 0)) = true then
        Array.replicate (min (uBandHi xe xo ye yo dm) len - uBandLo len xe xo ye yo dm + 2 * margin + 2) (0 : UInt32)
        else #[]) = zeros at h
    have hz : ∀ i, zeros.getD i 0 = 0 := by
      intro i; rw [← hzd]; split
      · exact replicate_getD _ i
      · rfl
    split at h
    · rename_i hc
      rw [uLevel2Body_eq m n len margin xa ya zeros xe xo ye yo dm wxe wxo wye wyo wdm hz hm hb hlen hxa
        hm32 hn32 _ _ (levelCheckB_true _ _ _ _ _ _ _ _ _ hc) (by omega) arrX arrY arrM sx sy sm gx gy gm] at h
      cases hU : uLevel m n len margin xa ya xe xo ye yo dm with
      | mk lo' w' mf' xf' yf' =>
        rw [hU] at hlo hw hxf hyf hmf
        simp only at hlo hw hxf hyf hmf
        subst hlo hw hxf hyf hmf
        exact (Option.some.inj h).symm
    · cases h

end Level2

end AlignmentSpec.U32Proof
#print axioms AlignmentSpec.U32Proof.uLevel2_some
