import AlignmentWfaU32Fill3
import AlignmentWfaU32FillSpec3
import AlignmentWfaU32Level2
import AlignmentWfaU32Loop3

/-! Refinement of the block-layout builder to the proved three-front builder. -/
namespace AlignmentSpec.U32Proof

/-- Proof-only layout invariant; no extra runtime checks. -/
structure BWF (m margin : Nat) (s : BLevel) : Prop where
  view : WF m margin (toU margin s)
  size : s.w ≠ 0 → s.blk.size = 3 * (s.w + 2 * margin)
  empty : s.w = 0 → s.blk = #[]

theorem bwf_empty (m margin : Nat) : BWF m margin bEmpty := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toU_bEmpty]; exact wf_uEmpty m margin
  · intro h; exact False.elim (h rfl)
  · intro _; rfl

theorem blockOf_getD (margin b : Nat) (s : BLevel)
    (hsz : s.blk.size = 3 * (s.w + 2 * margin)) (hb : b < 3)
    (i : Nat) (hi : i < s.w + 2 * margin) :
    (blockOf margin b s).getD i 0 = s.blk.getD (b * (s.w + 2 * margin) + i) 0 := by
  simp only [Array.getD_eq_getD_getElem?, blockOf_getElem? margin b s hsz hb i, if_pos hi]

/-- A checked block read is exactly the read of its extracted front. -/
theorem read3_view (m margin lo k t b sh : Nat) (zeros : Array UInt32)
    (hz : ∀ i, zeros.getD i 0 = 0) (s : BLevel) (hs : BWF m margin s)
    (hb : b < 3) (hw : WFA m margin s.w (blockOf margin b s))
    (hc : SrcOK3 margin lo (k + 1) zeros s b sh)
    (he : s.w ≠ 0 → k + sh = b * (s.w + 2 * margin) + (t + margin - s.lo)) :
    (srcArr3 zeros s).getD (k.toUInt32 + UInt32.ofNatLT sh hc.2.2.2.2).toNat 0 =
      ugetA margin s.lo (blockOf margin b s) t := by
  rw [read_index k sh (by have := hc.2.1; have := hc.2.2.1; have := hc.2.2.2.1; omega)]
  unfold srcArr3 ugetA
  by_cases h0 : s.w = 0
  · rw [if_pos h0, hz]
    exact (wfa_empty_getD m margin _ (h0 ▸ hw) _).symm
  · rw [if_neg h0, he h0]
    symm
    apply blockOf_getD margin b s (hs.size h0) hb
    have hbound := hc.2.1
    simp only [srcEnd3, if_neg h0, Nat.add_mul, Nat.one_mul] at hbound
    have := he h0
    omega

theorem read_X3 (m margin lo k b : Nat) (zeros : Array UInt32)
    (hz : ∀ i, zeros.getD i 0 = 0) (s : BLevel) (hs : BWF m margin s)
    (hb : b < 3) (hw : WFA m margin s.w (blockOf margin b s)) (hk : 1 ≤ lo + k)
    (hc : SrcOK3 margin lo (k + 1) zeros s b (srcSh3 margin lo b s - 1)) :
    (srcArr3 zeros s).getD (k.toUInt32 + UInt32.ofNatLT (srcSh3 margin lo b s - 1) hc.2.2.2.2).toNat 0 =
      ugetA margin s.lo (blockOf margin b s) (lo + k - 1) := by
  apply read3_view m margin lo k _ b _ zeros hz s hs hb hw hc
  intro h0
  have := hc.1 (Nat.pos_of_ne_zero h0)
  simp only [srcSh3, if_neg h0]
  omega

theorem read_Y3 (m margin lo k b : Nat) (zeros : Array UInt32)
    (hz : ∀ i, zeros.getD i 0 = 0) (s : BLevel) (hs : BWF m margin s)
    (hb : b < 3) (hw : WFA m margin s.w (blockOf margin b s))
    (hc : SrcOK3 margin lo (k + 1) zeros s b (srcSh3 margin lo b s + 1)) :
    (srcArr3 zeros s).getD (k.toUInt32 + UInt32.ofNatLT (srcSh3 margin lo b s + 1) hc.2.2.2.2).toNat 0 =
      ugetA margin s.lo (blockOf margin b s) (lo + k + 1) := by
  apply read3_view m margin lo k _ b _ zeros hz s hs hb hw hc
  intro h0
  have := hc.1 (Nat.pos_of_ne_zero h0)
  simp only [srcSh3, if_neg h0]
  omega

theorem read_D3 (m margin lo k b : Nat) (zeros : Array UInt32)
    (hz : ∀ i, zeros.getD i 0 = 0) (s : BLevel) (hs : BWF m margin s)
    (hb : b < 3) (hw : WFA m margin s.w (blockOf margin b s))
    (hc : SrcOK3 margin lo (k + 1) zeros s b (srcSh3 margin lo b s)) :
    (srcArr3 zeros s).getD (k.toUInt32 + UInt32.ofNatLT (srcSh3 margin lo b s) hc.2.2.2.2).toNat 0 =
      ugetA margin s.lo (blockOf margin b s) (lo + k) := by
  apply read3_view m margin lo k _ b _ zeros hz s hs hb hw hc
  intro h0
  have := hc.1 (Nat.pos_of_ne_zero h0)
  simp only [srcSh3, if_neg h0]
  omega

theorem srcOK3_mono (margin lo w k : Nat) (zeros : Array UInt32) (s : BLevel) (b sh : Nat)
    (h : SrcOK3 margin lo w zeros s b sh) (hk : k < w) :
    SrcOK3 margin lo (k + 1) zeros s b sh :=
  ⟨h.1, by have := h.2.1; omega, h.2.2⟩

section Cells
variable (m n len margin : Nat) (xa ya : Array Char) (zeros : Array UInt32) (xe xo ye yo dm : BLevel)

theorem cellX3_eq (wxe : BWF m margin xe) (wxo : BWF m margin xo)
    (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat) (ht : lo + k < 2 ^ 30)
    (hxe : SrcOK3 margin lo (k + 1) zeros xe 1 (srcSh3 margin lo 1 xe - 1))
    (hxo : SrcOK3 margin lo (k + 1) zeros xo 0 (srcSh3 margin lo 0 xo - 1)) :
    cellX2 m.toUInt32 n.toUInt32 (srcArr3 zeros xe) (srcArr3 zeros xo)
        (UInt32.ofNatLT (srcSh3 margin lo 1 xe - 1) hxe.2.2.2.2)
        (UInt32.ofNatLT (srcSh3 margin lo 0 xo - 1) hxo.2.2.2.2) k.toUInt32 (lo + k).toUInt32 =
      cellX m.toUInt32 n.toUInt32 margin (toU margin xe).xf (toU margin xo).mf xe.lo xo.lo (lo + k) := by
  unfold cellX2 cellX
  by_cases h0 : lo + k = 0
  · rw [if_pos ((toUInt32_eq_zero_iff _ ht).mpr h0), if_pos h0]
  · rw [if_neg (fun h => h0 ((toUInt32_eq_zero_iff _ ht).mp h)), if_neg h0, toUInt32_pred _ ht h0]
    rw [read_X3 m margin lo k 1 zeros hz xe wxe (by omega) wxe.view.xf (by omega) hxe,
      read_X3 m margin lo k 0 zeros hz xo wxo (by omega) wxo.view.mf (by omega) hxo]
    rfl

theorem cellY3_eq (wye : BWF m margin ye) (wyo : BWF m margin yo)
    (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat) (hb : m + n + 2 < 2 ^ 30)
    (hlen : len ≤ m + n + 1) (ht : lo + k + 1 < 2 ^ 30)
    (hye : SrcOK3 margin lo (k + 1) zeros ye 2 (srcSh3 margin lo 2 ye + 1))
    (hyo : SrcOK3 margin lo (k + 1) zeros yo 0 (srcSh3 margin lo 0 yo + 1)) :
    cellY2 m.toUInt32 len.toUInt32 (srcArr3 zeros ye) (srcArr3 zeros yo)
        (UInt32.ofNatLT (srcSh3 margin lo 2 ye + 1) hye.2.2.2.2)
        (UInt32.ofNatLT (srcSh3 margin lo 0 yo + 1) hyo.2.2.2.2) k.toUInt32 (lo + k).toUInt32 =
      cellY m.toUInt32 len margin (toU margin ye).yf (toU margin yo).mf ye.lo yo.lo (lo + k) := by
  unfold cellY2 cellY
  have hs : (lo + k).toUInt32 + 1 = (lo + k + 1).toUInt32 := toUInt32_add_of_lt (lo + k) 1 (by omega)
  rw [hs]
  by_cases h0 : lo + k + 1 < len
  · rw [if_pos ((toUInt32_lt_iff _ _ (by omega) (by omega)).mpr h0), if_pos h0]
    rw [read_Y3 m margin lo k 2 zeros hz ye wye (by omega) wye.view.yf hye,
      read_Y3 m margin lo k 0 zeros hz yo wyo (by omega) wyo.view.mf hyo]
    rfl
  · rw [if_neg (fun h => h0 ((toUInt32_lt_iff _ _ (by omega) (by omega)).mp h)), if_neg h0]

theorem cellM3_eq (wdm : BWF m margin dm) (hz : ∀ i, zeros.getD i 0 = 0) (lo k : Nat)
    (hb : m + n + 2 < 2 ^ 30) (ht : lo + k < 2 ^ 30)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size)
    (hdm : SrcOK3 margin lo (k + 1) zeros dm 0 (srcSh3 margin lo 0 dm))
    (x y : UInt32) (hx : x.toNat ≤ m + 1) (hy : y.toNat ≤ m + 1) :
    cellM2 m.toUInt32 n.toUInt32 xa ya hm32 hn32 (srcArr3 zeros dm)
        (UInt32.ofNatLT (srcSh3 margin lo 0 dm) hdm.2.2.2.2) k.toUInt32 (lo + k).toUInt32 x y =
      cellM m.toUInt32 n.toUInt32 xa ya margin (toU margin dm).mf dm.lo (lo + k) x y := by
  unfold cellM2 cellM
  rw [read_D3 m margin lo k 0 zeros hz dm wdm (by omega) wdm.view.mf hdm]
  apply uext2_eq
  have hmN := toNat_toUInt32_of_lt m (by omega)
  have hnN := toNat_toUInt32_of_lt n (by omega)
  have htN := toNat_toUInt32_of_lt (lo + k) ht
  have bdm := ugetA_bound m margin dm.lo dm.w (blockOf margin 0 dm) wdm.view.mf (lo + k)
  have hd : (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32
      (ugetA margin dm.lo (blockOf margin 0 dm) (lo + k))).toNat ≤ m + 1 := by
    rw [upushD_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩, hmN, hnN, htN]
    exact pushDR_le m n _ _ bdm
  have hb1 : (ubetter (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32
      (ugetA margin dm.lo (blockOf margin 0 dm) (lo + k))) x).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hd hx
  have hb2 : (ubetter (ubetter (upushD m.toUInt32 n.toUInt32 (lo + k).toUInt32
      (ugetA margin dm.lo (blockOf margin 0 dm) (lo + k))) x) y).toNat ≤ m + 1 := by
    rw [ubetter_toNat]; exact betterR_le m _ _ hb1 hy
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem uLevel3Body_eq (wxe : BWF m margin xe) (wxo : BWF m margin xo) (wye : BWF m margin ye)
    (wyo : BWF m margin yo) (wdm : BWF m margin dm) (hz : ∀ i, zeros.getD i 0 = 0)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size)
    (lo w : Nat) (hc : LevelCheck3 margin lo w zeros xe xo ye yo dm) (hlolen : lo + w ≤ len)
    (arrX arrY arrM : Array UInt32)
    (sx : arrX.size = margin + w) (sy : arrY.size = margin + w) (sm : arrM.size = margin + w)
    (gx : ∀ i, arrX[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellX m.toUInt32 n.toUInt32 margin (toU margin xe).xf (toU margin xo).mf xe.lo xo.lo (lo + (i - margin))) else none)
    (gy : ∀ i, arrY[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellY m.toUInt32 len margin (toU margin ye).yf (toU margin yo).mf ye.lo yo.lo (lo + (i - margin))) else none)
    (gm : ∀ i, arrM[i]? = if i < margin then some 0 else if i < margin + w then
        some (cellM m.toUInt32 n.toUInt32 xa ya margin (toU margin dm).mf dm.lo (lo + (i - margin))
          (cellX m.toUInt32 n.toUInt32 margin (toU margin xe).xf (toU margin xo).mf xe.lo xo.lo (lo + (i - margin)))
          (cellY m.toUInt32 len margin (toU margin ye).yf (toU margin yo).mf ye.lo yo.lo (lo + (i - margin)))) else none) :
    toU margin (uLevel3Body margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros xe xo ye yo dm lo w hc) =
      ⟨lo, w, pushZeros margin arrM, pushZeros margin arrX, pushZeros margin arrY⟩ ∧
    (uLevel3Body margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros xe xo ye yo dm lo w hc).blk.size =
      3 * (w + 2 * margin) := by
  obtain ⟨hcw, hcm, hcs, hM, hX, hY, hX32, hY32, cxe, cxo, cye, cyo, cdm⟩ := hc
  unfold uLevel3Body
  simp only
  have hspec := uFillGo3_spec xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 (UInt32.ofNatLT w hcw)
    (srcArr3 zeros xe) (srcArr3 zeros xo) (srcArr3 zeros ye)
    (srcArr3 zeros yo) (srcArr3 zeros dm)
    (UInt32.ofNatLT (srcSh3 margin lo 1 xe - 1) cxe.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 xo - 1) cxo.2.2.2.2)
    (UInt32.ofNatLT (srcSh3 margin lo 2 ye + 1) cye.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 yo + 1) cyo.2.2.2.2)
    (UInt32.ofNatLT (srcSh3 margin lo 0 dm) cdm.2.2.2.2) (UInt32.ofNatLT margin hcm)
    (UInt32.ofNatLT (margin + (w + 2 * margin)) hX32)
    (UInt32.ofNatLT (margin + 2 * (w + 2 * margin)) hY32) (3 * (w + 2 * margin))
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans cxe.2.1 cxe.2.2.1) cxe.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans cxo.2.1 cxo.2.2.1) cxo.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans cye.2.1 cye.2.2.1) cye.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans cyo.2.1 cyo.2.2.1) cyo.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact Nat.le_trans cdm.2.1 cdm.2.2.1) cdm.2.2.2.1
    (by simp only [UInt32.toNat_ofNatLT]; exact hM)
    (by simp only [UInt32.toNat_ofNatLT]; exact hX)
    (by simp only [UInt32.toNat_ofNatLT]; exact hY) hcs
    (by simp only [UInt32.toNat_ofNatLT]; omega)
    (by simp only [UInt32.toNat_ofNatLT]; omega)
    0 lo.toUInt32 (Array.replicate (3 * (w + 2 * margin)) 0) Array.size_replicate
  simp only at hspec
  obtain ⟨sf, ff⟩ := hspec
  simp only [UInt32.toNat_ofNatLT, UInt32.toNat_zero, Nat.add_zero, UInt32.sub_zero] at ff
  -- the cell equality on every band index
  have cellsX : ∀ j, margin ≤ j → j < margin + w →
      cellX2 m.toUInt32 n.toUInt32 (srcArr3 zeros xe) (srcArr3 zeros xo)
        (UInt32.ofNatLT (srcSh3 margin lo 1 xe - 1) cxe.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 xo - 1) cxo.2.2.2.2)
        (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32) =
      cellX m.toUInt32 n.toUInt32 margin (toU margin xe).xf (toU margin xo).mf xe.lo xo.lo (lo + (j - margin)) := by
    intro j hj1 hj2
    rw [toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellX3_eq m n margin zeros xe xo wxe wxo hz lo (j - margin) (by omega)
      (srcOK3_mono margin lo w _ zeros xe 1 _ cxe (by omega)) (srcOK3_mono margin lo w _ zeros xo 0 _ cxo (by omega))
  have cellsY : ∀ j, margin ≤ j → j < margin + w →
      cellY2 m.toUInt32 len.toUInt32 (srcArr3 zeros ye) (srcArr3 zeros yo)
        (UInt32.ofNatLT (srcSh3 margin lo 2 ye + 1) cye.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 yo + 1) cyo.2.2.2.2)
        (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32) =
      cellY m.toUInt32 len margin (toU margin ye).yf (toU margin yo).mf ye.lo yo.lo (lo + (j - margin)) := by
    intro j hj1 hj2
    rw [toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellY3_eq m n len margin zeros ye yo wye wyo hz lo (j - margin) hb hlen (by omega)
      (srcOK3_mono margin lo w _ zeros ye 2 _ cye (by omega)) (srcOK3_mono margin lo w _ zeros yo 0 _ cyo (by omega))
  have cellsM : ∀ j, margin ≤ j → j < margin + w →
      cellM2 m.toUInt32 n.toUInt32 xa ya hm32 hn32 (srcArr3 zeros dm)
        (UInt32.ofNatLT (srcSh3 margin lo 0 dm) cdm.2.2.2.2) (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32)
        (cellX2 m.toUInt32 n.toUInt32 (srcArr3 zeros xe) (srcArr3 zeros xo)
          (UInt32.ofNatLT (srcSh3 margin lo 1 xe - 1) cxe.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 xo - 1) cxo.2.2.2.2)
          (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32))
        (cellY2 m.toUInt32 len.toUInt32 (srcArr3 zeros ye) (srcArr3 zeros yo)
          (UInt32.ofNatLT (srcSh3 margin lo 2 ye + 1) cye.2.2.2.2) (UInt32.ofNatLT (srcSh3 margin lo 0 yo + 1) cyo.2.2.2.2)
          (j - margin).toUInt32 (lo.toUInt32 + (j - margin).toUInt32)) =
      cellM m.toUInt32 n.toUInt32 xa ya margin (toU margin dm).mf dm.lo (lo + (j - margin))
        (cellX m.toUInt32 n.toUInt32 margin (toU margin xe).xf (toU margin xo).mf xe.lo xo.lo (lo + (j - margin)))
        (cellY m.toUInt32 len margin (toU margin ye).yf (toU margin yo).mf ye.lo yo.lo (lo + (j - margin))) := by
    intro j hj1 hj2
    rw [cellsX j hj1 hj2, cellsY j hj1 hj2, toUInt32_add_of_lt lo (j - margin) (by omega)]
    exact cellM3_eq m n margin xa ya zeros dm wdm hz lo (j - margin) hb (by omega) hm32 hn32
      (srcOK3_mono margin lo w _ zeros dm 0 _ cdm (by omega)) _ _
      (cellX_le m n margin (toU margin xe) (toU margin xo) wxe.view wxo.view hm hb _ (by omega))
      (cellY_le m n len margin (toU margin ye) (toU margin yo) wye.view wyo.view hm hb hlen _)
  refine ⟨?_, sf⟩
  unfold toU
  congr 1
  · apply arr_ext?
    intro j
    rw [blockOf_getElem? margin 0 _ sf (by omega) j]
    dsimp only
    by_cases hj : j < w + 2 * margin
    · rw [if_pos hj, ff, pushZeros_getElem?, sm, gm j]
      simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      by_cases j1 : j < margin
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
      · by_cases j2 : j < margin + w
        · rw [if_pos (by omega)]
          rw [if_pos j2, if_neg j1, if_pos j2, cellsM j (by omega) j2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg j2,
            if_pos (by omega), Array.getElem?_replicate, if_pos (by omega)]
    · rw [if_neg hj, Array.getElem?_eq_none (by rw [pushZeros_size, sm]; omega)]
  · apply arr_ext?
    intro j
    rw [blockOf_getElem? margin 1 _ sf (by omega) j]
    dsimp only
    by_cases hj : j < w + 2 * margin
    · rw [if_pos hj, ff, pushZeros_getElem?, sx, gx j]
      simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      by_cases j1 : j < margin
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
      · by_cases j2 : j < margin + w
        · rw [if_neg (by omega)]
          rw [if_pos (by omega)]
          have he : ((w + 2 * margin) + j) - (margin + (w + 2 * margin)) = j - margin := by omega
          rw [he]
          rw [if_pos j2, if_neg j1, if_pos j2, cellsX j (by omega) j2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg j2,
            if_pos (by omega), Array.getElem?_replicate, if_pos (by omega)]
    · rw [if_neg hj, Array.getElem?_eq_none (by rw [pushZeros_size, sx]; omega)]
  · apply arr_ext?
    intro j
    rw [blockOf_getElem? margin 2 _ sf (by omega) j]
    dsimp only
    by_cases hj : j < w + 2 * margin
    · rw [if_pos hj, ff, pushZeros_getElem?, sy, gy j]
      by_cases j1 : j < margin
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), if_pos j1, Array.getElem?_replicate, if_pos (by omega)]
      · by_cases j2 : j < margin + w
        · rw [if_neg (by omega)]
          rw [if_neg (by omega)]
          rw [if_pos (by omega)]
          have he : (2 * (w + 2 * margin) + j) - (margin + 2 * (w + 2 * margin)) = j - margin := by omega
          rw [he]
          rw [if_pos j2, if_neg j1, if_pos j2, cellsY j (by omega) j2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg j2,
            if_pos (by omega), Array.getElem?_replicate, if_pos (by omega)]
    · rw [if_neg hj, Array.getElem?_eq_none (by rw [pushZeros_size, sy]; omega)]

theorem uBandLo3_eq : uBandLo3 len xe xo ye yo dm =
    uBandLo len (toU margin xe) (toU margin xo) (toU margin ye) (toU margin yo) (toU margin dm) := rfl

theorem uBandHi3_eq : uBandHi3 xe xo ye yo dm =
    uBandHi (toU margin xe) (toU margin xo) (toU margin ye) (toU margin yo) (toU margin dm) := rfl

/-- A successfully built block level views to the proved builder's exact
arrays and preserves the block-layout invariant. -/
theorem uLevel3_some (wxe : BWF m margin xe) (wxo : BWF m margin xo) (wye : BWF m margin ye)
    (wyo : BWF m margin yo) (wdm : BWF m margin dm) (hz : ∀ i, zeros.getD i 0 = 0)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size) (lv : BLevel)
    (h : uLevel3 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros xe xo ye yo dm = some lv) :
    toU margin lv = uLevel m n len margin xa ya (toU margin xe) (toU margin xo)
      (toU margin ye) (toU margin yo) (toU margin dm) ∧ BWF m margin lv := by
  have wf := wf_uLevel m n len margin xa ya (toU margin xe) (toU margin xo)
    (toU margin ye) (toU margin yo) (toU margin dm) wxe.view wxo.view wye.view wyo.view wdm.view
    hm hb hlen hxa
  unfold uLevel3 at h
  dsimp only at h
  rw [uBandLo3_eq len margin, uBandHi3_eq margin] at h
  by_cases hne : min (uBandHi (toU margin xe) (toU margin xo) (toU margin ye) (toU margin yo) (toU margin dm)) len ≤
      uBandLo len (toU margin xe) (toU margin xo) (toU margin ye) (toU margin yo) (toU margin dm)
  · rw [if_pos hne] at h
    have he := Option.some.inj h
    subst lv
    rw [uLevel_empty m n len margin xa ya _ _ _ _ _ hne, toU_bEmpty]
    exact ⟨rfl, bwf_empty m margin⟩
  · rw [if_neg hne] at h
    obtain ⟨hlo, hw, arrX, arrY, arrM, hxf, hyf, hmf, sx, sy, sm, gx, gy, gm⟩ :=
      uLevel_fronts m n len margin xa ya (toU margin xe) (toU margin xo) (toU margin ye)
        (toU margin yo) (toU margin dm) hne
    split at h
    · rename_i hc
      have he := Option.some.inj h
      subst lv
      obtain ⟨hv, hs⟩ := uLevel3Body_eq m n len margin xa ya zeros xe xo ye yo dm
        wxe wxo wye wyo wdm hz hm hb hlen hxa hm32 hn32 _ _
        (levelCheckB3_true _ _ _ _ _ _ _ _ _ hc) (by omega) arrX arrY arrM sx sy sm gx gy gm
      have eqv : toU margin (uLevel3Body margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros
          xe xo ye yo dm _ _ (levelCheckB3_true _ _ _ _ _ _ _ _ _ hc)) =
          uLevel m n len margin xa ya (toU margin xe) (toU margin xo) (toU margin ye) (toU margin yo) (toU margin dm) := by
        rw [hv]
        cases hU : uLevel m n len margin xa ya (toU margin xe) (toU margin xo)
            (toU margin ye) (toU margin yo) (toU margin dm) with
        | mk lo' w' mf' xf' yf' =>
          rw [hU] at hlo hw hxf hyf hmf
          simp only at hlo hw hxf hyf hmf
          subst hlo hw hxf hyf hmf
          rfl
      refine ⟨eqv, ⟨eqv.symm ▸ wf, fun _ => hs, ?_⟩⟩
      intro h0
      change min _ len - _ = 0 at h0
      omega
    · cases h

end Cells
#print axioms uLevel3_some
end AlignmentSpec.U32Proof
