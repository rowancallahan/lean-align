import AlignmentWfaU32FillS
import AlignmentWfaU32FillSSpec
import AlignmentWfaU32Single
import AlignmentWfaU32Level2

/-!
# The single-source level denotes `nextLevelR`'s M front

With all penalties 1 the only source of a level is the previous level, and
by the invariant X ≤ M, Y ≤ M (AlignmentWfaU32Single.lean) the X and Y points
of `nextLevelR` are pushes of the previous M front alone (`pointX_single`,
`pointY_single`).  `uLevelS_some`: the M front the one-read-per-cell loop
builds reads, on every diagonal below `len`, exactly `rget` of the M front
`nextLevelR m n xa ya len 1 1 1 [R]` builds from any `R` whose M front reads
as the source's and which satisfies the invariant; and it is well-formed.
-/
namespace AlignmentSpec.U32Proof

/-- The value of an M cell from the previous M front `f` alone. -/
def modelCellS (m n len : Nat) (xa ya : Array Char) (f : Nat → Nat) (t : Nat) : Nat :=
  extR m xa ya t (betterR (betterR (pushDR m n t (f t))
    (if t = 0 then 0 else pushXR m n (t - 1) (f (t - 1))))
    (if t + 1 < len then pushYR m n (t + 1) (f (t + 1)) else 0))

theorem modelCellS_congr (m n len : Nat) (xa ya : Array Char) (f g : Nat → Nat) (t : Nat)
    (h0 : f t = g t) (h1 : t ≠ 0 → f (t - 1) = g (t - 1)) (h2 : t + 1 < len → f (t + 1) = g (t + 1)) :
    modelCellS m n len xa ya f t = modelCellS m n len xa ya g t := by
  unfold modelCellS
  rw [h0]
  by_cases ht : t = 0
  · rw [if_pos ht, if_pos ht]
    by_cases hl : t + 1 < len
    · rw [if_pos hl, if_pos hl, h2 hl]
    · rw [if_neg hl, if_neg hl]
  · rw [if_neg ht, if_neg ht, h1 ht]
    by_cases hl : t + 1 < len
    · rw [if_pos hl, if_pos hl, h2 hl]
    · rw [if_neg hl, if_neg hl]

theorem modelCellS_zero (m n len : Nat) (xa ya : Array Char) (f : Nat → Nat) (t : Nat)
    (h0 : f t = 0) (h1 : f (t - 1) = 0) (h2 : f (t + 1) = 0) :
    modelCellS m n len xa ya f t = 0 := by
  unfold modelCellS
  rw [h0, h1, h2]
  have hx : pushXR m n (t - 1) 0 = 0 := by unfold pushXR; rfl
  have hy : pushYR m n (t + 1) 0 = 0 := by unfold pushYR; rfl
  have hd : pushDR m n t 0 = 0 := by unfold pushDR; rfl
  rw [hx, hy, hd]
  have hb : betterR (betterR 0 (if t = 0 then 0 else 0)) (if t + 1 < len then 0 else 0) = 0 := by
    split <;> split <;> rfl
  rw [hb]
  unfold extR; rfl

theorem modelCellS_le (m n len : Nat) (xa ya : Array Char) (hxa : xa.size = m) (f : Nat → Nat)
    (hf : ∀ t, f t ≤ m + 1) (t : Nat) : modelCellS m n len xa ya f t ≤ m + 1 := by
  unfold modelCellS
  apply extR_le m xa ya hxa
  apply betterR_le
  · apply betterR_le
    · exact pushDR_le m n t _ (hf t)
    · split
      · omega
      · exact pushXR_le m n _ _ (hf _)
  · split
    · exact pushYR_le m n _ _ (hf _)
    · omega

/-- `nextLevelR` with the single source `R`: its M front is `modelCellS` of `R`'s M front. -/
theorem rget_nextLevelR_single (m n len : Nat) (xa ya : Array Char) (R : RLevel)
    (hinv : ∀ t, rget R.xf t ≤ rget R.mf t ∧ rget R.yf t ≤ rget R.mf t) (t : Nat) :
    rget (nextLevelR m n xa ya len 1 1 1 [R]).mf t =
      modelCellS m n len xa ya (fun t' => rget R.mf t') t := by
  rw [← nextLevelP_eq, rget_nextLevelP_mf]
  have hX : rget (nextLevelP m n xa ya len 1 1 1 [R]).xf t =
      pointX m n (frontAtR [R] 1 (·.xf)) (frontAtR [R] 1 (·.mf)) t := by
    simp only [nextLevelP, packPointX_eq]
    rw [← pointX_eq]
  have hY : rget (nextLevelP m n xa ya len 1 1 1 [R]).yf t =
      pointY m n len (frontAtR [R] 1 (·.yf)) (frontAtR [R] 1 (·.mf)) t := by
    simp only [nextLevelP, packPointY_eq]
    rw [← pointY_eq]
  have hF : ∀ sel : RLevel → RFront, frontAtR [R] 1 sel = sel R := by
    intro sel; rfl
  unfold pointM
  rw [hX, hY, hF, hF, hF, pointX_single m n R.xf R.mf (fun t => (hinv t).1),
    pointY_single m n len R.yf R.mf (fun t => (hinv t).2)]
  rfl

theorem wfa_getD_le (m margin w : Nat) (f : Array UInt32) (h : WFA m margin w f) (idx : Nat) :
    (f.getD idx 0).toNat ≤ m + 1 := by
  rw [Array.getD_eq_getD_getElem?]
  cases hi : f[idx]? with
  | none => simp
  | some v =>
    have hlt : idx < f.size := by
      rcases Nat.lt_or_ge idx f.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hi; cases hi
    have hv : f[idx] = v := by rw [Array.getElem?_eq_getElem hlt] at hi; cases hi; rfl
    simp only [Option.getD_some]
    rw [← hv]
    exact h.bound idx hlt

/-- The single-source cell on codes. -/
theorem uCellS_toNat (m n len : Nat) (xa ya : Array Char) (hm32 : m.toUInt32.toNat = xa.size)
    (hn32 : n.toUInt32.toNat = ya.size) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1)
    (hxa : xa.size = m) (t : Nat) (ht : t + 1 < 2 ^ 30) (prev cur next : UInt32)
    (hp : prev.toNat ≤ m + 1) (hc : cur.toNat ≤ m + 1) (hnx : next.toNat ≤ m + 1) :
    (uCellS xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 t.toUInt32 prev cur next).toNat =
      extR m xa ya t (betterR (betterR (pushDR m n t cur.toNat)
        (if t = 0 then 0 else pushXR m n (t - 1) prev.toNat))
        (if t + 1 < len then pushYR m n (t + 1) next.toNat else 0)) := by
  unfold uCellS
  have hmN := toNat_toUInt32_of_lt m (by omega)
  have hnN := toNat_toUInt32_of_lt n (by omega)
  have htN := toNat_toUInt32_of_lt t (by omega)
  -- the three pushes
  have hd : (upushD m.toUInt32 n.toUInt32 t.toUInt32 cur).toNat = pushDR m n t cur.toNat := by
    rw [upushD_toNat _ _ _ _ ⟨by omega, by omega, by omega, by omega⟩, hmN, hnN, htN]
  have hx : (if t.toUInt32 = 0 then 0 else upushX m.toUInt32 n.toUInt32 (t.toUInt32 - 1) prev).toNat =
      if t = 0 then 0 else pushXR m n (t - 1) prev.toNat := by
    by_cases h0 : t = 0
    · rw [if_pos ((toUInt32_eq_zero_iff t (by omega)).mpr h0), if_pos h0]; rfl
    · rw [if_neg (fun h => h0 ((toUInt32_eq_zero_iff t (by omega)).mp h)), if_neg h0,
        toUInt32_pred t (by omega) h0,
        upushX_toNat _ _ _ _ ⟨by omega, by omega, by rw [toNat_toUInt32_of_lt (t - 1) (by omega)]; omega, by omega⟩,
        hmN, hnN, toNat_toUInt32_of_lt (t - 1) (by omega)]
  have hy : (if t.toUInt32 + 1 < len.toUInt32 then upushY m.toUInt32 (t.toUInt32 + 1) next else 0).toNat =
      if t + 1 < len then pushYR m n (t + 1) next.toNat else 0 := by
    have hs : t.toUInt32 + 1 = (t + 1).toUInt32 := toUInt32_add_of_lt t 1 (by omega)
    rw [hs]
    by_cases hl : t + 1 < len
    · rw [if_pos ((toUInt32_lt_iff _ _ (by omega) (by omega)).mpr hl), if_pos hl,
        upushY_toNat _ n.toUInt32 _ _ ⟨by omega, by omega, by rw [toNat_toUInt32_of_lt (t + 1) (by omega)]; omega, by omega⟩,
        hmN, hnN, toNat_toUInt32_of_lt (t + 1) (by omega)]
    · rw [if_neg (fun h => hl ((toUInt32_lt_iff _ _ (by omega) (by omega)).mp h)), if_neg hl]; rfl
  -- bounds of the combined code
  have hdl : (upushD m.toUInt32 n.toUInt32 t.toUInt32 cur).toNat ≤ m + 1 := by
    rw [hd]; exact pushDR_le m n t _ hc
  have hxl : (if t.toUInt32 = 0 then 0 else upushX m.toUInt32 n.toUInt32 (t.toUInt32 - 1) prev).toNat ≤ m + 1 := by
    rw [hx]; split
    · omega
    · exact pushXR_le m n _ _ hp
  have hyl : (if t.toUInt32 + 1 < len.toUInt32 then upushY m.toUInt32 (t.toUInt32 + 1) next else 0).toNat ≤ m + 1 := by
    rw [hy]; split
    · exact pushYR_le m n _ _ hnx
    · omega
  have hb1 := betterR_le m _ _ hdl hxl
  rw [← ubetter_toNat] at hb1
  have hb2 := betterR_le m _ _ hb1 hyl
  rw [← ubetter_toNat] at hb2
  rw [uext2_eq _ _ _ _ xa ya hm32 hn32 ⟨by omega, by omega, by omega, by omega⟩,
    uext_toNat _ n.toUInt32 _ _ xa ya ⟨by omega, by omega, by omega, by omega⟩ (by omega),
    hmN, htN, ubetter_toNat, ubetter_toNat, hd, hx, hy]

/-- The value the loop writes for cell `k` of a level starting at `lo`
(source shift `base + 1`, `base = margin + lo - src.lo`) is `modelCellS` of the
source's padded reads at diagonal `lo + k`. -/
theorem cellS_toNat (m n len margin lo k : Nat) (xa ya : Array Char) (src : ULevel)
    (hsrc : WFA m margin src.w src.mf) (hm32 : m.toUInt32.toNat = xa.size)
    (hn32 : n.toUInt32.toNat = ya.size) (hb : m + n + 2 < 2 ^ 30) (hlen : len ≤ m + n + 1)
    (hxa : xa.size = m) (ht : lo + k + 1 < 2 ^ 30) (hbase : src.lo + 1 ≤ margin + lo)
    (hsh : margin + lo - src.lo + 1 < UInt32.size) :
    (cellS xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 src.mf
        (UInt32.ofNatLT (margin + lo - src.lo + 1) hsh) k.toUInt32 (lo + k).toUInt32).toNat =
      modelCellS m n len xa ya (fun t' => (uget margin src (·.mf) t').toNat) (lo + k) := by
  unfold cellS
  rw [UInt32.toNat_ofNatLT, toNat_toUInt32_of_lt k (by omega)]
  rw [uCellS_toNat m n len xa ya hm32 hn32 hb hlen hxa (lo + k) ht _ _ _
    (wfa_getD_le m margin src.w src.mf hsrc _) (wfa_getD_le m margin src.w src.mf hsrc _)
    (wfa_getD_le m margin src.w src.mf hsrc _)]
  unfold modelCellS
  simp only [uget, ugetA]
  have e0 : k + (margin + lo - src.lo + 1) - 1 = lo + k + margin - src.lo := by omega
  have e2 : k + (margin + lo - src.lo + 1) = lo + k + 1 + margin - src.lo := by omega
  by_cases h0 : lo + k = 0
  · rw [if_pos h0, if_pos h0, e0, e2]
  · have e1 : k + (margin + lo - src.lo + 1) - 2 = lo + k - 1 + margin - src.lo := by omega
    rw [if_neg h0, if_neg h0, e1, e0, e2]

section LevelS
variable (m n len margin : Nat) (xa ya : Array Char) (src : ULevel) (R : RLevel)

/-- Every read of an empty source is zero. -/
theorem uget_empty_src (hsrc : WFA m margin src.w src.mf) (h0 : src.w = 0) (hm : 1 ≤ margin) (t : Nat) :
    uget margin src (·.mf) t = 0 := by
  simp only [uget]
  exact ugetA_out m margin src.lo src.w src.mf hsrc hm t (by omega)

/-- Reads outside the source band are zero. -/
theorem uget_out_src (hsrc : WFA m margin src.w src.mf) (hm : 1 ≤ margin) (t : Nat)
    (ht : t < src.lo ∨ src.lo + src.w ≤ t) : uget margin src (·.mf) t = 0 := by
  simp only [uget]
  exact ugetA_out m margin src.lo src.w src.mf hsrc hm t ht

/-- Main theorem: a level returned by the single-source builder is well-formed
and its M front denotes `nextLevelR`'s from any `R` with the same M reads and
the invariant. -/
theorem uLevelS_some (hsrc : WFA m margin src.w src.mf)
    (hR : ∀ t, t < len → rget R.mf t = (uget margin src (·.mf) t).toNat)
    (hinv : ∀ t, rget R.xf t ≤ rget R.mf t ∧ rget R.yf t ≤ rget R.mf t)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len = m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size) (lv : ULevel)
    (h : uLevelS len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 src = some lv) :
    WFA m margin lv.w lv.mf ∧
    ∀ t, t < len → (uget margin lv (·.mf) t).toNat = rget (nextLevelR m n xa ya len 1 1 1 [R]).mf t := by
  -- the model side, in terms of the source's reads
  have hmodel : ∀ t, t < len → rget (nextLevelR m n xa ya len 1 1 1 [R]).mf t =
      modelCellS m n len xa ya (fun t' => (uget margin src (·.mf) t').toNat) t := by
    intro t ht
    rw [rget_nextLevelR_single m n len xa ya R hinv t]
    apply modelCellS_congr
    · exact hR t ht
    · intro _; exact hR (t - 1) (by omega)
    · intro hl; exact hR (t + 1) hl
  unfold uLevelS at h
  dsimp only at h
  by_cases h0 : src.w = 0
  · rw [if_pos h0] at h
    have hlv : lv = uEmpty := (Option.some.inj h).symm
    subst hlv
    refine ⟨(wf_uEmpty m margin).mf, ?_⟩
    intro t ht
    rw [hmodel t ht, uget_uEmpty margin (·.mf) rfl t]
    symm
    apply modelCellS_zero
    all_goals simp only [uget_empty_src m margin src hsrc h0 hm]; rfl
  · rw [if_neg h0] at h
    have hpos : 0 < src.w := Nat.pos_of_ne_zero h0
    by_cases hne : min (src.lo + src.w + 1) len ≤ src.lo - 1
    · rw [if_pos hne] at h
      have hlv : lv = uEmpty := (Option.some.inj h).symm
      subst hlv
      refine ⟨(wf_uEmpty m margin).mf, ?_⟩
      intro t ht
      rw [hmodel t ht, uget_uEmpty margin (·.mf) rfl t]
      symm
      have hfar : len ≤ src.lo - 1 := by
        rcases Nat.le_total (src.lo + src.w + 1) len with hh | hh
        · rw [Nat.min_eq_left hh] at hne; omega
        · rw [Nat.min_eq_right hh] at hne; exact hne
      have hout : ∀ t', t' ≤ t + 1 → uget margin src (·.mf) t' = 0 := fun t' ht' =>
        uget_out_src m margin src hsrc hm t' (Or.inl (by omega))
      apply modelCellS_zero
      · show (uget margin src (·.mf) t).toNat = 0
        rw [hout t (by omega)]; rfl
      · show (uget margin src (·.mf) (t - 1)).toNat = 0
        rw [hout (t - 1) (by omega)]; rfl
      · show (uget margin src (·.mf) (t + 1)).toNat = 0
        rw [hout (t + 1) (by omega)]; rfl
    · rw [if_neg hne] at h
      generalize hL : src.lo - 1 = lo at h hne
      generalize hW : min (src.lo + src.w + 1) len - lo = w at h hne
      have hlolen : lo + w ≤ len := by omega
      split at h
      · rename_i hc
        have hlv := (Option.some.inj h).symm
        subst hlv
        obtain ⟨hcw, hcm, hcs, hco, hbase, hsz1, hsz2, hsh, hw1⟩ := levelCheckSB_true _ _ _ _ hc
        unfold uLevelSBody
        dsimp only
        have hspec := uFillS_spec xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32
          (UInt32.ofNatLT w hcw) (by simp only [UInt32.toNat_ofNatLT]; exact hw1) src.mf
          (UInt32.ofNatLT (margin + lo - src.lo + 1) hsh) (UInt32.ofNatLT margin hcm)
          (w + 2 * margin)
          (by simp only [UInt32.toNat_ofNatLT]; exact hsz1) hsz2
          (by simp only [UInt32.toNat_ofNatLT]; exact hco) hcs
          0 (by simp [UInt32.le_iff_toNat_le]) lo.toUInt32 (src.mf.getD (margin + lo - src.lo - 1) 0)
          (src.mf.getD (margin + lo - src.lo) 0)
          (Array.replicate (w + 2 * margin) 0) Array.size_replicate
          (by simp only [UInt32.toNat_zero, UInt32.toNat_ofNatLT]; congr 1; omega)
          (by simp only [UInt32.toNat_zero, UInt32.toNat_ofNatLT]; congr 1; omega)
        simp only at hspec
        obtain ⟨hsize, hval⟩ := hspec
        simp only [UInt32.toNat_ofNatLT, UInt32.toNat_zero, Nat.add_zero, UInt32.sub_zero] at hval
        have hwpos : 0 < w := by omega
        -- the cell values
        have hcell : ∀ j, margin ≤ j → j < margin + w →
            (cellS xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 src.mf
              (UInt32.ofNatLT (margin + lo - src.lo + 1) hsh) (j - margin).toUInt32
              (lo.toUInt32 + (j - margin).toUInt32)).toNat =
            modelCellS m n len xa ya (fun t' => (uget margin src (·.mf) t').toNat) (lo + (j - margin)) := by
          intro j hj1 hj2
          rw [toUInt32_add_of_lt lo (j - margin) (by omega)]
          exact cellS_toNat m n len margin lo (j - margin) xa ya src hsrc hm32 hn32 hb (by omega) hxa
            (by omega) hbase hsh
        have hfle : ∀ t', (uget margin src (·.mf) t').toNat ≤ m + 1 := by
          intro t'; simp only [uget]; exact ugetA_bound m margin _ _ _ hsrc t'
        refine ⟨⟨?_, fun _ => hsize, ?_⟩, ?_⟩
        · -- padding
          intro i hi hout
          have hv := hval i
          rw [if_neg (by omega), Array.getElem?_replicate, if_pos (by rw [hsize] at hi; exact hi)] at hv
          rw [Array.getElem?_eq_getElem hi] at hv
          exact Option.some.inj hv
        · -- bound
          intro i hi
          have hv := hval i
          by_cases hin : margin ≤ i ∧ i < margin + w
          · rw [if_pos hin, Array.getElem?_eq_getElem hi] at hv
            rw [Option.some.inj hv, hcell i hin.1 hin.2]
            exact modelCellS_le m n len xa ya hxa _ hfle _
          · rw [if_neg (by omega), Array.getElem?_replicate, if_pos (by rw [hsize] at hi; exact hi),
              Array.getElem?_eq_getElem hi] at hv
            rw [Option.some.inj hv]; simp
        · -- values
          intro t ht
          rw [hmodel t ht]
          simp only [uget, ugetA]
          by_cases hin : lo ≤ t ∧ t < lo + w
          · have hj := hval (t + margin - lo)
            rw [if_pos ⟨by omega, by omega⟩] at hj
            rw [Array.getD_eq_getD_getElem?, hj]
            simp only [Option.getD_some]
            rw [hcell (t + margin - lo) (by omega) (by omega)]
            have e2 : lo + (t + margin - lo - margin) = t := by omega
            rw [e2]
            rfl
          · -- outside the band: the loop wrote nothing, the model reads only zeros
            have hz : ((uFillS xa ya m.toUInt32 n.toUInt32 len.toUInt32 hm32 hn32 (UInt32.ofNatLT w hcw)
                (by simp only [UInt32.toNat_ofNatLT]; exact hw1) src.mf
                (UInt32.ofNatLT (margin + lo - src.lo + 1) hsh) (UInt32.ofNatLT margin hcm) (w + 2 * margin)
                (by simp only [UInt32.toNat_ofNatLT]; exact hsz1) hsz2
                (by simp only [UInt32.toNat_ofNatLT]; exact hco) hcs 0 (by simp [UInt32.le_iff_toNat_le]) lo.toUInt32
                (src.mf.getD (margin + lo - src.lo - 1) 0) (src.mf.getD (margin + lo - src.lo) 0)
                (Array.replicate (w + 2 * margin) 0) Array.size_replicate).getD (t + margin - lo) 0).toNat = 0 := by
              have hj := hval (t + margin - lo)
              rw [if_neg (by omega), Array.getElem?_replicate] at hj
              rw [Array.getD_eq_getD_getElem?, hj]
              split <;> rfl
            rw [hz]
            symm
            have hout : ∀ t', t' + 1 = t ∨ t' = t ∨ t' = t + 1 → uget margin src (·.mf) t' = 0 := by
              intro t' ht'
              apply uget_out_src m margin src hsrc hm
              rcases Nat.lt_or_ge t lo with hlt | hge
              · left; omega
              · right
                have : lo + w ≤ t := by omega
                rcases Nat.le_total (src.lo + src.w + 1) len with hh | hh
                · rw [Nat.min_eq_left hh] at hW; omega
                · rw [Nat.min_eq_right hh] at hW; omega
            apply modelCellS_zero
            · show (uget margin src (·.mf) t).toNat = 0
              rw [hout t (Or.inr (Or.inl rfl))]; rfl
            · show (uget margin src (·.mf) (t - 1)).toNat = 0
              by_cases h0 : t = 0
              · subst h0; rw [hout 0 (Or.inr (Or.inl rfl))]; rfl
              · rw [hout (t - 1) (Or.inl (by omega))]; rfl
            · show (uget margin src (·.mf) (t + 1)).toNat = 0
              rw [hout (t + 1) (Or.inr (Or.inr rfl))]; rfl
      · cases h

end LevelS

end AlignmentSpec.U32Proof
#print axioms AlignmentSpec.U32Proof.uLevelS_some
