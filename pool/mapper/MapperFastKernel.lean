import MapperFastBytes
import MapperFastAlgo

/-!
The fast window kernels compute `penB`:

* `hamming_spec`: the capped mismatch loop is `min (m + count) (lim + 1)`;
* `hamSeeds_spec`: skipping seeds known to be clean, it is `min (mismatches) (lim + 1)`;
* `gappedPen_spec`: the one-gap scan returns `penGap` when it is `≤ lim`, else `lim + 1`.
-/

namespace MapSpec.Fast

open MapSpec

theorem hamming_spec (r g : ByteArray) (a lim stop : Nat) :
    ∀ d i m, stop - i = d → m ≤ lim →
      hamming r g a lim i stop m = min (m + cntP (fun k => r.get! k != g.get! (a + k)) i (stop - i)) (lim + 1) := by
  intro d
  induction d with
  | zero =>
    intro i m hd hm
    unfold hamming
    rw [if_neg (by omega), hd]; simp [cntP]; omega
  | succ d ih =>
    intro i m hd hm
    unfold hamming
    rw [if_pos (by omega), show stop - i = (stop - (i + 1)) + 1 by omega, cntP]
    by_cases hp : (r.get! i != g.get! (a + i)) = true
    · rw [if_pos hp, if_pos hp]
      by_cases hl : lim < m + 1
      · rw [if_pos hl]; omega
      · rw [if_neg hl, ih (i + 1) (m + 1) (by omega) (by omega)]; omega
    · rw [if_neg hp, if_neg hp, ih (i + 1) m (by omega) hm]; omega

/-- Mismatch count of `R[i, i+m)` on diagonal `a`. -/
abbrev hc (R G : ByteArray) (a i m : Nat) : Nat := cntP (fun k => R.get! k != G.get! (a + k)) i m

theorem hamStep_spec (r g : ByteArray) (a lim i stop m : Nat) (clean : Bool) (S : Nat) (hm : m ≤ lim + 1)
    (hS : clean = true → S = 0) (hc' : hc r g a i (stop - i) = S) :
    hamStep r g a lim i stop clean m = min (m + S) (lim + 1) := by
  unfold hamStep
  by_cases h1 : m ≤ lim
  · cases clean with
    | false =>
      simp only [h1, decide_true, Bool.not_false, Bool.and_self, if_true]
      rw [hamming_spec r g a lim stop _ i m rfl h1]
      simp only [hc] at hc'
      rw [hc']
    | true =>
      simp only [h1, decide_true, Bool.not_true, Bool.and_false]
      rw [hS rfl]; simp; omega
  · simp only [show decide (m ≤ lim) = false by simp; omega, Bool.false_and]
    simp; omega

/-- **Same-length windows.**  With every seed in `mask` clean on diagonal `a`,
`hamSeeds` is the mismatch count of the read at `a`, capped at `lim + 1`. -/
theorem hamSeeds_spec (R G : ByteArray) (a mask lim : Nat) (hn : 4 * q ≤ R.size)
    (h0 : mask % 2 = 1 → hc R G a 0 25 = 0) (h1 : mask / 2 % 2 = 1 → hc R G a 25 25 = 0)
    (h2 : mask / 4 % 2 = 1 → hc R G a 50 25 = 0) (h3 : mask / 8 % 2 = 1 → hc R G a 75 25 = 0) :
    hamSeeds R G a mask lim = min (preB R G a R.size) (lim + 1) := by
  unfold hamSeeds
  simp only [q] at hn ⊢
  have hs : preB R G a R.size =
      hc R G a 0 25 + hc R G a 25 25 + hc R G a 50 25 + hc R G a 75 25 + hc R G a 100 (R.size - 100) := by
    unfold preB
    have e : R.size = 25 + 25 + 25 + 25 + (R.size - 100) := by omega
    conv => lhs; rw [e]
    simp only [cntP_add, hc]
  rw [hamming_spec R G a lim R.size _ (4 * 25) 0 rfl (by omega)]
  rw [hamStep_spec R G a lim 0 25 _ _ (hc R G a 0 25) (by omega) (by simp; exact h0) rfl]
  rw [hamStep_spec R G a lim 25 (2 * 25) _ _ (hc R G a 25 25) (by omega) (by simp; exact h1) rfl]
  rw [hamStep_spec R G a lim (2 * 25) (3 * 25) _ _ (hc R G a 50 25) (by omega) (by simp; exact h2) rfl]
  rw [hamStep_spec R G a lim (3 * 25) (4 * 25) _ _ (hc R G a 75 25) (by omega) (by simp; exact h3) rfl]
  rw [hs]
  simp only [hc, Nat.reduceMul] at *
  omega

theorem misCount_spec (r g : ByteArray) (d1 d0 stop : Nat) :
    ∀ d k m, stop - k = d →
      misCount r g d1 d0 k stop m = m + cntP (fun k => r.get! k != g.get! (k + d1 - d0)) k (stop - k) := by
  intro d
  induction d with
  | zero => intro k m hd; unfold misCount; rw [if_neg (by omega), hd]; rfl
  | succ d ih =>
    intro k m hd
    unfold misCount
    rw [if_pos (by omega), ih (k + 1) _ (by omega), show stop - k = (stop - (k + 1)) + 1 by omega, cntP]
    split <;> simp_all <;> omega

theorem minUpTo_anti (f : Nat → Nat) (i k : Nat) (h : i ≤ k) : minUpTo f k ≤ minUpTo f i := by
  induction k with
  | zero => rw [show i = 0 by omega]; exact Nat.le_refl _
  | succ k ih =>
    by_cases hi : i = k + 1
    · subst hi; exact Nat.le_refl _
    · simp only [minUpTo]; exact Nat.le_trans (Nat.min_le_left _ _) (ih (by omega))

theorem minUpTo_tail (f : Nat → Nat) (c i k : Nat) (h : i ≤ k)
    (hf : ∀ i', i < i' → i' ≤ k → c < f i') : minUpTo f k = minUpTo f i ∨ c < minUpTo f k := by
  induction k with
  | zero => left; rw [show i = 0 by omega]
  | succ k ih =>
    by_cases hi : i = k + 1
    · subst hi; left; rfl
    · have hk := hf (k + 1) (by omega) (Nat.le_refl _)
      simp only [minUpTo]
      rcases ih (by omega) (fun i' h1 h2 => hf i' h1 (by omega)) with e | e
      · rw [e]
        by_cases hm : minUpTo f i ≤ f (k + 1)
        · left; exact Nat.min_eq_left hm
        · right; rw [Nat.min_eq_right (by omega)]; exact hk
      · right; omega

theorem preB_succ (R G : ByteArray) (st i : Nat) :
    preB R G st (i + 1) = if (R.get! i != G.get! (st + i)) = true then preB R G st i + 1 else preB R G st i := by
  unfold preB; rw [cntP_add]; simp only [cntP, Nat.zero_add]; split <;> rfl

theorem sufB_succ (R G : ByteArray) (st len j : Nat) (hj : j < R.size) :
    sufB R G st len (j + 1) =
      sufB R G st len j - (if (R.get! j != G.get! (st + len + j - R.size)) = true then 1 else 0) := by
  unfold sufB
  rw [show R.size - j = (R.size - (j + 1)) + 1 by omega, cntP]
  omega

/-- The scan over gap positions `i .. stop` with early exit. -/
theorem gapScan_spec (r g : ByteArray) (st len skip mmax stop : Nat) (hst : stop + skip = r.size) :
    ∀ d i, stop - i = d → i ≤ stop →
      (minUpTo (misB r g st len skip) stop ≤ mmax →
        gapScan r g st len skip mmax stop i (preB r g st i) (sufB r g st len (i + skip))
          (minUpTo (misB r g st len skip) i) = minUpTo (misB r g st len skip) stop) ∧
      (mmax < minUpTo (misB r g st len skip) stop →
        mmax < gapScan r g st len skip mmax stop i (preB r g st i) (sufB r g st len (i + skip))
          (minUpTo (misB r g st len skip) i)) := by
  intro d
  induction d with
  | zero =>
    intro i hd hi
    have : i = stop := by omega
    subst this
    unfold gapScan; rw [if_neg (by omega)]
    exact ⟨fun _ => rfl, fun h => h⟩
  | succ d ih =>
    intro i hd hi
    unfold gapScan
    rw [if_pos (by omega)]
    simp only []
    rw [← preB_succ]
    by_cases hx : mmax < preB r g st (i + 1)
    · rw [if_pos hx]
      have hall : ∀ i', i < i' → i' ≤ stop → mmax < misB r g st len skip i' := by
        intro i' h1 h2
        have : preB r g st (i + 1) ≤ preB r g st i' := by
          unfold preB; exact cntP_mono _ 0 i' 0 (i + 1) (Nat.le_refl _) (by omega)
        unfold misB; omega
      have ha := minUpTo_anti (misB r g st len skip) i stop hi
      rcases minUpTo_tail _ mmax i stop hi hall with e | e
      · rw [e]; exact ⟨fun _ => rfl, fun h => h⟩
      · exact ⟨fun h => by omega, fun _ => by omega⟩
    · rw [if_neg hx]
      have hs : (if (r.get! (i + skip) != g.get! (st + len + i + skip - r.size)) = true
          then sufB r g st len (i + skip) - 1 else sufB r g st len (i + skip)) =
          sufB r g st len (i + 1 + skip) := by
        rw [show i + 1 + skip = (i + skip) + 1 by omega, sufB_succ r g st len (i + skip) (by omega),
          show st + len + (i + skip) = st + len + i + skip by omega]
        split <;> simp_all
      have hb : min (minUpTo (misB r g st len skip) i) (preB r g st (i + 1) + sufB r g st len (i + 1 + skip)) =
          minUpTo (misB r g st len skip) (i + 1) := by
        simp only [minUpTo, misB]
      have := ih (i + 1) (by omega) (by omega)
      rw [hs, hb]
      exact this

/-- **One-gap windows.**  `gappedPen` returns `penGap` when it is `≤ lim`, else `lim + 1`. -/
theorem gappedPen_spec (R G : ByteArray) (st len lim : Nat) (hne : len ≠ R.size)
    (h3 : gapLen R.size len ≤ 3) (hlim : lim ≤ 12) :
    gappedPen R G st len lim = if penGap R G st len ≤ lim then penGap R G st len else lim + 1 := by
  have hL : gapLen R.size len = if len > R.size then len - R.size else R.size - len := rfl
  have hsk : skipOf R.size len = if len < R.size then gapLen R.size len else 0 := by
    unfold skipOf gapLen; split <;> (try split) <;> omega
  unfold gappedPen penGap minMis
  simp only []
  rw [← hL, ← hsk]
  generalize hLv : gapLen R.size len = L at *
  generalize hskv : skipOf R.size len = skip at *
  have hL1 : 1 ≤ L := by rw [← hLv]; unfold gapLen; split <;> omega
  have hstop : (R.size - skip) + skip = R.size := by rw [← hskv]; unfold skipOf; split <;> omega
  by_cases hl : lim < 6 + 2 * L
  · rw [if_pos hl]
    split
    · split <;> omega
    · rw [if_neg (by omega)]
  rw [if_neg hl]
  have hsuf : misCount R G (st + len) R.size skip R.size 0 = sufB R G st len (0 + skip) := by
    rw [misCount_spec R G (st + len) R.size R.size _ skip 0 rfl, Nat.zero_add, Nat.zero_add]
    unfold sufB
    apply cntP_congr; intro k _ _; rw [show k + (st + len) = st + len + k by omega]
  have h0 : preB R G st 0 = 0 := rfl
  have hm0 : minUpTo (misB R G st len skip) 0 = sufB R G st len (0 + skip) := by
    simp [minUpTo, misB, h0]
  rw [hsuf]
  have hscan := gapScan_spec R G st len skip ((lim - 6 - 2 * L) / 4) (R.size - skip) hstop _ 0 rfl (by omega)
  rw [h0, hm0] at hscan
  generalize minUpTo (misB R G st len skip) (R.size - skip) = M at *
  by_cases hM : M ≤ (lim - 6 - 2 * L) / 4
  · rw [hscan.1 hM, if_neg (show ¬ ((lim - 6 - 2 * L) / 4 < M) by omega)]
    have h12 : 6 + 2 * L + 4 * M ≤ 12 := by omega
    rw [if_pos h12, if_pos (by omega)]
  · have := hscan.2 (by omega)
    rw [if_pos this]
    by_cases h12 : 6 + 2 * L + 4 * M ≤ 12
    · rw [if_pos h12, if_neg (by omega)]
    · rw [if_neg h12, if_neg (by omega)]

/-! ## `gappedPen2`: first and last mismatches -/

theorem fwdMis_spec (r g : ByteArray) (st stop : Nat) :
    ∀ d i0 k, stop - i0 = d → i0 ≤ stop → 1 ≤ k →
      i0 ≤ fwdMis r g st stop i0 k ∧ fwdMis r g st stop i0 k ≤ stop ∧
      ∀ i, i0 ≤ i → i ≤ stop →
        (cntP (fun x => r.get! x != g.get! (st + x)) i0 (i - i0) < k ↔ i ≤ fwdMis r g st stop i0 k) := by
  intro d
  induction d with
  | zero =>
    intro i0 k hd h0 hk
    unfold fwdMis; rw [if_neg (by omega)]
    refine ⟨h0, Nat.le_refl _, fun i h1 h2 => ?_⟩
    rw [show i - i0 = 0 by omega]; simp [cntP]; omega
  | succ d ih =>
    intro i0 k hd h0 hk
    unfold fwdMis; rw [if_pos (by omega)]
    by_cases hp : (r.get! i0 != g.get! (st + i0)) = true
    · rw [if_pos hp]
      by_cases hk1 : k ≤ 1
      · rw [if_pos hk1]
        refine ⟨Nat.le_refl _, by omega, fun i h1 h2 => ?_⟩
        by_cases hi : i = i0
        · subst hi; simp [cntP]; omega
        · rw [show i - i0 = (i - (i0 + 1)) + 1 by omega, Nat.add_comm, cntP_add, cntP, if_pos hp]
          simp only [cntP, Nat.zero_add]; omega
      · rw [if_neg hk1]
        obtain ⟨a1, a2, a3⟩ := ih (i0 + 1) (k - 1) (by omega) (by omega) (by omega)
        refine ⟨by omega, a2, fun i h1 h2 => ?_⟩
        by_cases hi : i = i0
        · subst hi; simp [cntP]; omega
        · have := a3 i (by omega) h2
          rw [show i - i0 = 1 + (i - (i0 + 1)) by omega, cntP_add, cntP, if_pos hp]
          simp only [cntP, Nat.add_zero]; omega
    · rw [if_neg hp]
      obtain ⟨a1, a2, a3⟩ := ih (i0 + 1) k (by omega) (by omega) hk
      refine ⟨by omega, a2, fun i h1 h2 => ?_⟩
      by_cases hi : i = i0
      · subst hi; simp [cntP]; omega
      · have := a3 i (by omega) h2
        rw [show i - i0 = 1 + (i - (i0 + 1)) by omega, cntP_add, cntP, if_neg hp]
        simp only [cntP, Nat.add_zero, Nat.zero_add]; omega

theorem bwdMis_spec (r g : ByteArray) (st len lo : Nat) :
    ∀ d e k, e - lo = d → lo ≤ e → 1 ≤ k →
      lo ≤ bwdMis r g st len lo e k ∧ bwdMis r g st len lo e k ≤ e ∧
      ∀ j, lo ≤ j → j ≤ e →
        (cntP (fun x => r.get! x != g.get! (st + len + x - r.size)) j (e - j) < k ↔
          bwdMis r g st len lo e k ≤ j) := by
  intro d
  induction d with
  | zero =>
    intro e k hd h0 hk
    unfold bwdMis; rw [if_neg (by omega)]
    refine ⟨Nat.le_refl _, h0, fun j h1 h2 => ?_⟩
    rw [show e - j = 0 by omega]; simp [cntP]; omega
  | succ d ih =>
    intro e k hd h0 hk
    unfold bwdMis; rw [if_pos (by omega)]
    have split : ∀ j, j < e → cntP (fun x => r.get! x != g.get! (st + len + x - r.size)) j (e - j) =
        cntP (fun x => r.get! x != g.get! (st + len + x - r.size)) j (e - 1 - j) +
          (if (r.get! (e - 1) != g.get! (st + len + (e - 1) - r.size)) = true then 1 else 0) := by
      intro j hj
      rw [show e - j = (e - 1 - j) + 1 by omega, cntP_add, show j + (e - 1 - j) = e - 1 by omega]
      simp [cntP]
    by_cases hp : (r.get! (e - 1) != g.get! (st + len + (e - 1) - r.size)) = true
    · rw [if_pos hp]
      by_cases hk1 : k ≤ 1
      · rw [if_pos hk1]
        refine ⟨by omega, Nat.le_refl _, fun j h1 h2 => ?_⟩
        by_cases hj : j = e
        · subst hj; simp [cntP]; omega
        · rw [split j (by omega), if_pos hp]; omega
      · rw [if_neg hk1]
        obtain ⟨a1, a2, a3⟩ := ih (e - 1) (k - 1) (by omega) (by omega) (by omega)
        refine ⟨a1, by omega, fun j h1 h2 => ?_⟩
        by_cases hj : j = e
        · subst hj; simp [cntP]; omega
        · have := a3 j h1 (by omega)
          rw [split j (by omega), if_pos hp]; omega
    · rw [if_neg hp]
      obtain ⟨a1, a2, a3⟩ := ih (e - 1) k (by omega) (by omega) hk
      refine ⟨a1, by omega, fun j h1 h2 => ?_⟩
      by_cases hj : j = e
      · subst hj; simp [cntP]; omega
      · have := a3 j h1 (by omega)
        rw [split j (by omega), if_neg hp]; omega

theorem cap_eq (lim X : Nat) (h12 : lim ≤ 12) :
    (if (if X ≤ 12 then X else 13) ≤ lim then (if X ≤ 12 then X else 13) else lim + 1) =
      if X ≤ lim then X else lim + 1 := by
  by_cases h1 : X ≤ 12
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

/-- **One-gap windows, fast form.**  For `lim ≤ 12`, `gappedPen2` returns `penGap`
when it is `≤ lim`, else `lim + 1`. -/
theorem gappedPen2_spec (R G : ByteArray) (st len lim : Nat) (hne : len ≠ R.size)
    (hlim : lim ≤ 12) :
    gappedPen2 R G st len lim = if penGap R G st len ≤ lim then penGap R G st len else lim + 1 := by
  have hL : gapLen R.size len = if len > R.size then len - R.size else R.size - len := rfl
  have hsk : skipOf R.size len = if len < R.size then gapLen R.size len else 0 := by
    unfold skipOf gapLen; split <;> (try split) <;> omega
  unfold gappedPen2 penGap minMis
  simp only []
  rw [← hL, ← hsk]
  generalize hLv : gapLen R.size len = L at *
  generalize hskv : skipOf R.size len = skip at *
  have hL1 : 1 ≤ L := by rw [← hLv]; unfold gapLen; split <;> omega
  have hstop : skip ≤ R.size := by rw [← hskv]; unfold skipOf; split <;> omega
  by_cases hl : lim < 6 + 2 * L
  · rw [if_pos hl]
    split
    · split <;> omega
    · rw [if_neg (by omega)]
  rw [if_neg hl]
  obtain ⟨f1a, f1b, f1⟩ := fwdMis_spec R G st (R.size - skip) _ 0 1 rfl (by omega) (Nat.le_refl _)
  obtain ⟨f2a, f2b, f2⟩ := fwdMis_spec R G st (R.size - skip) _ 0 2 rfl (by omega) (by omega)
  obtain ⟨e1a, e1b, e1⟩ := bwdMis_spec R G st len skip _ R.size 1 rfl hstop (Nat.le_refl _)
  obtain ⟨e2a, e2b, e2⟩ := bwdMis_spec R G st len skip _ R.size 2 rfl hstop (by omega)
  generalize fwdMis R G st (R.size - skip) 0 1 = F1 at *
  generalize fwdMis R G st (R.size - skip) 0 2 = F2 at *
  generalize bwdMis R G st len skip R.size 1 = E1 at *
  generalize bwdMis R G st len skip R.size 2 = E2 at *
  -- mismatches at split `i` in terms of the prefix and suffix counts
  have hmis : ∀ i, i ≤ R.size - skip → misB R G st len skip i =
      cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) +
        cntP (fun x => R.get! x != G.get! (st + len + x - R.size)) (i + skip) (R.size - (i + skip)) := by
    intro i _; rfl
  have hM0 : minUpTo (misB R G st len skip) (R.size - skip) = 0 ↔ E1 - skip ≤ F1 := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
      rw [h, hmis i hi] at he
      have := (f1 i (by omega) hi).1 (by omega)
      have := (e1 (i + skip) (by omega) (by omega)).1 (by omega)
      omega
    · intro h
      have := minUpTo_le (misB R G st len skip) (R.size - skip) F1 f1b
      rw [hmis F1 f1b] at this
      have := (f1 F1 (by omega) f1b).2 (Nat.le_refl _)
      have := (e1 (F1 + skip) (by omega) (by omega)).2 (by omega)
      omega
  have hM1 : minUpTo (misB R G st len skip) (R.size - skip) ≤ 1 ↔ (E1 - skip ≤ F2 ∨ E2 - skip ≤ F1) := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
      rw [hmis i hi] at he
      by_cases hpre : cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) = 0
      · right
        have := (f1 i (by omega) hi).1 (by omega)
        have := (e2 (i + skip) (by omega) (by omega)).1 (by omega)
        omega
      · left
        have := (f2 i (by omega) hi).1 (by omega)
        have := (e1 (i + skip) (by omega) (by omega)).1 (by omega)
        omega
    · rintro (h | h)
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F2 f2b
        rw [hmis F2 f2b] at this
        have := (f2 F2 (by omega) f2b).2 (Nat.le_refl _)
        have := (e1 (F2 + skip) (by omega) (by omega)).2 (by omega)
        omega
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F1 f1b
        rw [hmis F1 f1b] at this
        have := (f1 F1 (by omega) f1b).2 (Nat.le_refl _)
        have := (e2 (F1 + skip) (by omega) (by omega)).2 (by omega)
        omega
  generalize minUpTo (misB R G st len skip) (R.size - skip) = M at *
  rw [cap_eq lim _ hlim]
  by_cases h0 : E1 - skip ≤ F1
  · rw [if_pos h0, hM0.2 h0, if_pos (by omega)]; omega
  · rw [if_neg h0]
    have hM0' : M ≠ 0 := fun h => h0 (hM0.1 h)
    by_cases hl2 : lim < 10 + 2 * L
    · rw [if_pos hl2, if_neg (by omega)]
    · rw [if_neg hl2]
      by_cases h1 : (decide (E1 - skip ≤ F2) || decide (E2 - skip ≤ F1)) = true
      · rw [if_pos h1]
        have := hM1.2 (by simpa using h1)
        rw [if_pos (by omega)]; omega
      · rw [if_neg h1]
        have : ¬ M ≤ 1 := fun h => h1 (by simpa using hM1.1 h)
        rw [if_neg (by omega)]

end MapSpec.Fast

#print axioms MapSpec.Fast.hamSeeds_spec
#print axioms MapSpec.Fast.gappedPen2_spec

#print axioms MapSpec.Fast.hamSeeds_spec
#print axioms MapSpec.Fast.gappedPen_spec
