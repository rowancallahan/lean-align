import MapperFastBytes
import MapperFastAlgo

/-!
The fast window kernels compute `penB`:

* `hamming_spec`: the capped mismatch loop is `min (m + count) (lim + 1)`;
* `hamSeeds_spec`: skipping seeds known to be clean, it is `min (mismatches) (lim + 1)`;
* `gappedPen2_spec`: from the first two and last two mismatches, the one-gap
  penalty `penGap` when it is `≤ lim ≤ 12`, else `lim + 1`.
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
    unfold hamming; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
    rw [if_neg (by omega), hd]; simp [cntP]; omega
  | succ d ih =>
    intro i m hd hm
    unfold hamming; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
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
  unfold hamStep; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
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
  unfold hamSeeds; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
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
    unfold fwdMis; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]; rw [if_neg (by omega)]
    refine ⟨h0, Nat.le_refl _, fun i h1 h2 => ?_⟩
    rw [show i - i0 = 0 by omega]; simp [cntP]; omega
  | succ d ih =>
    intro i0 k hd h0 hk
    unfold fwdMis; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]; rw [if_pos (by omega)]
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
    unfold bwdMis; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]; rw [if_neg (by omega)]
    refine ⟨Nat.le_refl _, h0, fun j h1 h2 => ?_⟩
    rw [show e - j = 0 by omega]; simp [cntP]; omega
  | succ d ih =>
    intro e k hd h0 hk
    unfold bwdMis; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]; rw [if_pos (by omega)]
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
