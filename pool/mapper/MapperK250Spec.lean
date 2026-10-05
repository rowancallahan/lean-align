import MapperK250
import MapperGenScore

/-!
# `gappedPen3` and `kerG3` (byte level)

`gappedPen3` is `gappedPen2` with a third level (two mismatches around the gap):
the one-gap formula capped at `lim + 1` for `lim ≤ 17` (`gappedPen3_spec`).  Hence
`kerG3` is the window formula `fB` capped at `lim + 1` (`kerG3_eq`), and `kerG` for
`lim ≤ 15` (`kerG3_kerG`).
-/

namespace MapSpec.Fast

open MapSpec

theorem gappedPen3_spec (R G : ByteArray) (st len lim : Nat) (hne : len ≠ R.size) (hlim : lim ≤ 17) :
    gappedPen3 R G st len lim = min (6 + 2 * gapLen R.size len + 4 * minMis R G st len) (lim + 1) := by
  have hL : gapLen R.size len = if len > R.size then len - R.size else R.size - len := rfl
  have hsk : skipOf R.size len = if len < R.size then gapLen R.size len else 0 := by
    unfold skipOf gapLen; split <;> (try split) <;> omega
  unfold gappedPen3 minMis
  simp only []
  rw [← hL, ← hsk]
  generalize hLv : gapLen R.size len = L at *
  generalize hskv : skipOf R.size len = skip at *
  have hL1 : 1 ≤ L := by rw [← hLv]; unfold gapLen; split <;> omega
  have hstop : skip ≤ R.size := by rw [← hskv]; unfold skipOf; split <;> omega
  by_cases hl : lim < 6 + 2 * L
  · rw [if_pos hl]; omega
  rw [if_neg hl]
  obtain ⟨f1a, f1b, f1⟩ := fwdMis_spec R G st (R.size - skip) _ 0 1 rfl (by omega) (Nat.le_refl _)
  obtain ⟨f2a, f2b, f2⟩ := fwdMis_spec R G st (R.size - skip) _ 0 2 rfl (by omega) (by omega)
  obtain ⟨f3a, f3b, f3⟩ := fwdMis_spec R G st (R.size - skip) _ 0 3 rfl (by omega) (by omega)
  obtain ⟨e1a, e1b, e1⟩ := bwdMis_spec R G st len skip _ R.size 1 rfl hstop (Nat.le_refl _)
  obtain ⟨e2a, e2b, e2⟩ := bwdMis_spec R G st len skip _ R.size 2 rfl hstop (by omega)
  obtain ⟨e3a, e3b, e3⟩ := bwdMis_spec R G st len skip _ R.size 3 rfl hstop (by omega)
  generalize fwdMis R G st (R.size - skip) 0 1 = F1 at *
  generalize fwdMis R G st (R.size - skip) 0 2 = F2 at *
  generalize fwdMis R G st (R.size - skip) 0 3 = F3 at *
  generalize bwdMis R G st len skip R.size 1 = E1 at *
  generalize bwdMis R G st len skip R.size 2 = E2 at *
  generalize bwdMis R G st len skip R.size 3 = E3 at *
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
  have hM2 : minUpTo (misB R G st len skip) (R.size - skip) ≤ 2 ↔
      (E1 - skip ≤ F3 ∨ E2 - skip ≤ F2 ∨ E3 - skip ≤ F1) := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
      rw [hmis i hi] at he
      by_cases hp0 : cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) = 0
      · right; right
        have := (f1 i (by omega) hi).1 (by omega)
        have := (e3 (i + skip) (by omega) (by omega)).1 (by omega)
        omega
      · by_cases hp1 : cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) = 1
        · right; left
          have := (f2 i (by omega) hi).1 (by omega)
          have := (e2 (i + skip) (by omega) (by omega)).1 (by omega)
          omega
        · left
          have := (f3 i (by omega) hi).1 (by omega)
          have := (e1 (i + skip) (by omega) (by omega)).1 (by omega)
          omega
    · rintro (h | h | h)
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F3 f3b
        rw [hmis F3 f3b] at this
        have := (f3 F3 (by omega) f3b).2 (Nat.le_refl _)
        have := (e1 (F3 + skip) (by omega) (by omega)).2 (by omega)
        omega
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F2 f2b
        rw [hmis F2 f2b] at this
        have := (f2 F2 (by omega) f2b).2 (Nat.le_refl _)
        have := (e2 (F2 + skip) (by omega) (by omega)).2 (by omega)
        omega
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F1 f1b
        rw [hmis F1 f1b] at this
        have := (f1 F1 (by omega) f1b).2 (Nat.le_refl _)
        have := (e3 (F1 + skip) (by omega) (by omega)).2 (by omega)
        omega
  generalize minUpTo (misB R G st len skip) (R.size - skip) = M at *
  by_cases h0 : E1 - skip ≤ F1
  · rw [if_pos h0, hM0.2 h0]; omega
  · rw [if_neg h0]
    have hM0' : M ≠ 0 := fun h => h0 (hM0.1 h)
    by_cases hl2 : lim < 10 + 2 * L
    · rw [if_pos hl2]; omega
    · rw [if_neg hl2]
      by_cases h1 : (decide (E1 - skip ≤ F2) || decide (E2 - skip ≤ F1)) = true
      · rw [if_pos h1]
        have := hM1.2 (by simpa using h1)
        omega
      · rw [if_neg h1]
        have hM1' : ¬ M ≤ 1 := fun h => h1 (by simpa using hM1.1 h)
        by_cases hl3 : lim < 14 + 2 * L
        · rw [if_pos hl3]; omega
        · rw [if_neg hl3]
          by_cases h2 : (decide (E1 - skip ≤ F3) || decide (E2 - skip ≤ F2) || decide (E3 - skip ≤ F1)) = true
          · rw [if_pos h2]
            have := hM2.2 (by simpa [or_assoc] using h2)
            omega
          · rw [if_neg h2]
            have : ¬ M ≤ 2 := fun h => h2 (by simpa [or_assoc] using hM2.1 h)
            omega

theorem kerG3_eq (R G : ByteArray) (st len lim : Nat) (hlim : lim ≤ 17) :
    kerG3 R G st len lim = if st + len ≤ G.size then min (fB R G st len) (lim + 1) else lim + 1 := by
  unfold kerG3
  split
  · unfold fB
    split
    · next hs =>
      dsimp only
      rw [hamming_spec R G st (lim / 4) R.size _ 0 0 rfl (Nat.zero_le _), Nat.zero_add]
      unfold preB
      rw [Nat.sub_zero]
      generalize cntP (fun k => R.get! k != G.get! (st + k)) 0 R.size = c
      by_cases hc : c ≤ lim / 4
      · rw [Nat.min_eq_left (by omega), if_pos (by omega)]; omega
      · rw [Nat.min_eq_right (by omega), if_neg (by omega)]; omega
    · next hs => exact gappedPen3_spec R G st len lim hs hlim
  · rfl

theorem kerG3_kerG (R G : ByteArray) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerG3 R G st len lim = kerG R G st len lim := by
  rw [kerG3_eq R G st len lim (by omega), kerG_eq R G st len lim hlim]

end MapSpec.Fast
