import MapperFastKernel
import MapperFastMerge

/-!
Seeds and penalties (lemma (d) of the plan): which anchors a hit window has.

* `same_hit_mask`: a same-length window with penalty `≤ 12` has a clean seed on
  its diagonal (so its anchor is in the anchor list);
* `same_lower`: its mismatch count is at least the number of seeds not clean
  on that diagonal (penalty `≥ 4k` when `k` seeds are not clean);
* `gap_support`: a one-gap window with penalty `≤ 12` has at least 2 clean
  seeds on its two diagonals together, at least 3 when the penalty is `≤ 9`;
* `penB_gap_ge`: a window of another length costs at least 8.
-/

namespace MapSpec.Fast

open MapSpec

theorem seedBit_ne (G R : ByteArray) (j d : Nat) :
    seedBit G R j d ≠ 0 ↔ (BIAS - j * q ≤ d ∧ MatchAt G (d - (BIAS - j * q)) R (j * q)) := by
  unfold seedBit
  split
  · next h => exact ⟨fun _ => h, fun _ => Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega : 0 < 2))⟩
  · next h => exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

theorem pop4_maskAt (G R : ByteArray) (d : Nat) :
    pop4 (maskAt G R d) = (if seedBit G R 0 d = 0 then 0 else 1) + (if seedBit G R 1 d = 0 then 0 else 1) +
      (if seedBit G R 2 d = 0 then 0 else 1) + (if seedBit G R 3 d = 0 then 0 else 1) := by
  unfold maskAt seedBit
  split <;> split <;> split <;> split <;> rfl

theorem maskAt_bits (G R : ByteArray) (d : Nat) :
    (maskAt G R d % 2 = 1 ↔ seedBit G R 0 d ≠ 0) ∧ (maskAt G R d / 2 % 2 = 1 ↔ seedBit G R 1 d ≠ 0) ∧
    (maskAt G R d / 4 % 2 = 1 ↔ seedBit G R 2 d ≠ 0) ∧ (maskAt G R d / 8 % 2 = 1 ↔ seedBit G R 3 d ≠ 0) := by
  unfold maskAt seedBit
  split <;> split <;> split <;> split <;> decide

/-- A seed is clean on diagonal `d` iff its letters match the genome at offset `off`. -/
theorem seedBit_match (G R : ByteArray) (j d off : Nat) (hd : BIAS - j * q ≤ d)
    (ho : d - (BIAS - j * q) = off + j * q) (hfit : off + j * q + q ≤ G.size) :
    seedBit G R j d ≠ 0 ↔ cntP (fun k => R.get! k != G.get! (off + k)) (j * q) q = 0 := by
  rw [seedBit_ne, ho]
  constructor
  · rintro ⟨-, -, hm⟩
    apply cntP_zero_of
    intro k h1 h2
    have := hm (k - j * q) (by omega)
    rw [show off + j * q + (k - j * q) = off + k by omega, show j * q + (k - j * q) = k by omega] at this
    simp [this]
  · intro h
    refine ⟨hd, hfit, fun k hk => ?_⟩
    have := cntP_eq_zero _ _ _ h (j * q + k) (by omega) (by omega)
    rw [show off + (j * q + k) = off + j * q + k by omega] at this
    simp at this; exact this.symm

theorem seedBit_start (G R : ByteArray) (st j : Nat) (hj : j < 4) (hfit : st + j * q + q ≤ G.size) :
    seedBit G R j (st + BIAS) ≠ 0 ↔ hc R G st (j * q) q = 0 :=
  seedBit_match G R j (st + BIAS) st (by simp [BIAS, q]; omega) (by simp [BIAS, q]; omega) hfit

theorem preB_seeds (R G : ByteArray) (st : Nat) (hn : 100 ≤ R.size) :
    hc R G st 0 25 + hc R G st 25 25 + hc R G st 50 25 + hc R G st 75 25 ≤ preB R G st R.size := by
  unfold preB
  have e : R.size = 25 + (25 + (25 + (25 + (R.size - 100)))) := by omega
  conv => rhs; rw [e]
  simp only [cntP_add, hc, Nat.zero_add, Nat.reduceAdd]
  omega

/-- Same-length windows: clean seeds lower the mismatch count only where they are clean. -/
theorem same_lower (R G : ByteArray) (st : Nat) (hn : 100 ≤ R.size) (hfit : st + R.size ≤ G.size) :
    4 - pop4 (maskAt G R (st + BIAS)) ≤ preB R G st R.size := by
  have hp := preB_seeds R G st hn
  have b : ∀ j, j < 4 → seedBit G R j (st + BIAS) = 0 → 1 ≤ hc R G st (j * q) q := by
    intro j hj h0
    apply Nat.pos_of_ne_zero
    intro h; exact (seedBit_start G R st j hj (by simp [q]; omega)).2 h h0
  have b0 := b 0 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega); have b3 := b 3 (by omega)
  simp only [q, Nat.reduceMul] at b0 b1 b2 b3
  rw [pop4_maskAt]
  split <;> split <;> split <;> split <;> simp_all <;> omega

theorem same_hit_mask (R G : ByteArray) (st : Nat) (hn : 100 ≤ R.size) (hfit : st + R.size ≤ G.size)
    (h : penSame R G st ≤ 12) : maskAt G R (st + BIAS) ≠ 0 := by
  have hl := same_lower R G st hn hfit
  unfold penSame at h
  have : preB R G st R.size ≤ 3 := by split at h <;> omega
  intro h0
  rw [h0] at hl
  simp [pop4] at hl
  omega

/-- The bits a clean seed sets, for mask hypotheses of `hamSeeds_spec`. -/
theorem same_clean (R G : ByteArray) (st : Nat) (hn : 100 ≤ R.size) (hfit : st + R.size ≤ G.size) :
    (maskAt G R (st + BIAS) % 2 = 1 → hc R G st 0 25 = 0) ∧
    (maskAt G R (st + BIAS) / 2 % 2 = 1 → hc R G st 25 25 = 0) ∧
    (maskAt G R (st + BIAS) / 4 % 2 = 1 → hc R G st 50 25 = 0) ∧
    (maskAt G R (st + BIAS) / 8 % 2 = 1 → hc R G st 75 25 = 0) := by
  obtain ⟨b0, b1, b2, b3⟩ := maskAt_bits G R (st + BIAS)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact (seedBit_start G R st 0 (by omega) (by simp [q]; omega)).1 (b0.1 h)
  · exact (seedBit_start G R st 1 (by omega) (by simp [q]; omega)).1 (b1.1 h)
  · exact (seedBit_start G R st 2 (by omega) (by simp [q]; omega)).1 (b2.1 h)
  · exact (seedBit_start G R st 3 (by omega) (by simp [q]; omega)).1 (b3.1 h)

theorem penB_le (R G : ByteArray) (st len : Nat) : penB R G st len ≤ 13 := by
  unfold penB penSame penGap; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem penB_gap_ge (R G : ByteArray) (st len : Nat) (h : len ≠ R.size) : 8 ≤ penB R G st len := by
  have hL : 1 ≤ gapLen R.size len := by unfold gapLen; split <;> omega
  unfold penB penGap; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem seedBit_at (G R : ByteArray) (j d x : Nat) (hd : BIAS - j * q ≤ d) (hx : d - (BIAS - j * q) = x)
    (hfit : x + q ≤ G.size) (hm : ∀ k, k < q → G.get! (x + k) = R.get! (j * q + k)) : seedBit G R j d ≠ 0 := by
  rw [seedBit_ne, hx]; exact ⟨hd, hfit, hm⟩

theorem ite01 (u : Nat) : (if u = 0 then 0 else 1) ≤ 1 ∧ (u ≠ 0 → (if u = 0 then 0 else 1) = 1) := by
  split <;> simp_all

/-- **Support of a one-gap hit.**  Its two diagonals carry at least 2 clean
seeds together, at least 3 when the penalty is `≤ 9`. -/
theorem gap_support (R G : ByteArray) (st len : Nat) (hn : 100 ≤ R.size) (hfit : st + len ≤ G.size)
    (hne : len ≠ R.size) (h3 : gapLen R.size len ≤ 3) (hp : penGap R G st len ≤ 12) :
    (if penGap R G st len ≤ 9 then 3 else 2) ≤
      pop4 (maskAt G R (st + BIAS)) + pop4 (maskAt G R (st + len + BIAS - R.size)) := by
  have hL1 : 1 ≤ gapLen R.size len := by unfold gapLen; split <;> omega
  have hsk : skipOf R.size len = 0 ∧ R.size < len ∧ len = R.size + gapLen R.size len ∨
      skipOf R.size len = gapLen R.size len ∧ len < R.size ∧ len + gapLen R.size len = R.size := by
    unfold skipOf gapLen; split <;> split <;> omega
  have hpg : penGap R G st len = 6 + 2 * gapLen R.size len + 4 * minMis R G st len := by
    unfold penGap at hp ⊢; split <;> simp_all
  rw [hpg] at hp ⊢
  generalize hL : gapLen R.size len = L at *
  generalize hskv : skipOf R.size len = skip at *
  obtain ⟨i, hi, hiM⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
  have hM : minMis R G st len = misB R G st len skip i := by unfold minMis; rw [hskv, hiM]
  rw [hM] at hp ⊢
  -- the mismatch indicator of the alignment with its gap at `i`
  let F : Nat → Bool := fun k => if k < i then (R.get! k != G.get! (st + k))
    else if i + skip ≤ k then (R.get! k != G.get! (st + len + k - R.size)) else false
  have hmis : cntP F 0 R.size = misB R G st len skip i := by
    have e : R.size = i + (skip + (R.size - i - skip)) := by omega
    conv => lhs; rw [e]
    rw [cntP_add, cntP_add]
    unfold misB preB sufB
    rw [show R.size - (i + skip) = R.size - i - skip by omega, Nat.zero_add]
    rw [cntP_congr F (fun k => R.get! k != G.get! (st + k)) 0 i (fun k _ h2 => by simp only [F, if_pos (show k < i by omega)])]
    rw [cntP_congr F (fun _ => false) i skip (fun k h1 h2 => by
      simp only [F, if_neg (show ¬ k < i by omega), if_neg (show ¬ i + skip ≤ k by omega)])]
    rw [cntP_zero_of (fun _ => false) i skip (fun _ _ _ => rfl)]
    rw [cntP_congr F (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + skip) (R.size - i - skip) (fun k h1 _ => by
      simp only [F, if_neg (show ¬ k < i by omega), if_pos (show i + skip ≤ k by omega)])]
    omega
  have hseeds : cntP F 0 25 + cntP F 25 25 + cntP F 50 25 + cntP F 75 25 ≤ cntP F 0 R.size := by
    have e : R.size = 25 + (25 + (25 + (25 + (R.size - 100)))) := by omega
    conv => rhs; rw [e]
    simp only [cntP_add, Nat.zero_add, Nat.reduceAdd]
    omega
  -- each seed: clean on the start diagonal, clean on the end diagonal, or touched by the gap
  have seed : ∀ j, j < 4 →
      (j * q + q ≤ i ∧ (cntP F (j * q) q = 0 → seedBit G R j (st + BIAS) ≠ 0)) ∨
      (i + skip ≤ j * q ∧ (cntP F (j * q) q = 0 → seedBit G R j (st + len + BIAS - R.size) ≠ 0)) ∨
      (i < j * q + q ∧ j * q < i + skip) := by
    intro j hj
    by_cases hb : j * q + q ≤ i
    · left
      refine ⟨hb, fun h0 => (seedBit_start G R st j hj (by simp [q] at hb ⊢; omega)).2 ?_⟩
      rw [← h0]; unfold hc
      exact cntP_congr _ _ _ _ (fun k _ h2 => by simp only [F, if_pos (show k < i by omega)])
    · by_cases ha : i + skip ≤ j * q
      · right; left
        refine ⟨ha, fun h0 => ?_⟩
        apply seedBit_at G R j _ (st + len + j * q - R.size) (by simp [BIAS, q] at ha ⊢; omega)
          (by simp [BIAS, q] at ha ⊢; omega) (by simp [q] at ha ⊢; omega)
        intro k hk
        have := cntP_eq_zero _ _ _ h0 (j * q + k) (by omega) (by omega)
        simp only [F, if_neg (show ¬ j * q + k < i by omega), if_pos (show i + skip ≤ j * q + k by omega)] at this
        simp at this
        rw [show st + len + j * q - R.size + k = st + len + (j * q + k) - R.size by omega]
        exact this.symm
      · right; right; omega
  have s0 := seed 0 (by omega); have s1 := seed 1 (by omega); have s2 := seed 2 (by omega); have s3 := seed 3 (by omega)
  rw [pop4_maskAt, pop4_maskAt]
  simp only [q, Nat.reduceMul, Nat.zero_mul] at s0 s1 s2 s3
  have i0 := ite01 (seedBit G R 0 (st + BIAS)); have i1 := ite01 (seedBit G R 1 (st + BIAS))
  have i2 := ite01 (seedBit G R 2 (st + BIAS)); have i3 := ite01 (seedBit G R 3 (st + BIAS))
  have j0 := ite01 (seedBit G R 0 (st + len + BIAS - R.size))
  have j1 := ite01 (seedBit G R 1 (st + len + BIAS - R.size))
  have j2 := ite01 (seedBit G R 2 (st + len + BIAS - R.size))
  have j3 := ite01 (seedBit G R 3 (st + len + BIAS - R.size))
  generalize seedBit G R 0 (st + BIAS) = u0 at *
  generalize seedBit G R 1 (st + BIAS) = u1 at *
  generalize seedBit G R 2 (st + BIAS) = u2 at *
  generalize seedBit G R 3 (st + BIAS) = u3 at *
  generalize seedBit G R 0 (st + len + BIAS - R.size) = v0 at *
  generalize seedBit G R 1 (st + len + BIAS - R.size) = v1 at *
  generalize seedBit G R 2 (st + len + BIAS - R.size) = v2 at *
  generalize seedBit G R 3 (st + len + BIAS - R.size) = v3 at *
  generalize (if u0 = 0 then 0 else 1) = x0 at *
  generalize (if u1 = 0 then 0 else 1) = x1 at *
  generalize (if u2 = 0 then 0 else 1) = x2 at *
  generalize (if u3 = 0 then 0 else 1) = x3 at *
  generalize (if v0 = 0 then 0 else 1) = y0 at *
  generalize (if v1 = 0 then 0 else 1) = y1 at *
  generalize (if v2 = 0 then 0 else 1) = y2 at *
  generalize (if v3 = 0 then 0 else 1) = y3 at *
  generalize cntP F 0 25 = f0 at *
  generalize cntP F 25 25 = f1 at *
  generalize cntP F 50 25 = f2 at *
  generalize cntP F 75 25 = f3 at *
  rw [← hmis] at hp ⊢
  generalize cntP F 0 R.size = m at *
  clear hmis hM hiM hpg hskv hL
  have hm := Nat.le_trans hseeds (Nat.le_refl m)
  clear hseeds
  rcases s0 with ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ <;> rcases s1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
    rcases s2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;> rcases s3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
    split <;> omega

end MapSpec.Fast

#print axioms MapSpec.Fast.gap_support
#print axioms MapSpec.Fast.same_lower
