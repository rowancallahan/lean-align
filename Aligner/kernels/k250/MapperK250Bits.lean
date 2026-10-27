import MapperK250

/-!
# Bit lemmas for the word kernels

Base-4 digits (`Packed.dig`) of the `UInt64` operations used by the word kernels:
the fold of each 2-bit field to one bit, the field masks, XOR, the shifted pair of
aligned words (`comb`), the 8-byte gather (`gword`), and the selection of the
`k+1`-th lowest / highest set field (`selLow`, `selHigh`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

theorem dig_eq (x t : Nat) : dig x t = 2 * (x.testBit (2 * t + 1)).toNat + (x.testBit (2 * t)).toNat := by
  have h1 : x.testBit (2 * t) = (x / 2 ^ (2 * t)).testBit 0 := by rw [Nat.testBit_div_two_pow]; simp
  have h2 : x.testBit (2 * t + 1) = (x / 2 ^ (2 * t) / 2).testBit 0 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, Nat.testBit_div_two_pow]; simp
  rw [h1, h2, dig, show 4 ^ t = 2 ^ (2 * t) by rw [Nat.pow_mul]]
  generalize x / 2 ^ (2 * t) = y
  simp only [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 2) with h' | h' <;> simp [h, h'] <;> omega

theorem tb_hi (x : UInt64) (i : Nat) (hi : 64 ≤ i) : x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) hi))

theorem tb_not (m : UInt64) (i : Nat) : (~~~m).toNat.testBit i = (decide (i < 64) && !m.toNat.testBit i) := by
  show (~~~m.toBitVec).getLsbD i = _
  simp [BitVec.getLsbD_not]; rfl

theorem tb_byte (b : UInt8) (i : Nat) (hi : 8 ≤ i) : b.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by decide) hi))

theorem mask55 : ∀ t, t < 32 → (0x5555555555555555 : Nat).testBit (2 * t) = true ∧
    (0x5555555555555555 : Nat).testBit (2 * t + 1) = false := by decide

theorem dig_hi (x : UInt64) (t : Nat) (ht : 32 ≤ t) : dig x.toNat t = 0 := by
  rw [dig_eq, tb_hi _ _ (by omega), tb_hi _ _ (by omega)]; rfl

theorem cntNZ_congr (n x y : Nat) (h : ∀ t, t < n → dig x t = dig y t) : cntNZ n x = cntNZ n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [dig, Nat.pow_zero, Nat.div_one] at h0
    rw [cntNZ, cntNZ, h0, ih (x / 4) (y / 4) (fun t ht => by
      rw [dig_div4, dig_div4]; exact h _ (by omega))]

theorem xor_dig (x y : UInt64) (t : Nat) : dig (x ^^^ y).toNat t = 0 ↔ dig x.toNat t = dig y.toNat t := by
  simp only [dig, UInt64.toNat_xor, show 4 ^ t = 2 ^ (2 * t) by rw [Nat.pow_mul], Nat.xor_div_two_pow]
  exact xor_mod4_eq_zero _ _

theorem fold_dig (x : UInt64) (t : Nat) (ht : t < 32) :
    dig (fold x).toNat t = if dig x.toNat t = 0 then 0 else 1 := by
  have hm := mask55 t ht
  simp only [fold, UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_shiftRight]
  rw [dig_eq, dig_eq]
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
    show (0x5555555555555555 : UInt64).toNat = 0x5555555555555555 from rfl, hm.1, hm.2,
    show 1 + (2 * t + 1) = 2 * t + 2 by omega, show 1 + 2 * t = 2 * t + 1 by omega]
  cases x.toNat.testBit (2 * t) <;> cases x.toNat.testBit (2 * t + 1) <;> simp

theorem lowF_dig (x : UInt64) (c t : Nat) (ht : t < 32) :
    dig (lowF x c).toNat t = if t < c then dig x.toNat t else 0 := by
  unfold lowF
  split
  · rename_i hc
    rw [toNat_mask _ _ hc, show 4 ^ c = 2 ^ (2 * c) by rw [Nat.pow_mul], dig_eq, dig_eq]
    simp only [Nat.testBit_mod_two_pow]
    by_cases h : t < c
    · simp [h, show 2 * t + 1 < 2 * c by omega, show 2 * t < 2 * c by omega]
    · simp [h, show ¬ 2 * t + 1 < 2 * c by omega, show ¬ 2 * t < 2 * c by omega]
  · rw [if_pos (by omega)]

theorem highF_dig (x : UInt64) (c t : Nat) (ht : t < 32) :
    dig (highF x c).toNat t = if t < c then 0 else dig x.toNat t := by
  unfold highF
  split
  · simp_all
  split
  · rename_i hc0 hc
    have h0 : ((1 : UInt64) <<< (2 * c).toUInt64).toNat = 2 ^ (2 * c) := by
      rw [UInt64.toNat_shiftLeft]
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.one_mul, UInt64.toNat_one]
      rw [Nat.mod_eq_of_lt (show 2 * c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 * c < 64 by omega),
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    have h1 : (((1 : UInt64) <<< (2 * c).toUInt64) - 1).toNat = 2 ^ (2 * c) - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h0]; exact Nat.one_le_two_pow), h0,
        UInt64.toNat_one]
    rw [UInt64.toNat_and, dig_eq, dig_eq]
    simp only [Nat.testBit_and, tb_not, h1, Nat.testBit_two_pow_sub_one]
    by_cases h : t < c
    · simp [h, show 2 * t + 1 < 2 * c by omega, show 2 * t < 2 * c by omega]
    · simp [h, show ¬ 2 * t + 1 < 2 * c by omega, show ¬ 2 * t < 2 * c by omega, show 2 * t + 1 < 64 by omega,
        show 2 * t < 64 by omega]
  · rw [if_pos (by omega)]; simp [dig]

theorem comb_dig (cur nxt : UInt64) (s t : Nat) (hs : s < 32) (ht : t < 32) :
    dig (comb cur nxt s (2 * s).toUInt64 (64 - 2 * s).toUInt64).toNat t =
      if s + t < 32 then dig cur.toNat (s + t) else dig nxt.toNat (s + t - 32) := by
  unfold comb
  split
  · subst s; simp [ht]
  have e1 : (2 * s).toUInt64.toNat % 64 = 2 * s := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have e2 : (64 - 2 * s).toUInt64.toNat % 64 = 64 - 2 * s := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, e1, e2, dig_eq, dig_eq, dig_eq]
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  split
  · simp [show 2 * t + 1 < 64 by omega, show 2 * t < 64 by omega, show ¬ 2 * t + 1 ≥ 64 - 2 * s by omega,
      show ¬ 2 * t ≥ 64 - 2 * s by omega, show 2 * s + (2 * t + 1) = 2 * (s + t) + 1 by omega,
      show 2 * s + 2 * t = 2 * (s + t) by omega]
  · simp [show 2 * t + 1 < 64 by omega, show 2 * t < 64 by omega, show 2 * t + 1 ≥ 64 - 2 * s by omega,
      show 2 * t ≥ 64 - 2 * s by omega, tb_hi cur (2 * s + (2 * t + 1)) (by omega), tb_hi cur (2 * s + 2 * t) (by omega),
      show 2 * t + 1 - (64 - 2 * s) = 2 * (s + t - 32) + 1 by omega,
      show 2 * t - (64 - 2 * s) = 2 * (s + t - 32) by omega]

theorem tb_sh (b : UInt8) (k : UInt64) (hk : k.toNat < 64) (i : Nat) (hi : i < 64) :
    (b.toUInt64 <<< k).toNat.testBit i = (decide (k.toNat ≤ i) && b.toNat.testBit (i - k.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp [hi]

theorem gword_dig (w : ByteArray) (u t : Nat) (ht : t < 32) :
    dig (gword w u).toNat t = (w.get! (17 * (u / 2) + 1 + 8 * (u % 2) + t / 4)).toNat / 4 ^ (t % 4) % 4 := by
  simp only [gword, UInt64.toNat_or]
  rw [← dig, dig_eq, dig_eq]
  generalize 17 * (u / 2) + 1 + 8 * (u % 2) = b
  simp only [Nat.testBit_or]
  rw [tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega),
    tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega),
    tb_sh _ _ (by decide) _ (by omega)]
  rw [tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega),
    tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega), tb_sh _ _ (by decide) _ (by omega),
    tb_sh _ _ (by decide) _ (by omega)]
  simp only [UInt8.toNat_toUInt64]
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | omega | simp [tb_byte]

end MapSpec.Fast
