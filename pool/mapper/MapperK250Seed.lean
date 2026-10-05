import MapperK250Chunk
import MapperGenLook

/-!
# Seed hashes from the packed read

`seedHashAt R s` (the hash of the 25-letter seed at `s`) recomputes the big-endian
2-bit code letter by letter.  From the packed words (`packRP`): reverse the 32
fields of a word (`revF`, five SWAR swaps), take the 25 letters at `s` from two
reversed words (`beCode`).  `seedHashK_eq`: the same hash.
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- Fields reversed: field `k` ↦ field `31 − k`. -/
@[inline] def revF (x : UInt64) : UInt64 :=
  let x : UInt64 := ((x >>> 2) &&& (0x3333333333333333 : UInt64)) ||| ((x &&& (0x3333333333333333 : UInt64)) <<< 2)
  let x : UInt64 := ((x >>> 4) &&& (0x0F0F0F0F0F0F0F0F : UInt64)) ||| ((x &&& (0x0F0F0F0F0F0F0F0F : UInt64)) <<< 4)
  let x : UInt64 := ((x >>> 8) &&& (0x00FF00FF00FF00FF : UInt64)) ||| ((x &&& (0x00FF00FF00FF00FF : UInt64)) <<< 8)
  let x : UInt64 := ((x >>> 16) &&& (0x0000FFFF0000FFFF : UInt64)) ||| ((x &&& (0x0000FFFF0000FFFF : UInt64)) <<< 16)
  (x >>> 32) ||| (x <<< 32)

/-- Big-endian 2-bit code of the 25 letters at `s` (first letter highest). -/
@[inline] def beCode (w : Array UInt64) (s : Nat) : UInt64 :=
  let r := s % 32
  let a := revF (w.getD (s / 32) 0)
  let x := if r = 0 then a else (a <<< (2 * r).toUInt64) ||| (revF (w.getD (s / 32 + 1) 0) >>> (64 - 2 * r).toUInt64)
  x >>> 14

/-- `seedHashAt` from the packed read. -/
@[inline] def seedHashK (R : ByteArray) (K : RP) (s : Nat) : Option UInt64 :=
  if K.ok && decide (s + q ≤ R.size) then some (mix (beCode K.w s)) else seedHashAt R s


theorem sw_tb (x M K : UInt64) (m k : Nat) (hm : M.toNat = m) (hk : K.toNat = k) (hK : k < 64)
    (hM : ∀ i, i < 64 → (m.testBit i = true → i ^^^ k = i + k ∧ (k ≤ i → m.testBit (i - k) = false)) ∧
      (m.testBit i = false → k ≤ i ∧ m.testBit (i - k) = true ∧ i ^^^ k = i - k))
    (i : Nat) (hi : i < 64) :
    (((x >>> K) &&& M) ||| ((x &&& M) <<< K)).toNat.testBit i = x.toNat.testBit (i ^^^ k) := by
  rw [UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt64.toNat_and,
    hm, hk, Nat.mod_eq_of_lt hK]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, hi, decide_true, Bool.true_and]
  obtain ⟨h1, h2⟩ := hM i hi
  cases hmi : m.testBit i
  · obtain ⟨a, b, c⟩ := h2 hmi
    simp [a, b, c]
  · obtain ⟨a, b⟩ := h1 hmi
    rw [a, Nat.add_comm]
    by_cases hki : k ≤ i
    · simp [hki, b hki]
    · simp [hki]

theorem sw32_tb (x : UInt64) (i : Nat) (hi : i < 64) :
    ((x >>> 32) ||| (x <<< 32)).toNat.testBit i = x.toNat.testBit (i ^^^ 32) := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
  simp only [show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, hi, decide_true, Bool.true_and]
  have hx : ∀ i, i < 64 → i ^^^ 32 = if i < 32 then i + 32 else i - 32 := by decide
  rw [hx i hi]
  by_cases h : i < 32
  · simp [h, Nat.add_comm, show ¬ 32 ≤ i by omega]
  · simp [h, show 32 ≤ i by omega, tb_hi x (32 + i) (by omega)]

theorem m2 : ∀ i, i < 64 → ((0x3333333333333333 : Nat).testBit i = true → i ^^^ 2 = i + 2 ∧ (2 ≤ i → (0x3333333333333333 : Nat).testBit (i - 2) = false)) ∧
      ((0x3333333333333333 : Nat).testBit i = false → 2 ≤ i ∧ (0x3333333333333333 : Nat).testBit (i - 2) = true ∧ i ^^^ 2 = i - 2) := by decide

theorem m4 : ∀ i, i < 64 → ((0x0F0F0F0F0F0F0F0F : Nat).testBit i = true → i ^^^ 4 = i + 4 ∧ (4 ≤ i → (0x0F0F0F0F0F0F0F0F : Nat).testBit (i - 4) = false)) ∧
      ((0x0F0F0F0F0F0F0F0F : Nat).testBit i = false → 4 ≤ i ∧ (0x0F0F0F0F0F0F0F0F : Nat).testBit (i - 4) = true ∧ i ^^^ 4 = i - 4) := by decide

theorem m8 : ∀ i, i < 64 → ((0x00FF00FF00FF00FF : Nat).testBit i = true → i ^^^ 8 = i + 8 ∧ (8 ≤ i → (0x00FF00FF00FF00FF : Nat).testBit (i - 8) = false)) ∧
      ((0x00FF00FF00FF00FF : Nat).testBit i = false → 8 ≤ i ∧ (0x00FF00FF00FF00FF : Nat).testBit (i - 8) = true ∧ i ^^^ 8 = i - 8) := by decide

theorem m16 : ∀ i, i < 64 → ((0x0000FFFF0000FFFF : Nat).testBit i = true → i ^^^ 16 = i + 16 ∧ (16 ≤ i → (0x0000FFFF0000FFFF : Nat).testBit (i - 16) = false)) ∧
      ((0x0000FFFF0000FFFF : Nat).testBit i = false → 16 ≤ i ∧ (0x0000FFFF0000FFFF : Nat).testBit (i - 16) = true ∧ i ^^^ 16 = i - 16) := by decide

/-- One SWAR swap step. -/
def sw (x M K : UInt64) : UInt64 := ((x >>> K) &&& M) ||| ((x &&& M) <<< K)

theorem revF_eq (x : UInt64) : revF x =
    (fun y : UInt64 => (y >>> 32) ||| (y <<< 32))
      (sw (sw (sw (sw x 0x3333333333333333 2) 0x0F0F0F0F0F0F0F0F 4) 0x00FF00FF00FF00FF 8) 0x0000FFFF0000FFFF 16) := rfl

theorem xor_ix : ∀ i, i < 64 → i ^^^ 32 < 64 ∧ i ^^^ 32 ^^^ 16 < 64 ∧ i ^^^ 32 ^^^ 16 ^^^ 8 < 64 ∧
    i ^^^ 32 ^^^ 16 ^^^ 8 ^^^ 4 < 64 ∧ i ^^^ 32 ^^^ 16 ^^^ 8 ^^^ 4 ^^^ 2 = i ^^^ 62 := by decide

theorem revF_tb (x : UInt64) (i : Nat) (hi : i < 64) : (revF x).toNat.testBit i = x.toNat.testBit (i ^^^ 62) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := xor_ix i hi
  rw [revF_eq]
  simp only []
  rw [sw32_tb _ _ hi, sw, sw_tb _ _ _ 0x0000FFFF0000FFFF 16 rfl rfl (by decide) m16 _ h1, sw, sw_tb _ _ _ 0x00FF00FF00FF00FF 8 rfl rfl (by decide) m8 _ h2,
    sw, sw_tb _ _ _ 0x0F0F0F0F0F0F0F0F 4 rfl rfl (by decide) m4 _ h3, sw, sw_tb _ _ _ 0x3333333333333333 2 rfl rfl (by decide) m2 _ h4, h5]

theorem revF_dig (x : UInt64) (t : Nat) (ht : t < 32) : dig (revF x).toNat t = dig x.toNat (31 - t) := by
  have e : ∀ t, t < 32 → (2 * t + 1) ^^^ 62 = 2 * (31 - t) + 1 ∧ (2 * t) ^^^ 62 = 2 * (31 - t) := by decide
  rw [dig_eq, dig_eq, revF_tb _ _ (by omega), revF_tb _ _ (by omega), (e t ht).1, (e t ht).2]

theorem shr_dig (b K : UInt64) (m t : Nat) (hK : K.toNat = 2 * m) (hm : 2 * m < 64) :
    dig (b >>> K).toNat t = dig b.toNat (t + m) := by
  rw [UInt64.toNat_shiftRight, hK, Nat.mod_eq_of_lt hm, Nat.shiftRight_eq_div_pow]
  unfold dig
  rw [Nat.div_div_eq_div_mul, show 2 ^ (2 * m) * 4 ^ t = 4 ^ (t + m) by
    rw [Nat.pow_mul, Nat.pow_add, Nat.mul_comm]]

theorem shl_dig (a K : UInt64) (r t : Nat) (hK : K.toNat = 2 * r) (hr : r < 32) (ht : t < 32) :
    dig (a <<< K).toNat t = if r ≤ t then dig a.toNat (t - r) else 0 := by
  rw [UInt64.toNat_shiftLeft, hK, Nat.mod_eq_of_lt (show 2 * r < 64 by omega), dig_eq, dig_eq]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases h : r ≤ t
  · simp [h, show 2 * t + 1 < 64 by omega, show 2 * t < 64 by omega, show 2 * r ≤ 2 * t by omega, show 2 * r ≤ 2 * t + 1 by omega,
      show 2 * t + 1 - 2 * r = 2 * (t - r) + 1 by omega, show 2 * t - 2 * r = 2 * (t - r) by omega]
  · simp [h, show ¬ 2 * r ≤ 2 * t + 1 by omega, show ¬ 2 * r ≤ 2 * t by omega]

theorem dig_zero_bits (y t : Nat) (h : dig y t = 0) : y.testBit (2 * t + 1) = false ∧ y.testBit (2 * t) = false := by
  rw [dig_eq] at h
  cases h1 : y.testBit (2 * t + 1) <;> cases h2 : y.testBit (2 * t) <;> simp_all

theorem or_dig_l (x y : UInt64) (t : Nat) (h : dig y.toNat t = 0) : dig (x ||| y).toNat t = dig x.toNat t := by
  obtain ⟨h1, h2⟩ := dig_zero_bits _ _ h
  rw [UInt64.toNat_or, dig_eq, dig_eq, Nat.testBit_or, Nat.testBit_or, h1, h2]; simp

theorem or_dig_r (x y : UInt64) (t : Nat) (h : dig x.toNat t = 0) : dig (x ||| y).toNat t = dig y.toNat t := by
  obtain ⟨h1, h2⟩ := dig_zero_bits _ _ h
  rw [UInt64.toNat_or, dig_eq, dig_eq, Nat.testBit_or, Nat.testBit_or, h1, h2]; simp

theorem getD_get! (w : Array UInt64) (i : Nat) : w.getD i 0 = w[i]! := by
  by_cases h : i < w.size
  · rw [getElem!_pos w i h]; simp [Array.getD, h]
  · rw [getElem!_neg w i h]; simp [Array.getD, h]; rfl

theorem beCode_dig (w : Array UInt64) (s t : Nat) (ht : t < 25) :
    dig (beCode w s).toNat t = if s % 32 ≤ t + 7 then dig (w[s / 32]!).toNat (24 - t + s % 32)
      else dig (w[s / 32 + 1]!).toNat (s % 32 - 8 - t) := by
  unfold beCode
  simp only [getD_get!]
  rw [shr_dig _ _ 7 _ rfl (by omega)]
  have hr := Nat.mod_lt s (show 32 > 0 by omega)
  generalize s % 32 = r at *
  by_cases h0 : r = 0
  · subst h0
    rw [if_pos rfl, if_pos (by omega), revF_dig _ _ (by omega)]
    congr 1; omega
  · rw [if_neg h0]
    have e1 : ((2 * r).toUInt64).toNat = 2 * r := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    have e2 : ((64 - 2 * r).toUInt64).toNat = 2 * (32 - r) := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    by_cases h : r ≤ t + 7
    · rw [if_pos h, or_dig_l, shl_dig _ _ r _ e1 hr (by omega), if_pos h, revF_dig _ _ (by omega)]
      · congr 1; omega
      · rw [shr_dig _ _ (32 - r) _ e2 (by omega)]; exact dig_hi _ _ (by omega)
    · rw [if_neg h, or_dig_r, shr_dig _ _ (32 - r) _ e2 (by omega), revF_dig _ _ (by omega)]
      · congr 1; omega
      · rw [shl_dig _ _ r _ e1 hr (by omega), if_neg h]

theorem beCode_lt (w : Array UInt64) (s : Nat) : (beCode w s).toNat < 4 ^ 25 := by
  unfold beCode
  simp only []
  rw [UInt64.toNat_shiftRight, show (14 : UInt64).toNat % 64 = 14 from rfl, Nat.shiftRight_eq_div_pow]
  generalize (if s % 32 = 0 then _ else _ : UInt64) = x
  have := x.toNat_lt
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  exact Nat.lt_of_lt_of_le this (by decide)

theorem wN_dig (B : ByteArray) (i m t : Nat) (ht : t < m) : dig (wN B i m) t = c2N (B.get! (i + m - 1 - t)) := by
  induction m generalizing t with
  | zero => omega
  | succ m ih =>
    rw [wN_snoc]
    have hc := c2N_lt (B.get! (i + m))
    cases t with
    | zero => simp [dig]; omega
    | succ t =>
      rw [← dig_div4, show (wN B i m * 4 + c2N (B.get! (i + m))) / 4 = wN B i m by omega, ih t (by omega)]
      congr 2; omega

theorem eq_of_dig (n : Nat) : ∀ x y, x < 4 ^ n → y < 4 ^ n → (∀ t, t < n → dig x t = dig y t) → x = y := by
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy h
    have h0 := h 0 (by omega)
    simp only [dig, Nat.pow_zero, Nat.div_one] at h0
    have := ih (x / 4) (y / 4) (by rw [Nat.pow_succ] at hx; omega) (by rw [Nat.pow_succ] at hy; omega)
      (fun t ht => by rw [dig_div4, dig_div4]; exact h _ (by omega))
    omega

theorem seedHashK_eq (R : ByteArray) (s : Nat) : seedHashK R (packRP R) s = seedHashAt R s := by
  unfold seedHashK
  by_cases h : ((packRP R).ok && decide (s + q ≤ R.size)) = true
  · rw [if_pos h]
    rw [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hok, hs⟩ := h
    obtain ⟨hR, hP⟩ := packRP_ok R hok
    have hq : q = 25 := rfl
    rw [seedHashAt_spec, if_pos ((allACGT_word R s).2 (fun k hk => (hP (s + k) (by omega)).1))]
    unfold hashAt
    congr 2
    apply UInt64.toNat_inj.mp
    rw [hashWord_toNat, hq]
    apply eq_of_dig 25 _ _ (beCode_lt _ _) (wN_lt _ _ _)
    intro t ht
    rw [beCode_dig _ _ _ ht, wN_dig _ _ _ _ ht, show s + 25 - 1 - t = s + 24 - t by omega]
    have hj := (hP (s + 24 - t) (by omega)).2
    split
    · rw [show (s + 24 - t) / 32 = s / 32 by omega, show (s + 24 - t) % 32 = 24 - t + s % 32 by omega] at hj
      exact hj
    · rw [show (s + 24 - t) / 32 = s / 32 + 1 by omega, show (s + 24 - t) % 32 = s % 32 - 8 - t by omega] at hj
      exact hj
  · rw [if_neg h]

end MapSpec.Fast

#print axioms MapSpec.Fast.seedHashK_eq
