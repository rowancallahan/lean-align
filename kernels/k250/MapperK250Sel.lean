import MapperK250

/-!
# Selecting set fields

For `m : UInt64` whose 32 fields are `0` or `1` (`Bin`): `selLow m k` is the field
of the `k+1`-th lowest set field (`lowIdx`: `cnt64 (m ^^^ (m - 1)) − 1`, then clear the
lowest with `m &&& (m - 1)`), `selHigh m k` the `k+1`-th highest (`highIdx`: smear right
and count, then clear the highest).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- All 32 fields are `0` or `1`. -/
def Bin (m : UInt64) : Prop := ∀ t, t < 32 → dig m.toNat t ≤ 1

/-! ## Helpers: digits and counts -/

theorem dig_zero' (x : Nat) : dig x 0 = x % 4 := by simp [dig]

theorem dig_succ' (x q : Nat) : dig x (q + 1) = dig (x / 4) q := (dig_div4 x q).symm

theorem dig_of_zero (q : Nat) : dig 0 q = 0 := by simp [dig]

theorem xor_mod4 (a b : Nat) : (a ^^^ b) % 4 = a % 4 ^^^ b % 4 := Nat.xor_mod_two_pow (n := 2)
theorem xor_div4 (a b : Nat) : (a ^^^ b) / 4 = a / 4 ^^^ b / 4 := Nat.xor_div_two_pow (n := 2)
theorem and_mod4 (a b : Nat) : (a &&& b) % 4 = a % 4 &&& b % 4 := Nat.and_mod_two_pow (n := 2)
theorem and_div4 (a b : Nat) : (a &&& b) / 4 = a / 4 &&& b / 4 := Nat.and_div_two_pow (n := 2)

theorem cntNZ_succ_top (n x : Nat) :
    cntNZ (n + 1) x = cntNZ n x + (if dig x n = 0 then 0 else 1) := by
  induction n generalizing x with
  | zero => simp [cntNZ, dig]
  | succ n ih =>
    show (if x % 4 = 0 then 0 else 1) + cntNZ (n + 1) (x / 4) =
      ((if x % 4 = 0 then 0 else 1) + cntNZ n (x / 4)) + _
    rw [ih, dig_div4]; omega

theorem cntNZ_congrS (n : Nat) : ∀ x y, (∀ q < n, dig x q = dig y q) → cntNZ n x = cntNZ n y := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro x y h
    rw [cntNZ_succ_top, cntNZ_succ_top, ih x y (fun q hq => h q (by omega)), h n (by omega)]

theorem cntNZ_allzero (n x : Nat) (h : ∀ q < n, dig x q = 0) : cntNZ n x = 0 := by
  rw [cntNZ_congrS n x 0 (fun q hq => by rw [h q hq, dig_of_zero])]
  induction n with
  | zero => rfl
  | succ n ih => rw [cntNZ_succ_top, ih (fun q hq => h q (by omega))]; simp [dig_of_zero]

theorem cntNZ_clear (x y t : Nat) (hx : dig x t ≠ 0) (hy : dig y t = 0)
    (h : ∀ q, q ≠ t → dig x q = dig y q) (n : Nat) (ht : t < n) :
    cntNZ n x = cntNZ n y + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cntNZ_succ_top, cntNZ_succ_top]
    by_cases e : t = n
    · subst e
      rw [cntNZ_congrS t x y (fun q hq => h q (by omega)), if_neg hx, if_pos hy]
    · rw [ih (by omega), h n (Ne.symm e)]; omega

theorem exists_low (n : Nat) : ∀ x, cntNZ n x ≠ 0 →
    ∃ t < n, dig x t ≠ 0 ∧ ∀ q < t, dig x q = 0 := by
  induction n with
  | zero => intro x h; exact absurd rfl h
  | succ n ih =>
    intro x h
    by_cases h0 : x % 4 = 0
    · have h1 : cntNZ n (x / 4) ≠ 0 := by
        intro e; apply h; show (if x % 4 = 0 then 0 else 1) + cntNZ n (x / 4) = 0
        rw [if_pos h0, e]
      obtain ⟨t, ht, h2, h3⟩ := ih _ h1
      refine ⟨t + 1, by omega, by rw [dig_succ']; exact h2, ?_⟩
      intro q hq
      cases q with
      | zero => rw [dig_zero']; exact h0
      | succ q => rw [dig_succ']; exact h3 q (by omega)
    · exact ⟨0, by omega, by rw [dig_zero']; exact h0, fun q hq => by omega⟩

theorem exists_high (n : Nat) : ∀ x, cntNZ n x ≠ 0 →
    ∃ h < n, dig x h ≠ 0 ∧ ∀ q, h < q → q < n → dig x q = 0 := by
  induction n with
  | zero => intro x h; exact absurd rfl h
  | succ n ih =>
    intro x h
    by_cases h0 : dig x n = 0
    · rw [cntNZ_succ_top, if_pos h0] at h
      obtain ⟨t, ht, h2, h3⟩ := ih x (by omega)
      refine ⟨t, by omega, h2, fun q h4 h5 => ?_⟩
      by_cases e : q = n
      · subst e; exact h0
      · exact h3 q h4 (by omega)
    · exact ⟨n, by omega, h0, fun q h4 h5 => by omega⟩

/-! ## Lowest field -/

theorem low_nat (t : Nat) : ∀ x, dig x t = 1 → (∀ q < t, dig x q = 0) →
    (∀ n, t < n → cntNZ n (x ^^^ (x - 1)) = t + 1) ∧
      ∀ q, dig (x &&& (x - 1)) q = if q = t then 0 else dig x q := by
  induction t with
  | zero =>
    intro x hx _
    rw [dig_zero'] at hx
    have e1 : (x - 1) % 4 = 0 := by omega
    have e2 : (x - 1) / 4 = x / 4 := by omega
    refine ⟨fun n hn => ?_, fun q => ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      show (if (x ^^^ (x - 1)) % 4 = 0 then 0 else 1) + cntNZ n ((x ^^^ (x - 1)) / 4) = 1
      rw [xor_mod4, xor_div4, e1, e2, hx, Nat.xor_self,
        cntNZ_allzero n 0 (fun q _ => dig_of_zero q)]
      decide
    · cases q with
      | zero => rw [dig_zero', and_mod4, e1, hx]; rfl
      | succ q => rw [dig_succ', dig_succ', and_div4, e2, Nat.and_self]; simp
  | succ t ih =>
    intro x hx hlow
    have h0 : x % 4 = 0 := by have := hlow 0 (by omega); rwa [dig_zero'] at this
    rw [dig_succ'] at hx
    have hne : x / 4 ≠ 0 := by intro e; rw [e, dig_of_zero] at hx; omega
    obtain ⟨ih1, ih2⟩ := ih (x / 4) hx (fun q hq => by rw [← dig_succ']; exact hlow _ (by omega))
    have e1 : (x - 1) % 4 = 3 := by omega
    have e2 : (x - 1) / 4 = x / 4 - 1 := by omega
    refine ⟨fun n hn => ?_, fun q => ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      show (if (x ^^^ (x - 1)) % 4 = 0 then 0 else 1) + cntNZ n ((x ^^^ (x - 1)) / 4) = t + 1 + 1
      rw [xor_mod4, xor_div4, e1, e2, h0, ih1 n (by omega), if_neg (by decide)]
      omega
    · cases q with
      | zero => rw [dig_zero', and_mod4, e1, h0, dig_zero', h0]; rfl
      | succ q => rw [dig_succ', dig_succ', and_div4, e2, ih2 q]; simp

/-! ## Clearing a field by xor -/

theorem xor_pow_dig (h : Nat) : ∀ x q, dig (x ^^^ 4 ^ h) q = if q = h then dig x q ^^^ 1 else dig x q := by
  induction h with
  | zero =>
    intro x q
    cases q with
    | zero => rw [dig_zero', dig_zero', xor_mod4]; rfl
    | succ q => rw [dig_succ', dig_succ', xor_div4]; simp
  | succ h ih =>
    intro x q
    have a1 : 4 ^ (h + 1) % 4 = 0 := by rw [Nat.pow_succ]; simp
    have a2 : 4 ^ (h + 1) / 4 = 4 ^ h := by rw [Nat.pow_succ]; simp
    cases q with
    | zero => rw [dig_zero', dig_zero', xor_mod4, a1]; simp
    | succ q => rw [dig_succ', dig_succ', xor_div4, a2, ih]; simp

/-! ## Highest field: the smear -/

theorem testBit_dig (x q : Nat) :
    x.testBit (2 * q) = decide (dig x q % 2 = 1) ∧
      x.testBit (2 * q + 1) = decide (dig x q / 2 % 2 = 1) := by
  have e : (4 : Nat) ^ q = 2 ^ (2 * q) := by rw [Nat.pow_mul]
  refine ⟨?_, ?_⟩
  · rw [Nat.testBit_eq_decide_div_mod_eq, dig, e]
    congr 1; apply propext; omega
  · rw [Nat.testBit_eq_decide_div_mod_eq, dig, e, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    congr 1; apply propext; omega

theorem smear_step (x y c : Nat) (h : ∀ i, y.testBit i = true ↔ ∃ j, i ≤ j ∧ j < i + c ∧ x.testBit j = true) :
    ∀ i, (y ||| y >>> c).testBit i = true ↔ ∃ j, i ≤ j ∧ j < i + 2 * c ∧ x.testBit j = true := by
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true, h, h]
  constructor
  · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨j, h1, by omega, h3⟩
    · exact ⟨j, by omega, by omega, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    by_cases e : j < i + c
    · exact Or.inl ⟨j, h1, e, h3⟩
    · exact Or.inr ⟨j, by omega, by omega, h3⟩

theorem cnt_ones (t : Nat) : ∀ n, t < n → cntNZ n (2 * 4 ^ t - 1) = t + 1 := by
  induction t with
  | zero =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show (if (2 * 4 ^ 0 - 1) % 4 = 0 then 0 else 1) + cntNZ n ((2 * 4 ^ 0 - 1) / 4) = 1
    rw [cntNZ_allzero n _ (fun q _ => by simp [dig])]; decide
  | succ t ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show (if (2 * 4 ^ (t + 1) - 1) % 4 = 0 then 0 else 1) + cntNZ n ((2 * 4 ^ (t + 1) - 1) / 4) = t + 1 + 1
    have hp : 0 < 4 ^ t := Nat.pow_pos (by omega)
    rw [Nat.pow_succ, show (2 * (4 ^ t * 4) - 1) / 4 = 2 * 4 ^ t - 1 by omega,
      if_neg (by omega), ih n (by omega)]
    omega

theorem smear_cnt (x h s1 s2 s3 s4 s5 s6 : Nat) (e1 : s1 = x ||| x >>> 1) (e2 : s2 = s1 ||| s1 >>> 2)
    (e3 : s3 = s2 ||| s2 >>> 4) (e4 : s4 = s3 ||| s3 >>> 8) (e5 : s5 = s4 ||| s4 >>> 16)
    (e6 : s6 = s5 ||| s5 >>> 32) (hlt : x < 2 ^ 64) (hh : h < 32) (h1 : dig x h = 1)
    (hz : ∀ q, h < q → q < 32 → dig x q = 0) : cntNZ 32 s6 - 1 = h := by
  have s0 : ∀ i, x.testBit i = true ↔ ∃ j, i ≤ j ∧ j < i + 1 ∧ x.testBit j = true := by
    intro i; constructor
    · intro h; exact ⟨i, by omega, by omega, h⟩
    · rintro ⟨j, h1, h2, h3⟩; rwa [show i = j by omega]
  have t1 := smear_step x _ _ s0; rw [← e1] at t1
  have t2 := smear_step x _ _ t1; rw [← e2] at t2
  have t3 := smear_step x _ _ t2; rw [← e3] at t3
  have t4 := smear_step x _ _ t3; rw [← e4] at t4
  have t5 := smear_step x _ _ t4; rw [← e5] at t5
  have t6 := smear_step x _ _ t5; rw [← e6] at t6
  have top : x.testBit (2 * h) = true := by
    rw [(testBit_dig x h).1, h1]; rfl
  have above : ∀ j, 2 * h < j → x.testBit j = false := by
    intro j hj
    by_cases j64 : j < 64
    · obtain ⟨q, hq⟩ : ∃ q, j = 2 * q ∨ j = 2 * q + 1 := ⟨j / 2, by omega⟩
      rcases hq with rfl | rfl
      · rw [(testBit_dig x q).1, hz q (by omega) (by omega)]; rfl
      · by_cases e : q = h
        · subst e; rw [(testBit_dig x q).2, h1]; rfl
        · rw [(testBit_dig x q).2, hz q (by omega) (by omega)]; rfl
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
  have key : s6 = 2 * 4 ^ h - 1 := by
    rw [show 2 * 4 ^ h = 2 ^ (2 * h + 1) by rw [Nat.pow_succ, Nat.pow_mul, Nat.mul_comm]]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 2 * h + 1
    · rw [decide_eq_true hi]; exact (t6 i).2 ⟨2 * h, by omega, by omega, top⟩
    · rw [decide_eq_false hi]
      cases e : s6.testBit i
      · rfl
      · obtain ⟨j, j1, _, j3⟩ := (t6 i).1 e
        rw [above j (by omega)] at j3; exact absurd j3 (by decide)
  rw [key, cnt_ones h 32 hh]; omega

theorem highIdx_eq (m : UInt64) (h : Nat) (hh : h < 32) (h1 : dig m.toNat h = 1)
    (hz : ∀ q, h < q → q < 32 → dig m.toNat q = 0) : highIdx m = h := by
  simp only [highIdx]
  rw [cnt64_eq]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftRight]
  exact smear_cnt m.toNat h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl m.toNat_lt hh h1 hz


theorem cntNZ_top_zero (a x : Nat) (n : Nat) (han : a ≤ n) (h : ∀ q, a ≤ q → q < n → dig x q = 0) :
    cntNZ n x = cntNZ a x := by
  induction n with
  | zero => rw [show a = 0 by omega]
  | succ n ih =>
    by_cases e : a = n + 1
    · rw [e]
    · rw [cntNZ_succ_top, ih (by omega) (fun q h1 h2 => h q h1 (by omega)), if_pos (h n (by omega) (by omega))]
      rfl

theorem low_facts (m : UInt64) (hb : Bin m) (hk : cntNZ 32 m.toNat ≠ 0) :
    ∃ t < 32, dig m.toNat t = 1 ∧ (∀ q < t, dig m.toNat q = 0) ∧ lowIdx m = t ∧
      ∀ q, dig (m &&& (m - 1)).toNat q = if q = t then 0 else dig m.toNat q := by
  obtain ⟨t, ht, h1, h2⟩ := exists_low 32 m.toNat hk
  have h1' : dig m.toNat t = 1 := by have := hb t ht; omega
  have hne : m.toNat ≠ 0 := by intro e; rw [e, dig_of_zero] at h1; exact h1 rfl
  have hle : (1 : UInt64) ≤ m := by rw [UInt64.le_iff_toNat_le]; simp; omega
  obtain ⟨A, B⟩ := low_nat t m.toNat h1' h2
  refine ⟨t, ht, h1', h2, ?_, ?_⟩
  · simp only [lowIdx]
    rw [cnt64_eq, UInt64.toNat_xor, UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_one, A 32 ht]
    rfl
  · intro q
    rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_one, B]

theorem high_facts (m : UInt64) (hb : Bin m) (hk : cntNZ 32 m.toNat ≠ 0) :
    ∃ h < 32, dig m.toNat h = 1 ∧ (∀ q, h < q → q < 32 → dig m.toNat q = 0) ∧ highIdx m = h ∧
      ∀ q, dig (m ^^^ (1 <<< (2 * highIdx m).toUInt64)).toNat q =
        if q = h then 0 else dig m.toNat q := by
  obtain ⟨h, hh, h1, h2⟩ := exists_high 32 m.toNat hk
  have h1' : dig m.toNat h = 1 := by have := hb h hh; omega
  have hi := highIdx_eq m h hh h1' h2
  refine ⟨h, hh, h1', h2, hi, ?_⟩
  have e1 : ((1 : UInt64) <<< (2 * h).toUInt64).toNat = 4 ^ h := by
    rw [UInt64.toNat_shiftLeft]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.one_mul,
      UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt (show 2 * h < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 * h < 64 by omega),
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega)), Nat.pow_mul]
  intro q
  rw [hi, UInt64.toNat_xor, e1, xor_pow_dig]
  split
  · rename_i e; subst e; rw [h1']; rfl
  · rfl

/-- The `k+1`-th lowest set field. -/
theorem selLow_spec (m : UInt64) (hb : Bin m) (k : Nat) (hk : k < cntNZ 32 m.toNat) :
    selLow m k < 32 ∧ cntNZ (selLow m k) m.toNat = k ∧ dig m.toNat (selLow m k) = 1 := by
  induction k generalizing m with
  | zero =>
    obtain ⟨t, ht, h1, h2, hi, _⟩ := low_facts m hb (by omega)
    simp only [selLow, hi]
    exact ⟨ht, cntNZ_allzero t _ h2, h1⟩
  | succ k ih =>
    obtain ⟨t, ht, h1, h2, _, hd⟩ := low_facts m hb (by omega)
    simp only [selLow]
    have hb' : Bin (m &&& (m - 1)) := by
      intro q hq; rw [hd]; split
      · omega
      · exact hb q hq
    have hc := cntNZ_clear m.toNat (m &&& (m - 1)).toNat t (by omega) (by rw [hd, if_pos rfl])
      (fun q hq => by rw [hd, if_neg hq]) 32 ht
    obtain ⟨p1, p2, p3⟩ := ih _ hb' (by omega)
    generalize selLow (m &&& (m - 1)) k = p at p1 p2 p3
    have hpt : p ≠ t := by intro e; subst e; rw [hd, if_pos rfl] at p3; omega
    rw [hd, if_neg hpt] at p3
    have htp : t < p := by
      by_cases e : p < t
      · rw [h2 p e] at p3; omega
      · omega
    refine ⟨p1, ?_, p3⟩
    rw [cntNZ_clear m.toNat (m &&& (m - 1)).toNat t (by omega) (by rw [hd, if_pos rfl])
      (fun q hq => by rw [hd, if_neg hq]) p htp, p2]

/-- The `k+1`-th highest set field: `k` set fields above it. -/
theorem selHigh_spec (m : UInt64) (hb : Bin m) (k : Nat) (hk : k < cntNZ 32 m.toNat) :
    selHigh m k < 32 ∧ cntNZ (selHigh m k + 1) m.toNat + k = cntNZ 32 m.toNat ∧
      dig m.toNat (selHigh m k) = 1 := by
  induction k generalizing m with
  | zero =>
    obtain ⟨h, hh, h1, h2, hi, _⟩ := high_facts m hb (by omega)
    simp only [selHigh, hi]
    exact ⟨hh, by rw [cntNZ_top_zero (h + 1) _ 32 (by omega) (fun q a b => h2 q (by omega) b), Nat.add_zero], h1⟩
  | succ k ih =>
    obtain ⟨h, hh, h1, h2, _, hd⟩ := high_facts m hb (by omega)
    simp only [selHigh]
    generalize m ^^^ (1 <<< (2 * highIdx m).toUInt64) = m' at hd ⊢
    have hb' : Bin m' := by
      intro q hq; rw [hd]; split
      · omega
      · exact hb q hq
    have hc := cntNZ_clear m.toNat m'.toNat h (by omega) (by rw [hd, if_pos rfl])
      (fun q hq => by rw [hd, if_neg hq]) 32 hh
    obtain ⟨p1, p2, p3⟩ := ih _ hb' (by omega)
    generalize selHigh m' k = p at p1 p2 p3
    have hph : p ≠ h := by intro e; subst e; rw [hd, if_pos rfl] at p3; omega
    rw [hd, if_neg hph] at p3
    have hlt : p < h := by
      by_cases e : h < p
      · rw [h2 p e p1] at p3; omega
      · omega
    refine ⟨p1, ?_, p3⟩
    rw [cntNZ_congrS (p + 1) m.toNat m'.toNat (fun q hq => by rw [hd, if_neg (by omega)])]
    omega

end MapSpec.Fast
