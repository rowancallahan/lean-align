import MapperMzWords

/-!
2-bit packed genome and a word-level mismatch count.

* `packGenome G : Array UInt64`: 32 letters per word, letter `q` in bits
  `2·(q % 32), 2·(q % 32) + 1` of word `q / 32`, code A0 C1 G2 T3 (`byteCode`,
  any other byte 0).  `packGenome_ok : PackedOk G (packGenome G)`.
* `packAcgt G`: same layout, field 0 at A/C/G/T and 1 elsewhere; with
  `badCount` it counts the non-ACGT letters of a range (`badCount_eq`).
* `hamPacked pkG pkR p r len`: mismatches of `G[p, p+len)` against `R[r, r+len)`
  computed 32 letters at a time: unaligned 32-letter windows (two shifted
  words), XOR, fold of each 2-bit field to one bit `(x ||| x >>> 1) &&& 0x55…`,
  SWAR byte sums and `% 255`.  `hamPacked_eq`: under `PackedOk` for both and
  ACGT on both ranges it is the plain byte mismatch count
  `(List.range len).countP (fun i => G.get! (p+i) != R.get! (r+i))`.
-/

namespace MapSpec.Packed

open MapSpec MapSpec.Mz

/-! ## Nat layer: base-4 digits -/

/-- Number of nonzero base-4 digits among the first `n` of `x`. -/
def cntNZ : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => (if x % 4 = 0 then 0 else 1) + cntNZ n (x / 4)

/-- Sum of the first `n` base-`B` digits of `x`. -/
def dsum (B : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % B + dsum B n (x / B)

/-- The low `k` bits of each of the first `n` blocks of `2k` bits of `x`, in place. -/
def lowSum (k : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 ^ k + 2 ^ (2 * k) * lowSum k n (x / 2 ^ (2 * k))

/-- `n` copies of `c` in `k`-bit blocks. -/
def rep (k c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c + 2 ^ k * rep k c n

theorem and_split {j a b c d : Nat} (ha : a < 2 ^ j) (hc : c < 2 ^ j) :
    (2 ^ j * b + a) &&& (2 ^ j * d + c) = 2 ^ j * (b &&& d) + (a &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hc)]
  split <;> simp [Nat.testBit_and]

theorem and_rep (k n x : Nat) : x &&& rep (2 * k) (2 ^ k - 1) n = lowSum k n x := by
  induction n generalizing x with
  | zero => simp [rep, lowSum]
  | succ n ih =>
    have hk : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have h1 : x % 2 ^ (2 * k) < 2 ^ (2 * k) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have e : x = 2 ^ (2 * k) * (x / 2 ^ (2 * k)) + x % 2 ^ (2 * k) := (Nat.div_add_mod _ _).symm
    rw [rep, lowSum]
    conv => lhs; rw [e]
    rw [Nat.add_comm (2 ^ k - 1), and_split h1 (by omega), ih, Nat.and_two_pow_sub_one_eq_mod,
      Nat.add_comm, show 2 * k = k + k by omega, Nat.pow_add, Nat.mod_mul_right_mod]

theorem dsum_step {B d r : Nat} (n : Nat) (hd : d < B) :
    dsum B (n + 1) (d + B * r) = d + dsum B n r := by
  have hB : 0 < B := by omega
  rw [dsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ hB,
    Nat.div_eq_of_lt hd, Nat.zero_add]

theorem dsum_pair (k n x : Nat) (hk : 1 ≤ k) :
    dsum (2 ^ (2 * k)) n (lowSum k n x + lowSum k n (x / 2 ^ k)) = dsum (2 ^ k) (2 * n) x := by
  induction n generalizing x with
  | zero => simp [dsum]
  | succ n ih =>
    have hkk : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : 2 * 2 ^ k ≤ 2 ^ (2 * k) := by
      rw [hkk]; exact Nat.mul_le_mul_right _ (by
        have := Nat.pow_le_pow_right (show 0 < 2 by omega) hk; simpa using this)
    have hm1 := Nat.mod_lt x (Nat.two_pow_pos k)
    have hm2 := Nat.mod_lt (x / 2 ^ k) (Nat.two_pow_pos k)
    have hdiv : x / 2 ^ k / 2 ^ (2 * k) = x / 2 ^ (2 * k) / 2 ^ k := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [lowSum, lowSum, show ∀ a b c d : Nat, a + 2 ^ (2 * k) * b + (c + 2 ^ (2 * k) * d) =
        (a + c) + 2 ^ (2 * k) * (b + d) from fun _ _ _ _ => by rw [Nat.mul_add]; omega,
      dsum_step _ (by omega), hdiv, ih, show 2 * (n + 1) = (2 * n + 1) + 1 by omega, dsum, dsum,
      Nat.div_div_eq_div_mul, ← hkk, Nat.add_assoc]

/-- `x ≡ (digit sum) mod (B - 1)`. -/
theorem dsum_mod (B n x : Nat) (hB : 2 ≤ B) (hx : x < B ^ n) : x % (B - 1) = dsum B n x % (B - 1) := by
  induction n generalizing x with
  | zero => simp at hx; subst hx; simp [dsum]
  | succ n ih =>
    have hq : x / B < B ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← Nat.pow_succ]
    rw [dsum, Nat.add_mod (x % B), ← ih _ hq, ← Nat.add_mod]
    conv => lhs; rw [← Nat.mod_add_div x B]
    have : B * (x / B) = (B - 1) * (x / B) + x / B := by
      rw [← Nat.succ_mul, show (B - 1).succ = B by omega]
    rw [this, ← Nat.add_assoc, Nat.add_comm _ (x / B), ← Nat.add_assoc, Nat.add_mul_mod_self_left,
      Nat.add_comm]

theorem cntNZ_le (n x : Nat) : cntNZ n x ≤ n := by
  induction n generalizing x with
  | zero => simp [cntNZ]
  | succ n ih => have := ih (x / 4); simp only [cntNZ]; split <;> omega

/-- The fold `(x ||| x >>> 1) &&& 0x55…` has base-4 digit sum `cntNZ`. -/
theorem dsum_fold (n x : Nat) : dsum 4 n (lowSum 1 n (x ||| x >>> 1)) = cntNZ n x := by
  induction n generalizing x with
  | zero => simp [dsum, cntNZ]
  | succ n ih =>
    have hd : (x ||| x >>> 1) % 2 ^ 1 < 4 := by have := Nat.mod_lt (x ||| x >>> 1) (show 0 < 2 ^ 1 by decide); omega
    rw [lowSum, show 2 * 1 = 2 by rfl, show (2 : Nat) ^ 2 = 4 by rfl, dsum_step _ hd, cntNZ]
    have e1 : (x ||| x >>> 1) / 4 = x / 4 ||| (x / 4) >>> 1 := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_or_distrib, ← Nat.shiftRight_add, ← Nat.shiftRight_add]
    rw [e1, ih]
    congr 1
    rw [Nat.or_mod_two_pow, Nat.shiftRight_eq_div_pow]
    have a1 : x % 2 ^ 1 = x % 4 % 2 := by
      rw [show (4 : Nat) = 2 * 2 by rfl, Nat.mod_mul_right_mod]
    have a2 : x / 2 ^ 1 % 2 ^ 1 = x % 4 / 2 := by
      rw [show (4 : Nat) = 2 * 2 by rfl, Nat.mod_mul_right_div_self]
    rw [a1, a2]
    have : x % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize x % 4 = d at this ⊢
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h <;> decide

/-! ## Counting over a range -/

/-- Number of `q ∈ [i, i + n)` with `P q`. -/
def cntRange (P : Nat → Bool) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if P i then 1 else 0) + cntRange P (i + 1) n

theorem cntRange_add (P : Nat → Bool) (i a b : Nat) :
    cntRange P i (a + b) = cntRange P i a + cntRange P (i + a) b := by
  induction a generalizing i with
  | zero => simp [cntRange]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, cntRange, cntRange, ih,
      show i + 1 + a = i + (a + 1) by omega]
    omega

theorem cntRange_congr {P Q : Nat → Bool} {i n : Nat} (h : ∀ q, i ≤ q → q < i + n → P q = Q q) :
    cntRange P i n = cntRange Q i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [cntRange, cntRange, h i (by omega) (by omega),
      ih (fun q h1 h2 => h q (by omega) (by omega))]

theorem cntRange_eq_countP (P : Nat → Bool) (n : Nat) :
    cntRange P 0 n = (List.range n).countP P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntRange_add, ih, List.range_succ, List.countP_append]
    simp [cntRange]

/-! ## Mismatching digits -/

/-- Base-4 digit `i` of `x`. -/
def dig (x i : Nat) : Nat := x / 4 ^ i % 4

theorem dig_div4 (x i : Nat) : dig (x / 4) i = dig x (i + 1) := by
  simp only [dig, Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem xor_mod4_eq_zero (u v : Nat) : (u ^^^ v) % 4 = 0 ↔ u % 4 = v % 4 := by
  rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.xor_mod_two_pow]
  have hu : u % 2 ^ 2 < 4 := Nat.mod_lt _ (by decide)
  have hv : v % 2 ^ 2 < 4 := Nat.mod_lt _ (by decide)
  generalize u % 2 ^ 2 = a at hu ⊢
  generalize v % 2 ^ 2 = b at hv ⊢
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with h | h | h | h <;> subst h <;>
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with h | h | h | h <;> subst h <;> decide

/-- Nonzero digits of `A ^^^ B` = positions where the digits differ. -/
theorem cntNZ_xor (f g : Nat → Nat) (n : Nat) : ∀ (A B i : Nat),
    (∀ j < n, dig A j = f (i + j)) → (∀ j < n, dig B j = g (i + j)) →
    cntNZ n (A ^^^ B) = cntRange (fun q => f q != g q) i n := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B i hA hB
    rw [cntNZ, cntRange, show (4 : Nat) = 2 ^ 2 by rfl, Nat.xor_div_two_pow,
      ← show (4 : Nat) = 2 ^ 2 by rfl,
      ih (A / 4) (B / 4) (i + 1) (fun j hj => by rw [dig_div4, hA _ (by omega)]; congr 1; omega)
        (fun j hj => by rw [dig_div4, hB _ (by omega)]; congr 1; omega)]
    congr 1
    have h1 := hA 0 (by omega); have h2 := hB 0 (by omega)
    simp only [dig, Nat.pow_zero, Nat.div_one, Nat.add_zero] at h1 h2
    by_cases h : f i = g i
    · rw [if_pos ((xor_mod4_eq_zero A B).2 (by rw [h1, h2, h])), if_neg (by simp [h])]
    · rw [if_neg (fun e => h (by rw [← h1, ← h2]; exact (xor_mod4_eq_zero A B).1 e)),
        if_pos (by simp [h])]

/-- Masking to the low `m` digits. -/
theorem cntNZ_mod (m : Nat) : ∀ (n x : Nat), m ≤ n → cntNZ n (x % 4 ^ m) = cntNZ m x := by
  induction m with
  | zero =>
    intro n x _
    simp only [Nat.pow_zero, Nat.mod_one, cntNZ]
    induction n with
    | zero => rfl
    | succ n ih => simp [cntNZ, ih (Nat.zero_le _)]
  | succ m ih =>
    intro n x h
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [cntNZ, cntNZ, Nat.pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self,
      ih n _ (by omega)]

/-! ## Unaligned 32-letter windows -/

/-- Field (2-bit letter code) of position `q` of a packed array. -/
def fld (pk : Array UInt64) (q : Nat) : Nat := (pk.getD (q / 32) 0).toNat / 4 ^ (q % 32) % 4

/-- The 32 letters `[p, p + 32)` of a packed array, letter `p` in the low bits. -/
@[inline] def win (pk : Array UInt64) (p : Nat) : UInt64 :=
  let s := p % 32
  let a := pk.getD (p / 32) 0
  if s = 0 then a else (a >>> (2 * s).toUInt64) + (pk.getD (p / 32 + 1) 0 <<< (64 - 2 * s).toUInt64)

theorem div_mod4_drop (u c i : Nat) : (u + 4 ^ (i + 1) * c) / 4 ^ i % 4 = u / 4 ^ i % 4 := by
  rw [Nat.pow_succ, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.add_mul_mod_self_left]

theorem win_nat (A B s t i : Nat) (hA : A < 4 ^ (s + t)) (hi : i < s + t) :
    (A / 4 ^ s + B * 4 ^ t % 4 ^ (s + t)) % 4 ^ (s + t) / 4 ^ i % 4 =
      if i < t then A / 4 ^ (s + i) % 4 else B / 4 ^ (i - t) % 4 := by
  have p4 : ∀ k, 0 < 4 ^ k := fun k => Nat.pow_pos (by decide)
  rw [Nat.pow_add, Nat.mul_mod_mul_right]
  have hu : A / 4 ^ s < 4 ^ t := by
    rw [Nat.div_lt_iff_lt_mul (p4 s), Nat.mul_comm, ← Nat.pow_add]; exact hA
  have hv : B % 4 ^ s < 4 ^ s := Nat.mod_lt _ (p4 s)
  have hsum : A / 4 ^ s + B % 4 ^ s * 4 ^ t < 4 ^ s * 4 ^ t := by
    have : (B % 4 ^ s + 1) * 4 ^ t ≤ 4 ^ s * 4 ^ t := Nat.mul_le_mul_right _ hv
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [Nat.mod_eq_of_lt hsum]
  split
  · rename_i hit
    have e : 4 ^ t = 4 ^ (i + 1) * 4 ^ (t - (i + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, show B % 4 ^ s * (4 ^ (i + 1) * 4 ^ (t - (i + 1))) =
        4 ^ (i + 1) * (B % 4 ^ s * 4 ^ (t - (i + 1))) by
        rw [Nat.mul_comm, Nat.mul_assoc, Nat.mul_comm (4 ^ _) (B % _)],
      div_mod4_drop, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  · rename_i hit
    have e : 4 ^ i = 4 ^ t * 4 ^ (i - t) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm (B % _), Nat.add_mul_div_left _ _ (p4 t),
      Nat.div_eq_of_lt hu, Nat.zero_add]
    have e2 : 4 ^ s = 4 ^ (i - t) * (4 * 4 ^ (s - (i - t) - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    rw [e2, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem win_dig (pk : Array UInt64) (p i : Nat) (hi : i < 32) :
    dig (win pk p).toNat i = fld pk (p + i) := by
  simp only [win, dig, fld]
  split
  · rename_i hs
    rw [show (p + i) / 32 = p / 32 by omega, show (p + i) % 32 = i by omega]
  · rename_i hs
    have hA := (pk.getD (p / 32) 0).toNat_lt
    have hs2 : 2 * (p % 32) < 64 := by omega
    rw [UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show 2 * (p % 32) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - 2 * (p % 32) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hs2, Nat.mod_eq_of_lt (show 64 - 2 * (p % 32) < 64 by omega)]
    have e4 : ∀ k, (2 : Nat) ^ (2 * k) = 4 ^ k := fun k => by rw [Nat.pow_mul]
    rw [e4, show 64 - 2 * (p % 32) = 2 * (32 - p % 32) by omega, e4,
      show (2 : Nat) ^ 64 = 4 ^ (p % 32 + (32 - p % 32)) by
        rw [show p % 32 + (32 - p % 32) = 32 by omega],
      win_nat _ _ _ _ _ (by rw [show p % 32 + (32 - p % 32) = 32 by omega]; exact hA)
        (by omega)]
    split
    · rw [show (p + i) / 32 = p / 32 by omega, show (p + i) % 32 = p % 32 + i by omega]
    · rw [show (p + i) / 32 = p / 32 + 1 by omega,
        show (p + i) % 32 = i - (32 - p % 32) by omega]

/-! ## Word mismatch count (fold + SWAR popcount) -/

/-- Number of nonzero 2-bit fields of `x`. -/
@[inline] def cnt64 (x : UInt64) : Nat :=
  let t := (x ||| x >>> 1) &&& (0x5555555555555555 : UInt64)
  let a := (t &&& (0x3333333333333333 : UInt64)) + (t >>> 2 &&& (0x3333333333333333 : UInt64))
  let b := (a &&& (0x0f0f0f0f0f0f0f0f : UInt64)) + (a >>> 4 &&& (0x0f0f0f0f0f0f0f0f : UInt64))
  (b % 255).toNat

theorem cnt64_eq (x : UInt64) : cnt64 x = cntNZ 32 x.toNat := by
  have m1 : (0x5555555555555555 : UInt64).toNat = rep (2 * 1) (2 ^ 1 - 1) 32 := by decide
  have m2 : (0x3333333333333333 : UInt64).toNat = rep (2 * 2) (2 ^ 2 - 1) 16 := by decide
  have m3 : (0x0f0f0f0f0f0f0f0f : UInt64).toNat = rep (2 * 4) (2 ^ 4 - 1) 8 := by decide
  have k2 : (0x3333333333333333 : UInt64).toNat = 0x3333333333333333 := rfl
  have k3 : (0x0f0f0f0f0f0f0f0f : UInt64).toNat = 0x0f0f0f0f0f0f0f0f := rfl
  simp only [cnt64]
  generalize ht : (x ||| x >>> 1) &&& 0x5555555555555555 = t
  generalize ha : (t &&& (0x3333333333333333 : UInt64)) + (t >>> 2 &&& (0x3333333333333333 : UInt64)) = a
  generalize hb : (a &&& (0x0f0f0f0f0f0f0f0f : UInt64)) + (a >>> 4 &&& (0x0f0f0f0f0f0f0f0f : UInt64)) = b
  have ht' : t.toNat = lowSum 1 32 (x.toNat ||| x.toNat >>> 1) := by
    rw [← ht, UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_shiftRight, m1, and_rep]; rfl
  have ha' : a.toNat = lowSum 2 16 t.toNat + lowSum 2 16 (t.toNat / 2 ^ 2) := by
    rw [← ha, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight]
    have b1 : t.toNat &&& (0x3333333333333333 : UInt64).toNat ≤ 0x3333333333333333 :=
      k2 ▸ Nat.and_le_right
    have b2 : t.toNat >>> ((2 : UInt64).toNat % 64) &&& (0x3333333333333333 : UInt64).toNat ≤
      0x3333333333333333 := k2 ▸ Nat.and_le_right
    rw [Nat.mod_eq_of_lt (by omega), m2, and_rep, and_rep, Nat.shiftRight_eq_div_pow]; rfl
  have hb' : b.toNat = lowSum 4 8 a.toNat + lowSum 4 8 (a.toNat / 2 ^ 4) := by
    rw [← hb, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight]
    have b1 : a.toNat &&& (0x0f0f0f0f0f0f0f0f : UInt64).toNat ≤ 0x0f0f0f0f0f0f0f0f :=
      k3 ▸ Nat.and_le_right
    have b2 : a.toNat >>> ((4 : UInt64).toNat % 64) &&& (0x0f0f0f0f0f0f0f0f : UInt64).toNat ≤
      0x0f0f0f0f0f0f0f0f := k3 ▸ Nat.and_le_right
    rw [Nat.mod_eq_of_lt (by omega), m3, and_rep, and_rep, Nat.shiftRight_eq_div_pow]; rfl
  have d1 := dsum_pair 4 8 a.toNat (by omega)
  have d2 := dsum_pair 2 16 t.toNat (by omega)
  have d3 := dsum_fold 32 x.toNat
  simp only [Nat.reduceMul, Nat.reducePow] at d1 d2 ha' hb'
  rw [← hb'] at d1
  rw [← ha'] at d2
  rw [← ht'] at d3
  have hB := b.toNat_lt
  rw [UInt64.toNat_mod, show (255 : UInt64).toNat = 256 - 1 from rfl,
    dsum_mod 256 8 b.toNat (by decide) hB, d1, d2, d3]
  exact Nat.mod_eq_of_lt (by have := cntNZ_le 32 x.toNat; omega)

theorem toNat_mask (x : UInt64) (m : Nat) (hm : m < 32) :
    (x &&& ((1 <<< (2 * m).toUInt64) - 1)).toNat = x.toNat % 4 ^ m := by
  have h1 : ((1 : UInt64) <<< (2 * m).toUInt64).toNat = 2 ^ (2 * m) := by
    rw [UInt64.toNat_shiftLeft]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.one_mul,
      UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt (show 2 * m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 * m < 64 by omega),
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  have hle : (1 : UInt64) ≤ 1 <<< (2 * m).toUInt64 := by
    rw [UInt64.le_iff_toNat_le, h1]; exact Nat.one_le_two_pow
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ hle, h1, UInt64.toNat_one,
    Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul]

/-! ## The packed mismatch count -/

/-- Mismatches of `[p, p + len)` of `pkG` against `[r, r + len)` of `pkR`, 32 letters per step. -/
def hamPacked (pkG pkR : Array UInt64) (p r len : Nat) : Nat := go 0 0
where
  go (i acc : Nat) : Nat :=
    if i < len then
      let x := win pkG (p + i) ^^^ win pkR (r + i)
      let y := if len - i < 32 then x &&& ((1 <<< (2 * (len - i)).toUInt64) - 1) else x
      go (i + 32) (acc + cnt64 y)
    else acc
  termination_by len - i

/-- One chunk: the count of the (masked) XOR of two windows. -/
theorem chunk_eq (pkG pkR : Array UInt64) (p r i c : Nat) (hc : c ≤ 32) (x : UInt64)
    (hx : x = win pkG (p + i) ^^^ win pkR (r + i)) :
    cntNZ c x.toNat = cntRange (fun q => fld pkG (p + q) != fld pkR (r + q)) i c := by
  rw [hx, UInt64.toNat_xor]
  exact cntNZ_xor _ _ c _ _ i
    (fun j hj => by rw [win_dig _ _ _ (by omega), Nat.add_assoc])
    (fun j hj => by rw [win_dig _ _ _ (by omega), Nat.add_assoc])

theorem hamPacked_go (pkG pkR : Array UInt64) (p r len : Nat) (i acc : Nat) :
    hamPacked.go pkG pkR p r len i acc =
      acc + cntRange (fun q => fld pkG (p + q) != fld pkR (r + q)) i (len - i) := by
  rw [hamPacked.go]
  split
  · rename_i hi
    rw [hamPacked_go pkG pkR p r len (i + 32), Nat.add_assoc]
    congr 1
    split
    · rename_i hm
      rw [cnt64_eq, toNat_mask _ _ hm, cntNZ_mod _ _ _ (by omega),
        chunk_eq pkG pkR p r i _ (by omega) _ rfl, show len - (i + 32) = 0 by omega]
      rfl
    · rename_i hm
      rw [cnt64_eq, chunk_eq pkG pkR p r i _ (by omega) _ rfl,
        show len - i = 32 + (len - (i + 32)) by omega, cntRange_add]
  · rw [show len - i = 0 by omega]; rfl
termination_by len - i

/-- Field-level meaning, with no hypotheses. -/
theorem hamPacked_fields (pkG pkR : Array UInt64) (p r len : Nat) :
    hamPacked pkG pkR p r len = cntRange (fun q => fld pkG (p + q) != fld pkR (r + q)) 0 len := by
  rw [hamPacked, hamPacked_go]; simp

/-! ## Packing -/

/-- Every ACGT position `q` of `G` holds its code in field `q` of `pk`. -/
def PackedOk (G : ByteArray) (pk : Array UInt64) : Prop :=
  ∀ q < G.size, acgt (G.get! q) = true → fld pk q = byteCode (G.get! q)

/-- `G[b]`, or `0` past the end (no out-of-bounds panic). -/
@[inline] def byteAt (G : ByteArray) (b : Nat) : UInt8 := if b < G.size then G.get! b else 0

/-- `f` of the `n` bytes `G[b, b + n)`, first in the low bits. -/
def packW (f : UInt8 → Nat) (G : ByteArray) (b : Nat) : Nat → UInt64
  | 0 => 0
  | n + 1 => (f (byteAt G b)).toUInt64 + (packW f G (b + 1) n <<< 2)

def packN (f : UInt8 → Nat) (G : ByteArray) (b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f (byteAt G b) + 4 * packN f G (b + 1) n

theorem packN_lt (f : UInt8 → Nat) (hf : ∀ c, f c < 4) (G : ByteArray) (n : Nat) :
    ∀ b, packN f G b n < 4 ^ n := by
  induction n with
  | zero => intro; simp [packN]
  | succ n ih => intro b; have := ih (b + 1); have := hf (byteAt G b); rw [packN, Nat.pow_succ]; omega

theorem packW_toNat (f : UInt8 → Nat) (hf : ∀ c, f c < 4) (G : ByteArray) (n : Nat) (hn : n ≤ 32) :
    ∀ b, (packW f G b n).toNat = packN f G b n := by
  induction n with
  | zero => intro; rfl
  | succ n ih =>
    intro b
    have h1 := ih (by omega) (b + 1)
    have h2 := packN_lt f hf G n (b + 1)
    have h3 := hf (byteAt G b)
    have h4 : 4 ^ n ≤ 4 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
    have h5 : packN f G (b + 1) n < 4 ^ 31 := Nat.lt_of_lt_of_le h2 h4
    rw [packW, packN, UInt64.toNat_add, UInt64.toNat_shiftLeft, h1]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
    have e : (2 : Nat) ^ 64 = 4 * 4 ^ 31 := rfl
    have e2 : (2 : UInt64).toNat % 64 = 2 := rfl
    rw [e2, e]
    simp only [Nat.reducePow, Nat.reduceMul] at h5 ⊢
    rw [Nat.mod_eq_of_lt (show f (byteAt G b) < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show packN f G (b + 1) n * 4 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem dig_packN (f : UInt8 → Nat) (hf : ∀ c, f c < 4) (G : ByteArray) (n : Nat) :
    ∀ b i, i < n → dig (packN f G b n) i = f (byteAt G (b + i)) := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro b i hi
    have h3 := hf (byteAt G b)
    cases i with
    | zero => simp only [dig, packN, Nat.pow_zero, Nat.div_one, Nat.add_zero]; omega
    | succ i =>
      rw [← dig_div4, packN, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h3,
        Nat.zero_add, ih _ _ (by omega), show b + 1 + i = b + (i + 1) by omega]

/-- Pack `f` of every byte of `G`, 32 per word. -/
def packWith (f : UInt8 → Nat) (G : ByteArray) : Array UInt64 :=
  Array.ofFn (n := G.size / 32 + 1) fun w => packW f G (32 * w.val) 32

theorem fld_packWith (f : UInt8 → Nat) (hf : ∀ c, f c < 4) (G : ByteArray) (q : Nat)
    (hq : q < G.size) : fld (packWith f G) q = f (G.get! q) := by
  have hw : q / 32 < (packWith f G).size := by simp [packWith]; omega
  have e : (packWith f G).getD (q / 32) 0 = packW f G (32 * (q / 32)) 32 := by
    simp [packWith] at hw
    simp [packWith, Array.getD_eq_getD_getElem?, hw]
  simp only [fld, e]
  rw [packW_toNat f hf G 32 (by omega), show packN f G (32 * (q / 32)) 32 / 4 ^ (q % 32) % 4 =
    dig (packN f G (32 * (q / 32)) 32) (q % 32) from rfl, dig_packN f hf G 32 _ _ (by omega), byteAt, if_pos (by omega)]
  congr; omega

/-- The 2-bit genome: A0 C1 G2 T3, anything else 0. -/
def packGenome (G : ByteArray) : Array UInt64 := packWith byteCode G

theorem packGenome_ok (G : ByteArray) : PackedOk G (packGenome G) :=
  fun q hq _ => fld_packWith byteCode byteCode_lt G q hq

/-- `0` at A/C/G/T, `1` elsewhere. -/
@[inline] def badCode (b : UInt8) : Nat := if acgt b then 0 else 1

/-- Non-ACGT mask, same layout as `packGenome`. -/
def packAcgt (G : ByteArray) : Array UInt64 := packWith badCode G

/-- Number of non-ACGT letters in `G[p, p + len)`, from `am = packAcgt G`. -/
def badCount (am : Array UInt64) (p len : Nat) : Nat := hamPacked am #[] p 0 len

/-- `G[p, p + len)` is all ACGT. -/
def allAcgt (am : Array UInt64) (p len : Nat) : Bool := badCount am p len == 0

/-! ## Main theorems -/

/-- The packed count is the plain byte mismatch count. -/
theorem hamPacked_eq (G R : ByteArray) (pkG pkR : Array UInt64) (p r len : Nat)
    (hG : PackedOk G pkG) (hR : PackedOk R pkR)
    (hpG : p + len ≤ G.size) (hrR : r + len ≤ R.size)
    (aG : ∀ i < len, acgt (G.get! (p + i)) = true) (aR : ∀ i < len, acgt (R.get! (r + i)) = true) :
    hamPacked pkG pkR p r len =
      (List.range len).countP (fun i => G.get! (p + i) != R.get! (r + i)) := by
  rw [hamPacked_fields, ← cntRange_eq_countP]
  apply cntRange_congr
  intro q _ hq
  rw [hG _ (by omega) (aG q (by omega)), hR _ (by omega) (aR q (by omega))]
  by_cases h : G.get! (p + q) = R.get! (r + q)
  · simp [h]
  · have : byteCode (G.get! (p + q)) ≠ byteCode (R.get! (r + q)) :=
      fun e => h (byteCode_inj _ _ (aG q (by omega)) (aR q (by omega)) e)
    rw [(bne_iff_ne).2 this, (bne_iff_ne).2 h]

/-- On the packed genomes themselves. -/
theorem hamPacked_packGenome (G R : ByteArray) (p r len : Nat)
    (hpG : p + len ≤ G.size) (hrR : r + len ≤ R.size)
    (aG : ∀ i < len, acgt (G.get! (p + i)) = true) (aR : ∀ i < len, acgt (R.get! (r + i)) = true) :
    hamPacked (packGenome G) (packGenome R) p r len =
      (List.range len).countP (fun i => G.get! (p + i) != R.get! (r + i)) :=
  hamPacked_eq G R _ _ p r len (packGenome_ok G) (packGenome_ok R) hpG hrR aG aR

theorem badCount_eq (G : ByteArray) (p len : Nat) (hp : p + len ≤ G.size) :
    badCount (packAcgt G) p len = (List.range len).countP (fun i => !acgt (G.get! (p + i))) := by
  rw [badCount, hamPacked_fields, ← cntRange_eq_countP]
  apply cntRange_congr
  intro q _ hq
  have h0 : fld (#[] : Array UInt64) (0 + q) = 0 := by simp [fld, Array.getD]
  rw [h0, packAcgt, fld_packWith badCode (fun c => by unfold badCode; split <;> omega) G _ (by omega)]
  unfold badCode; split <;> simp_all

theorem allAcgt_iff (G : ByteArray) (p len : Nat) (hp : p + len ≤ G.size) :
    allAcgt (packAcgt G) p len = true ↔ ∀ i < len, acgt (G.get! (p + i)) = true := by
  rw [allAcgt, beq_iff_eq, badCount_eq G p len hp, List.countP_eq_zero]
  simp

end MapSpec.Packed
