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

/-! ## Unaligned 32-letter windows -/

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

/-! ## Packing -/

/-! ## Main theorems -/

end MapSpec.Packed
