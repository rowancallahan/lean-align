import MapperBytes

/-!
Byte-level word codes and the multiplicative hash used by the minimizer
index (`codecs/MzIndex.lean`).

* `wc B i n`: base-4 code (A0 C1 G2 T3, `byteCode`) of `B[i, i+n)`, first
  letter most significant; splitting (`wc_add`, `wc_div`, `wc_mod`) and
  "equal codes of ACGT words ⇒ equal bytes" (`eq_of_wc`).
* `hashU x m = ((x * HC) mod 2^64) &&& m`; with `m = 2^(2k) - 1` it is
  `x * HC mod 4^k`, a bijection on `[0, 4^k)` (`hash_inj`, via the inverse
  of the odd constant `HC` mod `2^64`).
* Executable loops (`wcGo`, `allA`, `eqRun`, `firstOdd`) with their meaning.
-/

namespace MapSpec.Mz

/-! ## Letters -/

/-- A, C, G or T. -/
@[inline] def acgt (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

theorem byteCode_lt (b : UInt8) : byteCode b < 4 := codeNat_lt _

theorem byteCode_inj (a b : UInt8) (ha : acgt a = true) (hb : acgt b = true)
    (h : byteCode a = byteCode b) : a = b := by
  simp only [acgt, Bool.or_eq_true, beq_iff_eq] at ha hb
  rcases ha with ((rfl | rfl) | rfl) | rfl <;> rcases hb with ((rfl | rfl) | rfl) | rfl <;>
    first | rfl | (simp [byteCode, codeNat] at h)

/-! ## Word codes -/

/-- Base-4 code of `B[i, i+n)`, first letter most significant. -/
def wc (B : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wc B i n * 4 + byteCode (B.get! (i + n))

theorem wc_lt (B : ByteArray) (i n : Nat) : wc B i n < 4 ^ n := by
  induction n with
  | zero => simp [wc]
  | succ n ih =>
    have := byteCode_lt (B.get! (i + n))
    rw [wc, Nat.pow_succ]; omega

theorem wc_add (B : ByteArray) (i m n : Nat) : wc B i (m + n) = wc B i m * 4 ^ n + wc B (i + m) n := by
  induction n with
  | zero => simp [wc]
  | succ n ih =>
    rw [← Nat.add_assoc, wc, ih, wc, Nat.pow_succ, Nat.add_assoc i m n]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem wc_div (B : ByteArray) (i m n : Nat) : wc B i (m + n) / 4 ^ n = wc B i m := by
  rw [wc_add, Nat.mul_comm, Nat.mul_add_div (Nat.pow_pos (by omega)),
    Nat.div_eq_of_lt (wc_lt B _ n), Nat.add_zero]

theorem wc_mod (B : ByteArray) (i m n : Nat) : wc B i (m + n) % 4 ^ n = wc B (i + m) n := by
  rw [wc_add, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (wc_lt B _ n)]

theorem wc_congr (B C : ByteArray) (i j n : Nat) (h : ∀ t < n, B.get! (i + t) = C.get! (j + t)) :
    wc B i n = wc C j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wc, wc, ih (fun t ht => h t (by omega)), h n (by omega)]

/-- Equal codes of two ACGT words: equal bytes. -/
theorem eq_of_wc (B C : ByteArray) (i j n : Nat)
    (hB : ∀ t < n, acgt (B.get! (i + t)) = true) (hC : ∀ t < n, acgt (C.get! (j + t)) = true)
    (h : wc B i n = wc C j n) : ∀ t < n, B.get! (i + t) = C.get! (j + t) := by
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    rw [wc, wc] at h
    have h1 := byteCode_lt (B.get! (i + n))
    have h2 := byteCode_lt (C.get! (j + n))
    have hl : byteCode (B.get! (i + n)) = byteCode (C.get! (j + n)) := by omega
    have hr : wc B i n = wc C j n := by omega
    intro t ht
    by_cases htn : t = n
    · subst htn; exact byteCode_inj _ _ (hB t (by omega)) (hC t (by omega)) hl
    · exact ih (fun t ht => hB t (by omega)) (fun t ht => hC t (by omega)) hr t (by omega)

/-! ## Executable loops -/

/-- `x · 4^(stop-i) + wc B i (stop - i)`, tail-recursive. -/
def wcGo (B : ByteArray) (i stop x : Nat) : Nat :=
  if i < stop then wcGo B (i + 1) stop (x * 4 + byteCode (B.get! i)) else x
termination_by stop - i

theorem wcGo_eq (B : ByteArray) (n : Nat) : ∀ i x, wcGo B i (i + n) x = x * 4 ^ n + wc B i n := by
  induction n with
  | zero => intro i x; rw [wcGo]; simp [wc]
  | succ n ih =>
    intro i x
    rw [wcGo, if_pos (by omega), show i + (n + 1) = (i + 1) + n by omega, ih]
    have := wc_add B i 1 n
    have h1 : wc B i 1 = byteCode (B.get! i) := by simp [wc]
    rw [Nat.add_comm 1 n, h1] at this
    rw [this, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm 4]

theorem wcGo_zero' (B : ByteArray) (i j : Nat) (h : i ≤ j) : wcGo B i j 0 = wc B i (j - i) := by
  have := wcGo_eq B (j - i) i 0
  rw [show i + (j - i) = j by omega] at this
  rw [this]; simp

/-- Every byte of `B[i, stop)` is A, C, G or T. -/
def allA (B : ByteArray) (i stop : Nat) : Bool :=
  if i < stop then acgt (B.get! i) && allA B (i + 1) stop else true
termination_by stop - i

theorem allA_iff (B : ByteArray) (n : Nat) :
    ∀ i, allA B i (i + n) = true ↔ ∀ t < n, acgt (B.get! (i + t)) = true := by
  induction n with
  | zero => intro i; rw [allA]; simp
  | succ n ih =>
    intro i
    rw [allA, if_pos (by omega), Bool.and_eq_true, show i + (n + 1) = (i + 1) + n by omega, ih]
    constructor
    · rintro ⟨h0, h⟩ t ht
      by_cases t0 : t = 0
      · subst t0; simpa using h0
      · have := h (t - 1) (by omega); rwa [show i + 1 + (t - 1) = i + t by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega); rwa [show i + (t + 1) = i + 1 + t by omega] at this

theorem allA_iff' (B : ByteArray) (i j : Nat) (h : i ≤ j) :
    allA B i j = true ↔ ∀ t < j - i, acgt (B.get! (i + t)) = true := by
  have := allA_iff B (j - i) i
  rwa [show i + (j - i) = j by omega] at this

/-- `a[i, i+k) = b[j, j+k)`. -/
def eqRun (a b : ByteArray) (i j : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => a.get! i == b.get! j && eqRun a b (i + 1) (j + 1) k

theorem eqRun_iff (a b : ByteArray) (k : Nat) :
    ∀ i j, eqRun a b i j k = true ↔ ∀ t < k, a.get! (i + t) = b.get! (j + t) := by
  induction k with
  | zero => intro i j; simp [eqRun]
  | succ k ih =>
    intro i j
    rw [eqRun, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h0, h⟩ t ht
      by_cases t0 : t = 0
      · subst t0; simpa using h0
      · have := h (t - 1) (by omega)
        rwa [show i + 1 + (t - 1) = i + t by omega, show j + 1 + (t - 1) = j + t by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega)
      rwa [show i + (t + 1) = i + 1 + t by omega, show j + (t + 1) = j + 1 + t by omega] at this

/-- First `i ∈ [i, stop)` with `B[i]` not ACGT (`stop` if none). -/
def firstOdd (B : ByteArray) (i stop : Nat) : Nat :=
  if i < stop then (if acgt (B.get! i) then firstOdd B (i + 1) stop else i) else stop
termination_by stop - i

theorem firstOdd_spec (B : ByteArray) (n : Nat) : ∀ i,
    i ≤ firstOdd B i (i + n) ∧ firstOdd B i (i + n) ≤ i + n ∧
    (∀ x, i ≤ x → x < firstOdd B i (i + n) → acgt (B.get! x) = true) ∧
    (firstOdd B i (i + n) < i + n → acgt (B.get! (firstOdd B i (i + n))) = false) := by
  induction n with
  | zero => intro i; rw [firstOdd, if_neg (by omega)]; refine ⟨by omega, by omega, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
    intro i
    rw [firstOdd, if_pos (by omega)]
    split
    · next ha =>
      have := ih (i + 1)
      rw [show i + 1 + n = i + (n + 1) by omega] at this
      obtain ⟨h1, h2, h3, h4⟩ := this
      refine ⟨by omega, h2, fun x hx1 hx2 => ?_, h4⟩
      by_cases hx : x = i
      · subst hx; exact ha
      · exact h3 x (by omega) hx2
    · next ha =>
      refine ⟨by omega, by omega, fun x hx1 hx2 => by omega, fun _ => by simpa using ha⟩

/-! ## Hash -/

def HC : UInt64 := 0x9E3779B97F4A7C15
/-- `HC · HCI ≡ 1 (mod 2^64)`. -/
def HCI : UInt64 := 0xf1de83e19937733d

/-- `(x · HC mod 2^64) &&& m`. -/
@[inline] def hashU (x : Nat) (m : UInt64) : Nat := ((x.toUInt64 * HC) &&& m).toNat

theorem hashU_eq (x k : Nat) (m : UInt64) (hm : m.toNat = 2 ^ (2 * k) - 1) (hk : k ≤ 32) :
    hashU x m = x * HC.toNat % 2 ^ (2 * k) := by
  unfold hashU
  rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_mul]
  have hd : 2 ^ (2 * k) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hd]
  show x.toUInt64.toNat * HC.toNat % 2 ^ (2 * k) = x * HC.toNat % 2 ^ (2 * k)
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mul_mod, Nat.mod_mod_of_dvd _ hd, ← Nat.mul_mod]

theorem HC_HCI : HC.toNat * HCI.toNat % 2 ^ 64 = 1 := by decide

/-- The hash is a bijection on `[0, 4^k)`. -/
theorem hash_inj (k x y : Nat) (hk : k ≤ 32) (hx : x < 2 ^ (2 * k)) (hy : y < 2 ^ (2 * k))
    (h : x * HC.toNat % 2 ^ (2 * k) = y * HC.toNat % 2 ^ (2 * k)) : x = y := by
  have hd : 2 ^ (2 * k) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  have hinv : HC.toNat * HCI.toNat % 2 ^ (2 * k) = 1 % 2 ^ (2 * k) := by
    rw [← Nat.mod_mod_of_dvd _ hd, HC_HCI]
  have key : ∀ z, z < 2 ^ (2 * k) → z = z * HC.toNat % 2 ^ (2 * k) * HCI.toNat % 2 ^ (2 * k) := by
    intro z hz
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, hinv, ← Nat.mul_mod, Nat.mul_one,
      Nat.mod_eq_of_lt hz]
  rw [key x hx, key y hy, h]

/-! ## Bits as arithmetic -/

theorem shiftRight_eq (x n : Nat) : x >>> n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n

theorem and_mask_eq (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n := Nat.and_two_pow_sub_one_eq_mod x n

theorem four_pow (n : Nat) : 4 ^ n = 2 ^ (2 * n) := by
  rw [Nat.pow_mul]

end MapSpec.Mz

#print axioms MapSpec.Mz.eq_of_wc
#print axioms MapSpec.Mz.hash_inj
#print axioms MapSpec.Mz.hashU_eq
