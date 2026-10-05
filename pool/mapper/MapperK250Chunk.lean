import MapperK250Bits
import MapperFastIndex

/-!
# Chunks: packed read against the packed genome

`packRP_ok`: a read that passed the pack check is ACGT with its codes in the words.
`chunk_dig`: digit `t` of read word `j` XOR the genome letters of that chunk (the two
aligned words shifted, `comb`) is `0` iff the bytes match, when the genome letter lies
in a flagged block of a `PGen` that spells `G`.
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- Base-4 value of `B[s, s+m)`, first letter least significant. -/
def wv (B : ByteArray) (s : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => wv B s m + c2N (B.get! (s + m)) * 4 ^ m

theorem wv_lt (B : ByteArray) (s m : Nat) : wv B s m < 4 ^ m := by
  induction m with
  | zero => simp [wv]
  | succ m ih =>
    have := c2N_lt (B.get! (s + m))
    rw [wv, Nat.pow_succ]
    have : c2N (B.get! (s + m)) * 4 ^ m ≤ 3 * 4 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega

theorem wv_dig (B : ByteArray) (s m t : Nat) (ht : t < m) : dig (wv B s m) t = c2N (B.get! (s + t)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [wv]
    have hx := wv_lt B s m
    have hc := c2N_lt (B.get! (s + m))
    by_cases e : t = m
    · subst e
      unfold dig
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hx, Nat.zero_add,
        Nat.mod_eq_of_lt hc]
    · have ht' : t < m := by omega
      rw [← ih ht']
      unfold dig
      have h4 : 4 ^ m = 4 ^ t * (4 * 4 ^ (m - t - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      rw [h4, ← Nat.mul_assoc, Nat.mul_comm _ (4 ^ t), Nat.mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)), ← Nat.mul_assoc, Nat.mul_comm _ 4,
        Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem step_toNat (w : UInt64) (sh : UInt64) (m : Nat) (b : UInt8) (hm : m < 32) (hsh : sh.toNat = 2 * m)
    (hw : w.toNat < 4 ^ m) :
    (w ||| ((codeTab.get! b.toNat) &&& 3).toUInt64 <<< sh).toNat = w.toNat + c2N b * 4 ^ m := by
  have hc := c2_tab b.toNat (UInt8.toNat_lt b)
  rw [show b.toNat.toUInt8 = b by simp] at hc
  have hc' : (((codeTab.get! b.toNat) &&& 3).toUInt64).toNat = c2N b := by
    rw [← hc]; simp
  have hlt := c2N_lt b
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hc', hsh, Nat.mod_eq_of_lt (by omega : 2 * m < 64),
    Nat.shiftLeft_eq]
  have h4 : (4 : Nat) ^ m = 2 ^ (2 * m) := by rw [Nat.pow_mul]
  have hb : c2N b * 2 ^ (2 * m) < 2 ^ 64 := by
    have : 2 ^ (2 * m) * 4 ≤ 2 ^ 64 := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have : c2N b * 2 ^ (2 * m) < 4 * 2 ^ (2 * m) := Nat.mul_lt_mul_of_pos_right hlt (Nat.pow_pos (by omega))
    omega
  rw [Nat.mod_eq_of_lt hb, Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by rw [← h4]; exact hw)]
  rw [h4, Nat.mul_comm (c2N b), Nat.add_comm]

theorem letter_iff (b c : UInt8) (hb : acgt b = true) (hc : c.toNat < 4) :
    b = letter c ↔ c2N b = c.toNat := by
  have key : ∀ n, n < 4 → ∀ m ∈ [65, 67, 71, 84],
      ((m : Nat).toUInt8 = letter n.toUInt8 ↔ c2N m.toUInt8 = n) := by decide
  have ec : c = c.toNat.toUInt8 := by simp
  have hm : b.toNat ∈ [65, 67, 71, 84] := by
    rcases acgt_cases b hb with e | e | e | e <;> subst e <;> simp
  have := key c.toNat hc b.toNat hm
  rw [show b.toNat.toUInt8 = b by simp, ← ec] at this
  exact this

theorem getD_push_lt (acc : Array UInt64) (x : UInt64) (q : Nat) (h : q < acc.size) :
    (acc.push x)[q]! = acc[q]! := by
  rw [getElem!_pos (acc.push x) q (by simp; omega), getElem!_pos acc q h, Array.getElem_push, dif_pos h]

theorem getD_push_eq (acc : Array UInt64) (x : UInt64) : (acc.push x)[acc.size]! = x := by
  rw [getElem!_pos (acc.push x) acc.size (by simp), Array.getElem_push, dif_neg (by omega)]

theorem packLoop_ok (R : ByteArray) : ∀ n i sh w acc ok, R.size - i = n → i ≤ R.size →
    sh.toNat = 2 * (i % 32) → acc.size = i / 32 →
    (∀ q, q < acc.size → acc[q]!.toNat = wv R (32 * q) 32) →
    w.toNat = wv R (32 * (i / 32)) (i % 32) →
    (ok = true → ∀ k, k < i → acgt (R.get! k) = true) →
    (packLoop R i sh w acc ok).ok = true →
    ∀ k, k < R.size → acgt (R.get! k) = true ∧
      dig ((packLoop R i sh w acc ok).w[k / 32]!).toNat (k % 32) = c2N (R.get! k) := by
  intro n
  induction n with
  | zero =>
    intro i sh w acc ok hn hi hsh hacc hq hw hok hr k hk
    have e : i = R.size := by omega
    subst e
    rw [packLoop, if_neg (by omega)] at hr ⊢
    refine ⟨hok hr k hk, ?_⟩
    by_cases hkq : k / 32 < acc.size
    · rw [getD_push_lt _ _ _ hkq, hq _ hkq, wv_dig _ _ _ _ (Nat.mod_lt _ (by omega))]
      congr 2; omega
    · have e : k / 32 = acc.size := by omega
      rw [e, getD_push_eq, hw, wv_dig _ _ _ _ (by omega)]
      congr 2; omega
  | succ n ih =>
    intro i sh w acc ok hn hi hsh hacc hq hw hok hr k hk
    have hiR : i < R.size := by omega
    rw [packLoop, if_pos hiR] at hr ⊢
    have hstep := step_toNat w sh (i % 32) (R.get! i) (Nat.mod_lt _ (by omega)) hsh
      (by rw [hw]; exact wv_lt _ _ _)
    have hw' : (w ||| ((codeTab.get! (R.get! i).toNat) &&& 3).toUInt64 <<< sh).toNat =
        wv R (32 * (i / 32)) (i % 32 + 1) := by
      rw [hstep, wv, hw]; congr 4; omega
    have hok' : (ok && decide (codeTab.get! (R.get! i).toNat < 4)) = true → ∀ k, k < i + 1 → acgt (R.get! k) = true := by
      intro h k hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases e : k = i
      · subst e; simpa [acgt] using h.2
      · exact hok h.1 k (by omega)
    by_cases h62 : i % 32 = 31
    · have hs : (sh == 62) = true := by
        simp only [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hsh, h62]; rfl
      simp only [hs, if_true] at hr ⊢
      refine ih (i + 1) 0 0 _ _ (by omega) (by omega) (by simp; omega) (by simp; omega) ?_ ?_ hok' hr k hk
      · intro q hq'
        simp only [Array.size_push] at hq'
        by_cases e : q < acc.size
        · rw [getD_push_lt _ _ _ e]; exact hq q e
        · have e' : q = acc.size := by omega
          rw [e', getD_push_eq, hw', hacc, h62]
      · rw [show (i + 1) % 32 = 0 by omega]; rfl
    · have hs : (sh == 62) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e; rw [e] at hsh
        simp at hsh; omega
      simp only [hs] at hr ⊢
      refine ih (i + 1) (sh + 2) _ acc _ (by omega) (by omega) ?_ (by omega) hq ?_ hok' hr k hk
      · rw [UInt64.toNat_add, hsh]; simp; omega
      · rw [hw', show (i + 1) / 32 = i / 32 by omega, show (i + 1) % 32 = i % 32 + 1 by omega]

/-- The packed read: every letter ACGT, its code in field `i % 32` of word `i / 32`. -/
theorem packRP_ok (R : ByteArray) (h : (packRP R).ok = true) :
    R.size ≤ 256 ∧ ∀ i, i < R.size → acgt (R.get! i) = true ∧
      dig ((packRP R).w[i / 32]!).toNat (i % 32) = c2N (R.get! i) := by
  unfold packRP at h ⊢
  by_cases hs : R.size ≤ 256
  · rw [if_pos hs] at h ⊢
    refine ⟨hs, packLoop_ok R _ 0 0 0 _ true rfl (by omega) rfl (by simp) (by simp) rfl
      (fun _ k hk => by omega) h⟩
  · rw [if_neg hs] at h; simp at h

theorem code_dig (P : PGen) (U T : Nat) (hT : T < 32) :
    dig (gword P.w U).toNat T = (P.code (32 * U + T)).toNat := by
  rw [gword_dig _ _ _ hT]
  unfold PGen.code
  have e1 : (32 * U + T) >>> 6 = U / 2 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e2 : ((32 * U + T) >>> 2) &&& 15 = 8 * (U % 2) + T / 4 := by
    rw [Nat.shiftRight_eq_div_pow, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2, show 17 * (U / 2) + 1 + (8 * (U % 2) + T / 4) = 17 * (U / 2) + 1 + 8 * (U % 2) + T / 4 by omega]
  generalize P.w.get! (17 * (U / 2) + 1 + 8 * (U % 2) + T / 4) = x
  have e3 : (((32 * U + T).toUInt8 &&& 3) <<< 1).toNat = 2 * (T % 4) := by
    have h3 : ((32 * U + T).toUInt8 &&& 3).toNat = T % 4 := by
      rw [UInt8.toNat_and, show (3 : UInt8).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
      simp; omega
    rw [UInt8.toNat_shiftLeft, h3, Nat.shiftLeft_eq]
    simp; omega
  rw [UInt8.toNat_and, UInt8.toNat_shiftRight, e3, Nat.mod_eq_of_lt (by omega : 2 * (T % 4) < 8),
    show (3 : UInt8).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- Read chunk `j` against the genome at window start `st`: digit `t` of the XOR is `0`
iff read letter `32j + t` matches. -/
theorem chunk_dig (R G : ByteArray) (P : PGen) (hP : Rep P G) (hok : (packRP R).ok = true)
    (st j t : Nat) (ht : t < 32) (hx : 32 * j + t < R.size) (hin : st + 32 * j + t < P.n)
    (hfl : P.w.get! (17 * ((P.o + st + 32 * j + t) / 64)) = 1) :
    dig ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + st) / 32 + j)) (gword P.w ((P.o + st) / 32 + j + 1))
        ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64 (64 - 2 * ((P.o + st) % 32)).toUInt64).toNat t = 0 ↔
      R.get! (32 * j + t) = G.get! (st + 32 * j + t) := by
  have hR := (packRP_ok R hok).2 (32 * j + t) hx
  rw [show (32 * j + t) / 32 = j by omega, show (32 * j + t) % 32 = t by omega] at hR
  have hgen : dig (comb (gword P.w ((P.o + st) / 32 + j)) (gword P.w ((P.o + st) / 32 + j + 1))
      ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64 (64 - 2 * ((P.o + st) % 32)).toUInt64).toNat t =
      (P.code (P.o + st + 32 * j + t)).toNat := by
    rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) ht]
    split
    · rw [code_dig _ _ _ (by omega)]; congr 2; omega
    · rw [code_dig _ _ _ (by omega)]; congr 2; omega
  have hG : G.get! (st + 32 * j + t) = letter (P.code (P.o + st + 32 * j + t)) := by
    rw [← hP.2, PGen.get, if_pos hin, raw_eq, Nat.shiftRight_eq_div_pow,
      show P.o + (st + 32 * j + t) = P.o + st + 32 * j + t by omega, hfl]
    rfl
  have hc : (P.code (P.o + st + 32 * j + t)).toNat < 4 := by
    unfold PGen.code
    rw [UInt8.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [xor_dig, hR.2, hgen, hG, letter_iff _ _ hR.1 hc]

end MapSpec.Fast
