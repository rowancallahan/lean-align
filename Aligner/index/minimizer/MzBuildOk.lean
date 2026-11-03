import MzIndex

/-!
# The minimizer-index builder passes its checker

`Mz.buildW G 22 26 0 5 6` (the parameters `Proofs/Index.lean` builds with) is accepted by
`Mz.check` whenever the genome has at most `2^32 + 23` letters (`check_buildW`). Part 1: bytes
(`getU32`/`setU32`, `zeros`, `wrLE`/`rdSlot`).
-/

open MapSpec MapSpec.Mz
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace MapSpec.Mz.BO

theorem get!_data (B : ByteArray) (i : Nat) : B.get! i = B.data[i]! := by
  cases B; rfl

theorem get!_ge (B : ByteArray) (i : Nat) (h : B.size ≤ i) : B.get! i = 0 := by
  cases B with
  | mk bs =>
  rw [get!_data, getElem!_neg bs i (by simp only [ByteArray.size] at h; omega)]; rfl

theorem size_set! (B : ByteArray) (j : Nat) (v : UInt8) : (B.set! j v).size = B.size := by
  cases B; simp [ByteArray.set!, ByteArray.size]

theorem get!_set! (B : ByteArray) (j i : Nat) (v : UInt8) :
    (B.set! j v).get! i = if i = j ∧ j < B.size then v else B.get! i := by
  cases B with
  | mk bs =>
  simp only [ByteArray.set!, get!_data, ByteArray.size]
  by_cases hi : i < bs.size
  · rw [getElem!_pos (bs.set! j v) i (by simpa using hi), getElem!_pos bs i hi]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij, Ne.symm hij]
  · rw [getElem!_neg (bs.set! j v) i (by simpa using hi), getElem!_neg bs i hi]
    split
    · omega
    · rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem or_add (a b i : Nat) (ha : a < 2 ^ i) : a ||| b * 2 ^ i = a + b * 2 ^ i := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt ha, Nat.or_comm]

theorem getU32_nat (B : ByteArray) (i : Nat) : getU32 B i =
    (B.get! (4 * i)).toNat + (B.get! (4 * i + 1)).toNat * 2 ^ 8 + (B.get! (4 * i + 2)).toNat * 2 ^ 16 +
      (B.get! (4 * i + 3)).toNat * 2 ^ 24 := by
  unfold getU32
  have h0 := (B.get! (4 * i)).toNat_lt
  have h1 := (B.get! (4 * i + 1)).toNat_lt
  have h2 := (B.get! (4 * i + 2)).toNat_lt
  have h3 := (B.get! (4 * i + 3)).toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  simp only [show (8 : UInt32).toNat = 8 from rfl, show (16 : UInt32).toNat = 16 from rfl,
    show (24 : UInt32).toNat = 24 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show (B.get! (4 * i + 1)).toNat * 2 ^ (8 % 32) < 2 ^ 32 by simp; omega),
    Nat.mod_eq_of_lt (show (B.get! (4 * i + 2)).toNat * 2 ^ (16 % 32) < 2 ^ 32 by simp; omega),
    Nat.mod_eq_of_lt (show (B.get! (4 * i + 3)).toNat * 2 ^ (24 % 32) < 2 ^ 32 by simp; omega)]
  simp only [show 8 % 32 = 8 from rfl, show 16 % 32 = 16 from rfl, show 24 % 32 = 24 from rfl]
  rw [or_add _ _ 8 (by omega), or_add _ _ 16 (by omega), or_add _ _ 24 (by omega)]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem size_setU32 (B : ByteArray) (i v : Nat) : (setU32 B i v).size = B.size := by
  simp only [setU32, size_set!]

theorem get!_setU32 (B : ByteArray) (i v j : Nat) (h : 4 * i + 3 < B.size) :
    ((setU32 B i v).get! j).toNat =
      if 4 * i ≤ j ∧ j < 4 * i + 4 then v % 2 ^ 32 / 2 ^ (8 * (j - 4 * i)) % 256 else (B.get! j).toNat := by
  simp only [setU32, get!_set!, size_set!]
  have hv : v.toUInt32.toNat = v % 2 ^ 32 := by simp
  by_cases h0 : j = 4 * i
  · subst h0; simp [show 4 * i < B.size by omega, hv]
  by_cases h1 : j = 4 * i + 1
  · subst h1; simp [show 4 * i + 1 < B.size by omega, hv, Nat.shiftRight_eq_div_pow]
  by_cases h2 : j = 4 * i + 2
  · subst h2; simp [show 4 * i + 2 < B.size by omega, hv, Nat.shiftRight_eq_div_pow]
  by_cases h3 : j = 4 * i + 3
  · subst h3; simp [h, hv, Nat.shiftRight_eq_div_pow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem getU32_setU32 (B : ByteArray) (i v j : Nat) (h : 4 * i + 3 < B.size) :
    getU32 (setU32 B i v) j = if j = i then v % 2 ^ 32 else getU32 B j := by
  rw [getU32_nat, get!_setU32 _ _ _ _ h, get!_setU32 _ _ _ _ h, get!_setU32 _ _ _ _ h, get!_setU32 _ _ _ _ h]
  by_cases hj : j = i
  · subst j
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos rfl]
    simp only [show 4 * i + 1 - 4 * i = 1 by omega, show 4 * i + 2 - 4 * i = 2 by omega,
      show 4 * i + 3 - 4 * i = 3 by omega, Nat.sub_self]
    have := Nat.mod_lt v (show 0 < 2 ^ 32 by decide)
    generalize v % 2 ^ 32 = x at this ⊢
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
    omega
  · rw [if_neg hj, getU32_nat, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem zeros_eq (n : Nat) : zeros n = (List.range' 0 n).foldl (fun B _ => B.push 0) (ByteArray.emptyWithCapacity n) := by
  simp [zeros, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]; rfl

theorem foldl_push (l : List Nat) (B : ByteArray) :
    (l.foldl (fun B _ => B.push 0) B).size = B.size + l.length ∧
    ∀ i, (l.foldl (fun B _ => B.push 0) B).get! i = B.get! i := by
  induction l generalizing B with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (B.push 0)
    refine ⟨by simp [h1]; omega, fun i => ?_⟩
    rw [List.foldl_cons, h2, get!_data, get!_data]
    simp only [ByteArray.data_push]
    have hB : B.size = B.data.size := rfl
    by_cases hi : i < B.data.size
    · rw [getElem!_pos (B.data.push 0) i (by simp; omega), getElem!_pos B.data i hi, Array.getElem_push_lt]
    · by_cases he : i = B.data.size
      · subst he; rw [getElem!_pos (B.data.push 0) _ (by simp), Array.getElem_push_eq,
          getElem!_neg B.data _ (by omega)]; rfl
      · rw [getElem!_neg (B.data.push 0) _ (by simp; omega), getElem!_neg B.data _ (by omega)]

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  rw [zeros_eq, (foldl_push _ _).1]; simp [ByteArray.size, ByteArray.emptyWithCapacity]; rfl

theorem get!_zeros (n i : Nat) : (zeros n).get! i = 0 := by
  rw [zeros_eq, (foldl_push _ _).2, get!_ge _ _ (by simp [ByteArray.size, ByteArray.emptyWithCapacity]; exact Nat.zero_le _)]

theorem getU32_zeros (n i : Nat) : getU32 (zeros n) i = 0 := by
  rw [getU32_nat]; simp [get!_zeros]

theorem size_wrLE (B : ByteArray) (j : Nat) (v : UInt64) (n : Nat) : (wrLE B j v n).size = B.size := by
  induction n generalizing B j v with
  | zero => rfl
  | succ n ih => rw [wrLE, ih, size_set!]

theorem get!_wrLE (n : Nat) : ∀ (B : ByteArray) (j : Nat) (v : UInt64) (i : Nat), j + n ≤ B.size →
    ((wrLE B j v n).get! i).toNat =
      if j ≤ i ∧ i < j + n then v.toNat / 2 ^ (8 * (i - j)) % 256 else (B.get! i).toNat := by
  induction n with
  | zero => intro B j v i _; simp [wrLE]; intro h1 h2; omega
  | succ n ih =>
    intro B j v i hs
    rw [wrLE, ih _ _ _ _ (by rw [size_set!]; omega), get!_set!]
    simp only [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftRight_eq_div_pow]
    by_cases hij : i = j
    · subst hij
      rw [if_neg (show ¬(i + 1 ≤ i ∧ i < i + 1 + n) by omega), if_pos (show i = i ∧ i < B.size from ⟨rfl, by omega⟩),
        if_pos (show i ≤ i ∧ i < i + (n + 1) by omega)]
      simp
    · rw [if_neg (show ¬(i = j ∧ j < B.size) from fun h => hij h.1)]
      by_cases hin : j + 1 ≤ i ∧ i < j + 1 + n
      · rw [if_pos hin, if_pos (show j ≤ i ∧ i < j + (n + 1) by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
        congr 3; omega
      · rw [if_neg hin, if_neg (show ¬(j ≤ i ∧ i < j + (n + 1)) by omega)]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem getElem_get! (B : ByteArray) (j : Nat) (h : j < B.size) : B[j] = B.get! j := by
  cases B with
  | mk bs => show bs[j] = bs[j]!; rw [getElem!_pos bs j h]

theorem rdSlot5 (B : ByteArray) (t : Nat) (h : 5 * t + 4 < B.size) : rdSlot B 5 t =
    (B.get! (5 * t)).toNat + (B.get! (5 * t + 1)).toNat * 2 ^ 8 + (B.get! (5 * t + 2)).toNat * 2 ^ 16 +
      (B.get! (5 * t + 3)).toNat * 2 ^ 24 + (B.get! (5 * t + 4)).toNat * 2 ^ 32 := by
  unfold rdSlot rd4 byteAt
  dsimp only
  rw [if_neg (show ¬ (5 : Nat) = 4 by decide), if_pos (rfl : (5 : Nat) = 5), dif_pos (show 5 * t + 3 < B.size by omega)]
  simp only [getElem_get!]
  have h0 := (B.get! (5 * t)).toNat_lt
  have h1 := (B.get! (5 * t + 1)).toNat_lt
  have h2 := (B.get! (5 * t + 2)).toNat_lt
  have h3 := (B.get! (5 * t + 3)).toNat_lt
  have h4 := (B.get! (5 * t + 4)).toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  simp only [show (8 : UInt64).toNat = 8 from rfl, show (16 : UInt64).toNat = 16 from rfl,
    show (24 : UInt64).toNat = 24 from rfl, show (32 : UInt64).toNat = 32 from rfl, Nat.shiftLeft_eq,
    show 8 % 64 = 8 from rfl, show 16 % 64 = 16 from rfl, show 24 % 64 = 24 from rfl, show 32 % 64 = 32 from rfl]
  rw [Nat.mod_eq_of_lt (show (B.get! (5 * t + 1)).toNat * 2 ^ 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (B.get! (5 * t + 2)).toNat * 2 ^ 16 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (B.get! (5 * t + 3)).toNat * 2 ^ 24 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (B.get! (5 * t + 4)).toNat * 2 ^ 32 < 2 ^ 64 by omega)]
  rw [or_add _ _ 8 (by omega), or_add _ _ 16 (by omega), or_add _ _ 24 (by omega), or_add _ _ 32 (by omega)]

/-- A slot written with `wrLE` reads back (5-byte slots, value `< 2^40`). -/
theorem rdSlot5_wrLE_self (B : ByteArray) (t : Nat) (v : UInt64) (h : 5 * t + 5 ≤ B.size) :
    rdSlot (wrLE B (5 * t) v 5) 5 t = v.toNat % 2 ^ 40 := by
  rw [rdSlot5 _ _ (by rw [size_wrLE]; omega)]
  simp only [get!_wrLE 5 B (5 * t) v _ h]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  simp only [show 5 * t + 1 - 5 * t = 1 by omega, show 5 * t + 2 - 5 * t = 2 by omega,
    show 5 * t + 3 - 5 * t = 3 by omega, show 5 * t + 4 - 5 * t = 4 by omega, Nat.sub_self]
  generalize v.toNat = x
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

theorem rdSlot5_wrLE_ne (B : ByteArray) (t t' : Nat) (v : UInt64) (h : 5 * t + 5 ≤ B.size) (hne : t' ≠ t)
    (ht : 5 * t' + 5 ≤ B.size) :
    rdSlot (wrLE B (5 * t) v 5) 5 t' = rdSlot B 5 t' := by
  · rw [rdSlot5 _ _ (by rw [size_wrLE]; omega), rdSlot5 _ _ (by omega)]
    simp only [get!_wrLE 5 B (5 * t) v _ h]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- `r` is the leftmost place of the least value of `f` on `[0, n)`. -/
def IsLAM (f : Nat → Nat) (n r : Nat) : Prop :=
  r < n ∧ (∀ j < n, f r ≤ f j) ∧ (∀ j < r, f r < f j)

theorem IsLAM.unique {f : Nat → Nat} {n r r' : Nat} (h : IsLAM f n r) (h' : IsLAM f n r') : r = r' := by
  rcases Nat.lt_trichotomy r r' with e | e | e
  · have := h'.2.2 r e; have := h.2.1 r' h'.1; omega
  · exact e
  · have := h.2.2 r' e; have := h'.2.1 r h.1; omega

theorem miniGo_spec (u kmU : UInt64) (f : Nat → Nat)
    (hf : ∀ o < 20, ((((u >>> (38 - 2 * o : Nat).toUInt64) &&& kmU) * HC) &&& kmU).toNat = f o) :
    ∀ n o bo sh bh, 20 - o = n → 1 ≤ o → o ≤ 20 → bo < o → (o < 20 → sh = (38 - 2 * o : Nat).toUInt64) →
      bh.toNat = f bo → (∀ j < o, f bo ≤ f j) → (∀ j < bo, f bo < f j) →
      IsLAM f 20 (miniGo u kmU 20 o bo sh bh) := by
  intro n
  induction n with
  | zero =>
    intro o bo sh bh hn h1 h20 hb _ hbh hmin hleft
    rw [miniGo, if_neg (by omega)]
    exact ⟨by omega, fun j hj => hmin j (by omega), hleft⟩
  | succ n ih =>
    intro o bo sh bh hn h1 h20 hb hsh hbh hmin hleft
    rw [miniGo, if_pos (by omega)]
    dsimp only
    have hfo := hf o (by omega)
    rw [hsh (by omega)] at *
    split
    · next hlt =>
      have hlt' : f o < f bo := by rw [← hfo, ← hbh]; exact hlt
      refine ih _ _ _ _ (by omega) (by omega) (by omega) (by omega) (fun h => ?_) hfo (fun j hj => ?_) (fun j hj => ?_)
      · apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le]; simp only [Nat.toUInt64, UInt64.toNat_ofNat']
              rw [Nat.mod_eq_of_lt (by omega)]; show 2 ≤ _; omega)]
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        show 38 - 2 * o - 2 = _; omega
      · by_cases hj' : j = o
        · subst hj'; exact Nat.le_refl _
        · have := hmin j (by omega); omega
      · have := hmin j hj; omega
    · next hge =>
      have hge' : f bo ≤ f o := by
        rw [← hfo, ← hbh]; exact Nat.not_lt.mp (fun h => hge (UInt64.lt_iff_toNat_lt.mpr h))
      refine ih _ _ _ _ (by omega) (by omega) (by omega) (by omega) (fun h => ?_) hbh (fun j hj => ?_) hleft
      · apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le]; simp only [Nat.toUInt64, UInt64.toNat_ofNat']
              rw [Nat.mod_eq_of_lt (by omega)]; show 2 ≤ _; omega)]
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        show 38 - 2 * o - 2 = _; omega
      · by_cases hj' : j = o
        · subst hj'; exact hge'
        · exact hmin j (by omega)

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- The hash `mini` compares t-words (`t = 6`) by. -/
def Hs (x : Nat) : Nat := ((x.toUInt64 * HC) &&& 4095).toNat

theorem tword (G : ByteArray) (p o : Nat) (ho : o < 20) :
    ((wc G p q).toUInt64 >>> (38 - 2 * o : Nat).toUInt64) &&& 4095 = (wc G (p + o) 6).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hv : wc G p q < 2 ^ 64 := Nat.lt_of_lt_of_le (wc_lt G p q) (by rw [four_pow]; exact Nat.pow_le_pow_right (by omega) (by decide))
  have h6 : wc G (p + o) 6 < 2 ^ 64 := Nat.lt_of_lt_of_le (wc_lt G _ 6) (by decide)
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.toUInt64, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt h6]
  rw [Nat.mod_eq_of_lt (show 38 - 2 * o < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 38 - 2 * o < 64 by omega),
    show (4095 : UInt64).toNat = 2 ^ 12 - 1 from rfl, and_mask_eq, shiftRight_eq,
    show 38 - 2 * o = 2 * (19 - o) by omega, ← four_pow, show 12 = 2 * 6 from rfl, ← four_pow]
  have h1 := wc_div G p (o + 6) (19 - o)
  rw [show o + 6 + (19 - o) = q by rw [show q = 25 from rfl]; omega] at h1
  rw [h1, wc_mod]

theorem mini_lam (ix : MzIdx) (ht : ix.t = 6) (htm : ix.tmU = 4095) (hw : ix.w = 4) (G : ByteArray) (p : Nat) :
    ∃ r, IsLAM (fun j => Hs (wc G (p + j) 6)) 20 r ∧ ix.mini (wc G p q) = r % 4 := by
  unfold MzIdx.mini
  simp only [ht, htm, hw]
  have hf : ∀ o < 20, (((((wc G p q).toUInt64 >>> (38 - 2 * o : Nat).toUInt64) &&& 4095) * HC) &&& 4095).toNat =
      Hs (wc G (p + o) 6) := fun o ho => by rw [tword G p o ho]; rfl
  rw [show q + 1 - 6 = 20 from rfl]
  have hl := miniGo_spec _ _ _ hf _ 1 0 ((2 * (q - 6)).toUInt64 - 2)
    ((((wc G p q).toUInt64 >>> (2 * (q - 6)).toUInt64) &&& 4095) * HC &&& 4095) rfl (Nat.le_refl _) (by decide) (by decide)
    (fun _ => by decide) (hf 0 (by decide))
    (fun j hj => by rw [show j = 0 by omega]; exact Nat.le_refl _) (fun j hj => by omega)
  refine ⟨_, hl, ?_⟩
  split
  · next h => rw [Nat.mod_eq_of_lt h]
  · rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- One window to the next: the minimizer place does not go back. -/
theorem mini_step (ix : MzIdx) (ht : ix.t = 6) (htm : ix.tmU = 4095) (hw : ix.w = 4) (G : ByteArray) (p : Nat) :
    p + ix.mini (wc G p q) ≤ p + 1 + ix.mini (wc G (p + 1) q) := by
  obtain ⟨r, hr, e⟩ := mini_lam ix ht htm hw G p
  obtain ⟨r', hr', e'⟩ := mini_lam ix ht htm hw G (p + 1)
  rw [e, e']
  have hsh : ∀ j, Hs (wc G (p + 1 + j) 6) = Hs (wc G (p + (j + 1)) 6) := fun j => by rw [Nat.add_assoc, Nat.add_comm 1 j]
  simp only [hsh] at hr'
  have h20 := hr.1
  by_cases r0 : r = 0
  · subst r0; omega
  by_cases hlt : Hs (wc G (p + 20) 6) < Hs (wc G (p + r) 6)
  · have h19 : IsLAM (fun j => Hs (wc G (p + (j + 1)) 6)) 20 19 := by
      refine ⟨by decide, fun j hj => ?_, fun j hj => ?_⟩
      · by_cases j19 : j = 19
        · subst j19; exact Nat.le_refl _
        · have := hr.2.1 (j + 1) (by omega); dsimp only at this ⊢; rw [show p + (19 + 1) = p + 20 from rfl]; omega
      · have := hr.2.1 (j + 1) (by omega); dsimp only at this ⊢; rw [show p + (19 + 1) = p + 20 from rfl]; omega
    have := hr'.unique h19
    omega
  · have hr1 : IsLAM (fun j => Hs (wc G (p + (j + 1)) 6)) 20 (r - 1) := by
      refine ⟨by omega, fun j hj => ?_, fun j hj => ?_⟩
      · dsimp only; rw [Nat.sub_add_cancel (by omega)]
        by_cases j19 : j = 19
        · subst j19; rw [show p + (19 + 1) = p + 20 from rfl]; omega
        · exact hr.2.1 (j + 1) (by omega)
      · dsimp only; rw [Nat.sub_add_cancel (by omega)]
        exact hr.2.2 (j + 1) (by omega)
    have := hr'.unique hr1
    omega

theorem mini_mono (ix : MzIdx) (ht : ix.t = 6) (htm : ix.tmU = 4095) (hw : ix.w = 4) (G : ByteArray) (p : Nat) :
    ∀ d, p + ix.mini (wc G p q) ≤ p + d + ix.mini (wc G (p + d) q) := by
  intro d
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => have := mini_step ix ht htm hw G (p + d); rw [← Nat.add_assoc]; omega

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- Minimizer place of the window at `p`. -/
def pmOf (ix : MzIdx) (G : ByteArray) (p : Nat) : Nat := p + ix.mini (wcGo G p (p + q) 0)

/-- The minimizer places `checkComp` visits (in order, consecutive repeats dropped). -/
def evs (ix : MzIdx) (G : ByteArray) (last : Nat) : (n p : Nat) → List Nat
  | 0, _ => []
  | n + 1, p =>
    if allA G p (p + q) then
      if pmOf ix G p + 1 = last then evs ix G last n (p + 1)
      else pmOf ix G p :: evs ix G (pmOf ix G p + 1) n (p + 1)
    else evs ix G last n (p + 1)

/-- `checkComp` along its places. -/
def replay (ix : MzIdx) (G : ByteArray) (fill : ByteArray) : List Nat → Bool
  | [] => true
  | pm :: es =>
    let b := ix.hsh (wcGo G pm (pm + ix.k) 0) >>> ix.kb
    let t := getU32 fill b
    decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf (ix.slot t) == pm &&
      replay ix G (setU32 fill b (t + 1)) es

theorem checkComp_eq (ix : MzIdx) (G : ByteArray) :
    ∀ n fill last p, checkComp ix G fill last n p = replay ix G fill (evs ix G last n p) := by
  intro n
  induction n with
  | zero => intro fill last p; rfl
  | succ n ih =>
    intro fill last p
    unfold checkComp evs pmOf
    by_cases hA : allA G p (p + q) = true
    · rw [if_pos hA, if_pos hA]
      dsimp only
      by_cases hl : p + ix.mini (wcGo G p (p + q) 0) + 1 = last
      · rw [if_pos hl, if_pos hl, ih]
      · rw [if_neg hl, if_neg hl]; simp only [replay, ih]
    · rw [if_neg hA, if_neg hA, ih]

/-- What the builder's rolling state knows after reading `G[0, p)`: the ACGT run ending at `p`
has length `good`, and `x` holds the code of its last `min good q` letters. -/
def FI (G : ByteArray) (p : Nat) (x : UInt64) (good : Nat) : Prop :=
  good ≤ p ∧ x.toNat < 2 ^ 50 ∧ (∀ i < good, acgt (G.get! (p - 1 - i)) = true) ∧
    (good = p ∨ acgt (G.get! (p - 1 - good)) = false) ∧
    x.toNat % 4 ^ (min good q) = wc G (p - min good q) (min good q)

theorem roll_mod (x c m : Nat) (hc : c < 4) (hm : 1 ≤ m) (hm' : m ≤ 25) :
    (x * 4 % 2 ^ 64 + c) % 2 ^ 50 % 4 ^ m = (x % 4 ^ (m - 1) * 4 + c) % 4 ^ m := by
  have hd1 : 4 ^ m ∣ 2 ^ 50 := by
    rw [four_pow]; exact Nat.pow_dvd_pow 2 (by omega)
  have hd2 : 4 ^ m ∣ 2 ^ 64 := by
    rw [four_pow]; exact Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hd1, Nat.add_mod, Nat.mod_mod_of_dvd _ hd2, ← Nat.add_mod]
  have e : 4 ^ m = 4 ^ (m - 1) * 4 := by rw [← Nat.pow_succ]; congr 1; omega
  conv => lhs; rw [← Nat.mod_add_div x (4 ^ (m - 1))]
  rw [Nat.add_mul, Nat.add_right_comm, e, Nat.mul_assoc, Nat.mul_comm (x / _) 4, ← Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

theorem FI_step (G : ByteArray) (p : Nat) (x : UInt64) (good : Nat) (h : FI G p x good) :
    FI G (p + 1)
      (if acgt (G.get! p) then (x <<< 2 ||| (byteCode (G.get! p)).toUInt64) &&& 0x3FFFFFFFFFFFF else x)
      (if acgt (G.get! p) then good + 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  by_cases ha : acgt (G.get! p) = true
  · rw [if_pos ha, if_pos ha]
    have hc := byteCode_lt (G.get! p)
    have hx : ((x <<< 2 ||| (byteCode (G.get! p)).toUInt64) &&& 0x3FFFFFFFFFFFF).toNat =
        (x.toNat * 4 % 2 ^ 64 + byteCode (G.get! p)) % 2 ^ 50 := by
      simp only [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_shiftLeft, Nat.toUInt64, UInt64.toNat_ofNat',
        show (2 : UInt64).toNat % 64 = 2 from rfl, show (0x3FFFFFFFFFFFF : UInt64).toNat = 2 ^ 50 - 1 from rfl,
        and_mask_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show byteCode (G.get! p) < 2 ^ 64 by omega)]
      congr 1
      have hy : x.toNat * 2 ^ 2 % 2 ^ 64 = x.toNat % 2 ^ 62 * 2 ^ 2 := by
        rw [show (2 : Nat) ^ 64 = 2 ^ 62 * 2 ^ 2 from rfl, Nat.mul_mod_mul_right]
      rw [hy, Nat.or_comm, or_add _ _ 2 (by omega)]
      omega
    have hq : q = 25 := rfl
    refine ⟨by omega, by rw [hx]; exact Nat.mod_lt _ (by decide), fun i hi => ?_, ?_, ?_⟩
    · by_cases i0 : i = 0
      · subst i0; simpa using ha
      · have := h3 (i - 1) (by omega); rwa [show p - 1 - (i - 1) = p + 1 - 1 - i by omega] at this
    · rcases h4 with h4 | h4
      · left; omega
      · right; rwa [show p + 1 - 1 - (good + 1) = p - 1 - good by omega]
    · rw [hx, roll_mod _ _ _ hc (by omega) (by omega)]
      by_cases hg : good < q
      · rw [show min (good + 1) q = good + 1 by omega, show good + 1 - 1 = good by omega,
          show min good q = good by omega] at *
        rw [h5, show p + 1 - (good + 1) = p - good by omega]
        have e : wc G (p - good) (good + 1) = wc G (p - good) good * 4 + byteCode (G.get! p) := by
          rw [wc, show p - good + good = p by omega]
        rw [← e]; exact Nat.mod_eq_of_lt (wc_lt _ _ _)
      · rw [show min (good + 1) q = q by omega] at *
        rw [show min good q = q by omega] at h5
        have e1 : x.toNat % 4 ^ (q - 1) = wc G (p - 24) 24 := by
          rw [show q - 1 = 24 from rfl, ← Nat.mod_mod_of_dvd x.toNat (show 4 ^ 24 ∣ 4 ^ q from
            Nat.pow_dvd_pow 4 (by omega)), h5]
          have := wc_mod G (p - q) 1 24
          rwa [show 1 + 24 = q from rfl, show p - q + 1 = p - 24 by omega] at this
        have e : wc G (p + 1 - q) q = wc G (p - 24) 24 * 4 + byteCode (G.get! p) := by
          rw [show p + 1 - q = p - 24 by omega, show q = 24 + 1 from rfl, wc, show p - 24 + 24 = p by omega]
        rw [e1, ← e]; exact Nat.mod_eq_of_lt (wc_lt _ _ _)
  · rw [if_neg ha, if_neg ha]
    refine ⟨by omega, h2, fun i hi => by omega, Or.inr (by simpa using ha), ?_⟩
    simp [wc, Nat.mod_one]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem FI_window (G : ByteArray) (e : Nat) (x : UInt64) (g : Nat) (h : FI G e x g) (he : q ≤ e) :
    (allA G (e - q) (e - q + q) = true ↔ q ≤ g) ∧ (q ≤ g → x.toNat = wc G (e - q) q) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hq : q = 25 := rfl
  refine ⟨?_, fun hg => ?_⟩
  · rw [allA_iff]
    constructor
    · intro hA
      apply Classical.byContradiction; intro hlt
      rcases h4 with h4 | h4
      · omega
      · have := hA (e - 1 - g - (e - q)) (by omega)
        rw [show e - q + (e - 1 - g - (e - q)) = e - 1 - g by omega, h4] at this; cases this
    · intro hg t ht
      have := h3 (q - 1 - t) (by omega)
      rwa [show e - 1 - (q - 1 - t) = e - q + t by omega] at this
  · rw [show min g q = q by omega] at h5
    rw [← h5, Nat.mod_eq_of_lt (by rw [show (4 : Nat) ^ q = 2 ^ 50 from rfl]; exact h2)]

theorem foldMinsGo_evs (ix0 : MzIdx) (hg : Good ix0) (G : ByteArray) {α : Type} (f : α → Nat → Nat → α) :
    ∀ d p x good last acc, G.size - p = d → FI G p x good →
      foldMinsGo ix0 G f p x good last acc =
        (evs ix0 G last (G.size - max p (q - 1)) (p + 1 - q)).foldl
          (fun a pm => f a pm (ix0.hsh (wc G pm ix0.k))) acc := by
  have hq : q = 25 := rfl
  intro d
  induction d with
  | zero =>
    intro p x good last acc hd _
    rw [foldMinsGo, if_neg (by omega), show G.size - max p (q - 1) = 0 by omega]
    rfl
  | succ d ih =>
    intro p x good last acc hd hI
    rw [foldMinsGo, if_pos (by omega)]
    dsimp only
    have hI' := FI_step G p x good hI
    generalize hx' : (if acgt (G.get! p) = true then (x <<< 2 ||| (byteCode (G.get! p)).toUInt64) &&& 0x3FFFFFFFFFFFF
      else x) = x' at hI'
    generalize hg' : (if acgt (G.get! p) = true then good + 1 else 0) = g' at hI'
    by_cases hp : p < q - 1
    · have hlt : ¬ (g' ≥ q) := by have := hI'.1; omega
      rw [if_neg hlt, ih (p + 1) x' g' last acc (by omega) hI',
        show max (p + 1) (q - 1) = max p (q - 1) by omega, show p + 1 + 1 - q = p + 1 - q by omega]
    · obtain ⟨hw1, hw2⟩ := FI_window G (p + 1) x' g' hI' (by omega)
      rw [show G.size - max p (q - 1) = (G.size - max (p + 1) (q - 1)) + 1 by omega, evs,
        show p + 1 - q + q = p + 1 by omega] at *
      have ih' := fun last acc => ih (p + 1) x' g' last acc (by omega) hI'
      rw [show p + 1 + 1 - q = p + 1 - q + 1 by omega] at ih'
      by_cases hA : allA G (p + 1 - q) (p + 1) = true
      · have hgq := hw1.1 hA
        have hv := hw2 hgq
        rw [if_pos hgq, if_pos hA]
        have hm := mini_lt hg x'.toNat
        have hpm : pmOf ix0 G (p + 1 - q) = p + 1 - q + ix0.mini x'.toNat := by
          rw [pmOf, show p + 1 - q + q = p + 1 by omega, wcGo_zero' _ _ _ (by omega),
            show p + 1 - (p + 1 - q) = q by omega, hv]
        have hsub : ix0.sub x'.toNat (ix0.mini x'.toNat) = wc G (p + 1 - q + ix0.mini x'.toNat) ix0.k := by
          rw [hv]; exact sub_wc hg G _ _ (by have := hg.w_eq; have := mini_lt hg (wc G (p + 1 - q) q); omega)
        rw [hpm]
        by_cases hl : p + 1 - q + ix0.mini x'.toNat + 1 = last
        · rw [if_neg (by simp [hl]), if_pos hl, ih']
        · rw [if_pos (by simp [hl]), if_neg hl, hsub, ih']; rfl
      · rw [if_neg (fun h => hA (hw1.2 h)), if_neg hA, ih']

theorem foldMins_evs (ix0 : MzIdx) (hg : Good ix0) (G : ByteArray) {α : Type} (init : α) (f : α → Nat → Nat → α) :
    foldMins ix0 G init f =
      (evs ix0 G 0 (G.size + 1 - q) 0).foldl (fun a pm => f a pm (ix0.hsh (wc G pm ix0.k))) init := by
  unfold foldMins
  rw [foldMinsGo_evs ix0 hg G f _ 0 0 0 0 init rfl
    ⟨Nat.le_refl _, by decide, fun i hi => by omega, Or.inl rfl, by simp [wc]⟩]
  rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem evs_length (ix : MzIdx) (G : ByteArray) : ∀ n last p, (evs ix G last n p).length ≤ n := by
  intro n
  induction n with
  | zero => intro last p; simp [evs]
  | succ n ih =>
    intro last p
    unfold evs
    split
    · split
      · have := ih last (p + 1); omega
      · have := ih (pmOf ix G p + 1) (p + 1); simp; omega
    · have := ih last (p + 1); omega

theorem evs_mem (ix : MzIdx) (G : ByteArray) : ∀ n last p x, x ∈ evs ix G last n p →
    ∃ s, p ≤ s ∧ allA G s (s + q) = true ∧ x = pmOf ix G s := by
  intro n
  induction n with
  | zero => intro last p x h; simp [evs] at h
  | succ n ih =>
    intro last p x h
    unfold evs at h
    split at h
    · next hA =>
      split at h
      · obtain ⟨s, h1, h2, h3⟩ := ih _ _ _ h; exact ⟨s, by omega, h2, h3⟩
      · rcases List.mem_cons.mp h with h | h
        · exact ⟨p, Nat.le_refl _, hA, h⟩
        · obtain ⟨s, h1, h2, h3⟩ := ih _ _ _ h; exact ⟨s, by omega, h2, h3⟩
    · obtain ⟨s, h1, h2, h3⟩ := ih _ _ _ h; exact ⟨s, by omega, h2, h3⟩

theorem pmOf_mono (ix : MzIdx) (ht : ix.t = 6) (htm : ix.tmU = 4095) (hw : ix.w = 4) (G : ByteArray)
    (p p' : Nat) (h : p ≤ p') : pmOf ix G p ≤ pmOf ix G p' := by
  unfold pmOf
  rw [wcGo_zero, wcGo_zero]
  have := mini_mono ix ht htm hw G p (p' - p)
  rwa [Nat.add_sub_cancel' h] at this

theorem evs_sorted (ix : MzIdx) (ht : ix.t = 6) (htm : ix.tmU = 4095) (hw : ix.w = 4) (G : ByteArray) :
    ∀ n last p, last ≤ pmOf ix G p + 1 →
      (∀ x ∈ evs ix G last n p, last ≤ x) ∧ (evs ix G last n p).Pairwise (· < ·) := by
  intro n
  induction n with
  | zero => intro last p _; simp [evs]
  | succ n ih =>
    intro last p hl
    have hm := pmOf_mono ix ht htm hw G p (p + 1) (by omega)
    unfold evs
    split
    · split
      · exact ih last (p + 1) (by omega)
      · next hne =>
        obtain ⟨h1, h2⟩ := ih (pmOf ix G p + 1) (p + 1) (by omega)
        refine ⟨fun x hx => ?_, List.pairwise_cons.mpr ⟨fun x hx => ?_, h2⟩⟩
        · rcases List.mem_cons.mp hx with hx | hx
          · omega
          · have := h1 x hx; omega
        · have := h1 x hx; omega
    · exact ih last (p + 1) (by omega)

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem checkParams_ix0 (pb : Nat) : checkParams (mkIdx 22 26 0 5 pb 6) = true := by
  simp only [checkParams, mkIdx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨?_, by decide +kernel⟩
  simp only [if_true, and_true, show q = 25 from rfl]
  and_intros <;> first | decide | omega | rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

abbrev ix0 (G : ByteArray) : MzIdx := mkIdx 22 26 0 5 (G.size.log2 + 1) 6

def cntStep (ix : MzIdx) (cnt : ByteArray) (_ : Nat) (h : Nat) : ByteArray :=
  setU32 cnt (h >>> ix.kb + 1) (getU32 cnt (h >>> ix.kb + 1) + 1)

def sumStep (cnt : ByteArray) (b : Nat) : ByteArray := setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)

def fillStep (ix : MzIdx) (G : ByteArray) (st : ByteArray × ByteArray) (pm h : Nat) : ByteArray × ByteArray :=
  (setU32 st.1 (h >>> ix.kb) (getU32 st.1 (h >>> ix.kb) + 1),
    wrLE st.2 (5 * getU32 st.1 (h >>> ix.kb)) (slotAt ix G pm h) 5)

def runStep (G : ByteArray) (r : Array Nat) (p : Nat) : Array Nat :=
  let r := if (!acgt (G.get! p) && (p == 0 || acgt (G.get! (p - 1)))) = true then r.push p else r
  if (!acgt (G.get! p) && (p + 1 == G.size || acgt (G.get! (p + 1)))) = true then r.push (p + 1) else r

theorem forIn_id_foldl {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) : forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h]; exact ih _

def cntOf (G : ByteArray) : ByteArray :=
  (List.range' 0 (2 ^ 26)).foldl sumStep (foldMins (ix0 G) G (zeros (4 * (2 ^ 26 + 1))) (cntStep (ix0 G)))

theorem buildW_eq (G : ByteArray) (h : G.size.log2 + 1 ≤ 39) :
    buildW G 22 26 0 5 6 =
      { (ix0 G) with
        offs := cntOf G
        sl := (foldMins (ix0 G) G (cntOf G, zeros (5 * getU32 (cntOf G) (2 ^ 26))) (fillStep (ix0 G) G)).2
        runs := (List.range' 0 G.size).foldl (runStep G) #[] } := by
  unfold buildW
  simp only [Id.run]
  rw [if_neg (by simp [show q = 25 from rfl]; omega)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
  rw [forIn_id_foldl _ _ _ (runStep G) (fun p r => by
    unfold runStep; dsimp only; split <;> split <;> rfl)]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- Places of `l` in bucket `b`. -/
def cntB (bk : Nat → Nat) (l : List Nat) (b : Nat) : Nat := (l.filter (fun x => bk x == b)).length

/-- Where bucket `j` starts. -/
def offF (bk : Nat → Nat) (l : List Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => offF bk l j + cntB bk l j

theorem cntB_cons (bk : Nat → Nat) (x : Nat) (l : List Nat) (b : Nat) :
    cntB bk (x :: l) b = cntB bk l b + (if bk x = b then 1 else 0) := by
  unfold cntB; by_cases h : bk x = b <;> simp [List.filter_cons, h]

theorem cntB_append (bk : Nat → Nat) (l l' : List Nat) (b : Nat) :
    cntB bk (l ++ l') b = cntB bk l b + cntB bk l' b := by
  unfold cntB; simp [List.filter_append]

theorem offF_cons (bk : Nat → Nat) (x : Nat) (l : List Nat) :
    ∀ j, offF bk (x :: l) j = offF bk l j + (if bk x < j then 1 else 0) := by
  intro j
  induction j with
  | zero => simp [offF]
  | succ j ih =>
    simp only [offF, ih, cntB_cons]
    by_cases h1 : bk x < j
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; omega
    · by_cases h2 : bk x = j
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]; omega
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]; omega

theorem offF_all (bk : Nat → Nat) (nb : Nat) : ∀ l : List Nat, (∀ x ∈ l, bk x < nb) → offF bk l nb = l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    have : ∀ j, offF bk [] j = 0 := fun j => by
      induction j with
      | zero => rfl
      | succ n ih => simp [offF, cntB, ih]
    exact this nb
  | cons x l ih =>
    intro h
    rw [offF_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), if_pos (h x List.mem_cons_self)]
    rfl

theorem offF_mono (bk : Nat → Nat) (l : List Nat) (j : Nat) : ∀ d, offF bk l j ≤ offF bk l (j + d) := by
  intro d
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => rw [← Nat.add_assoc, offF]; omega

theorem count_fold (bk : Nat → Nat) (nb : Nat) :
    ∀ (l : List Nat) (cnt : ByteArray), cnt.size = 4 * (nb + 1) → (∀ x ∈ l, bk x < nb) →
      (∀ j, getU32 cnt j + l.length < 2 ^ 32) →
      (l.foldl (fun cnt x => setU32 cnt (bk x + 1) (getU32 cnt (bk x + 1) + 1)) cnt).size = 4 * (nb + 1) ∧
      ∀ j, getU32 (l.foldl (fun cnt x => setU32 cnt (bk x + 1) (getU32 cnt (bk x + 1) + 1)) cnt) j =
        getU32 cnt j + (if j = 0 then 0 else cntB bk l (j - 1)) := by
  intro l
  induction l with
  | nil => intro cnt hs _ _; simp [cntB, hs]
  | cons x l ih =>
    intro cnt hs hb hl
    have hx := hb x List.mem_cons_self
    have hs' : 4 * (bk x + 1) + 3 < cnt.size := by omega
    obtain ⟨i1, i2⟩ := ih (setU32 cnt (bk x + 1) (getU32 cnt (bk x + 1) + 1)) (by rw [size_setU32, hs])
      (fun y hy => hb y (List.mem_cons_of_mem _ hy)) (fun j => by
        rw [getU32_setU32 _ _ _ _ hs']; have := hl j; have := hl (bk x + 1)
        simp only [List.length_cons] at *
        split <;> omega)
    refine ⟨i1, fun j => ?_⟩
    rw [List.foldl_cons, i2, getU32_setU32 _ _ _ _ hs', cntB_cons]
    have := hl j; have := hl (bk x + 1)
    simp only [List.length_cons] at *
    by_cases hj : j = bk x + 1
    · subst hj; rw [if_pos rfl, Nat.mod_eq_of_lt (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]; omega
    · rw [if_neg hj]
      by_cases j0 : j = 0
      · simp [j0]
      · rw [if_neg j0, if_neg j0, if_neg (by omega)]; omega

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem sum_fold (bk : Nat → Nat) (nb : Nat) (l : List Nat) (cnt1 : ByteArray) (hs : cnt1.size = 4 * (nb + 1))
    (h1 : ∀ j ≤ nb, getU32 cnt1 j = if j = 0 then 0 else cntB bk l (j - 1)) (hlt : offF bk l nb < 2 ^ 32) :
    ∀ m ≤ nb, ((List.range' 0 m).foldl sumStep cnt1).size = 4 * (nb + 1) ∧
      ∀ j ≤ nb, getU32 ((List.range' 0 m).foldl sumStep cnt1) j =
        if j ≤ m then offF bk l j else cntB bk l (j - 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨hs, fun j hj => ?_⟩
    simp only [List.range'_zero, List.foldl_nil, h1 j hj]
    by_cases j0 : j = 0
    · subst j0; simp [offF]
    · rw [if_neg j0, if_neg (by omega)]
  | succ m ih =>
    intro hm
    obtain ⟨i1, i2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    have hs' : 4 * (m + 1) + 3 < ((List.range' 0 m).foldl sumStep cnt1).size := by omega
    refine ⟨by rw [sumStep, size_setU32, i1], fun j hj => ?_⟩
    rw [sumStep, getU32_setU32 _ _ _ _ hs', i2 (m + 1) hm, i2 m (by omega), if_pos (Nat.le_refl m),
      if_neg (show ¬ m + 1 ≤ m by omega), show m + 1 - 1 = m by omega]
    have hmono := offF_mono bk l (m + 1) (nb - (m + 1))
    rw [show m + 1 + (nb - (m + 1)) = nb by omega] at hmono
    by_cases hj1 : j = m + 1
    · subst hj1; rw [if_pos rfl, if_pos (Nat.le_refl _), offF, Nat.mod_eq_of_lt (by rw [offF] at hmono; omega)]; omega
    · rw [if_neg hj1, i2 _ hj]
      by_cases hjm : j ≤ m
      · rw [if_pos hjm, if_pos (by omega)]
      · rw [if_neg hjm, if_neg (by omega)]

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- Places of `l` in bucket `b`, in order. -/
def inB (bk : Nat → Nat) (l : List Nat) (b : Nat) : List Nat := l.filter (fun x => bk x == b)

theorem length_inB (bk : Nat → Nat) (l : List Nat) (b : Nat) : (inB bk l b).length = cntB bk l b := rfl

theorem inB_append_single (bk : Nat → Nat) (l : List Nat) (x b : Nat) :
    inB bk (l ++ [x]) b = inB bk l b ++ (if bk x = b then [x] else []) := by
  unfold inB; by_cases h : bk x = b <;> simp [List.filter_append, h]

theorem getD_append_left' (l l' : List Nat) (r : Nat) (h : r < l.length) : (l ++ l').getD r 0 = l.getD r 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

def fillG (bk : Nat → Nat) (sv : Nat → UInt64) (st : ByteArray × ByteArray) (x : Nat) : ByteArray × ByteArray :=
  (setU32 st.1 (bk x) (getU32 st.1 (bk x) + 1), wrLE st.2 (5 * getU32 st.1 (bk x)) (sv x) 5)

/-- After the places `P` (a prefix of `E`) are written. -/
def FillInv (bk : Nat → Nat) (sv : Nat → UInt64) (nb : Nat) (E P : List Nat) (st : ByteArray × ByteArray) : Prop :=
  st.1.size = 4 * (nb + 1) ∧ st.2.size = 5 * E.length ∧
    (∀ b < nb, getU32 st.1 b = offF bk E b + cntB bk P b) ∧
    (∀ b < nb, ∀ r < cntB bk P b, rdSlot st.2 5 (offF bk E b + r) = (sv ((inB bk P b).getD r 0)).toNat % 2 ^ 40)

theorem fill_step (bk : Nat → Nat) (sv : Nat → UInt64) (nb : Nat) (E P l : List Nat) (x : Nat)
    (hE : P ++ x :: l = E) (hb : ∀ y ∈ E, bk y < nb) (hlen : E.length < 2 ^ 32)
    (st : ByteArray × ByteArray) (h : FillInv bk sv nb E P st) :
    FillInv bk sv nb E (P ++ [x]) (fillG bk sv st x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hx : bk x < nb := hb x (by rw [← hE]; simp)
  have hcE : ∀ b, cntB bk E b = cntB bk P b + cntB bk (x :: l) b := fun b => by rw [← hE, cntB_append]
  have hcx : ∀ b, cntB bk (P ++ [x]) b = cntB bk P b + (if bk x = b then 1 else 0) := fun b => by
    rw [cntB_append]; unfold cntB; by_cases e : bk x = b <;> simp [e]
  have hnb := offF_all bk nb E hb
  have hoff : ∀ b, b < nb → offF bk E b + cntB bk E b ≤ E.length := fun b hb' => by
    have := offF_mono bk E (b + 1) (nb - (b + 1)); rw [show b + 1 + (nb - (b + 1)) = nb by omega, offF] at this; omega
  have hlt : ∀ b b', b < b' → offF bk E b + cntB bk E b ≤ offF bk E b' := fun b b' hbb => by
    have := offF_mono bk E (b + 1) (b' - (b + 1)); rw [show b + 1 + (b' - (b + 1)) = b' by omega, offF] at this; omega
  have hcx0 : cntB bk (x :: l) (bk x) ≥ 1 := by rw [cntB_cons, if_pos rfl]; omega
  have ht := h3 (bk x) hx
  have hcE0 := hcE (bk x)
  have hoff0 := hoff (bk x) hx
  have hs1 : 4 * bk x + 3 < st.1.size := by omega
  have hs2 : 5 * getU32 st.1 (bk x) + 5 ≤ st.2.size := by rw [ht, h2]; omega
  refine ⟨by simp [fillG, size_setU32, h1], by simp [fillG, size_wrLE, h2], fun b hb' => ?_, fun b hb' r hr => ?_⟩
  · simp only [fillG]
    rw [getU32_setU32 _ _ _ _ hs1, hcx]
    by_cases e : b = bk x
    · subst e; rw [if_pos rfl, if_pos rfl, ht, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [if_neg e, if_neg (Ne.symm e), h3 b hb']; rfl
  · simp only [fillG]
    rw [inB_append_single]
    rw [hcx] at hr
    by_cases e : b = bk x ∧ r = cntB bk P b
    · obtain ⟨e1, e2⟩ := e
      subst e1 e2
      rw [ht, rdSlot5_wrLE_self _ _ _ (by rw [← ht]; exact hs2), if_pos rfl,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_inB]; exact Nat.le_refl _)]
      simp [length_inB]
    · have hrP : r < cntB bk P b := by
        by_cases e' : b = bk x
        · subst e'; rw [if_pos rfl] at hr; omega
        · rw [if_neg (Ne.symm e')] at hr; omega
      have hcEb := hcE b
      have hob := hoff b hb'
      rw [rdSlot5_wrLE_ne _ _ _ _ hs2 (by
          rw [ht]
          intro heq
          by_cases e' : b = bk x
          · subst e'; omega
          · rcases Nat.lt_or_gt_of_ne e' with e' | e'
            · have := hlt b (bk x) e'; omega
            · have := hlt (bk x) b e'; omega) (by rw [h2]; omega),
        h4 b hb' r hrP, getD_append_left' _ _ _ (by rw [length_inB]; exact hrP)]

theorem fill_fold (bk : Nat → Nat) (sv : Nat → UInt64) (nb : Nat) (E : List Nat)
    (hb : ∀ y ∈ E, bk y < nb) (hlen : E.length < 2 ^ 32) :
    ∀ l P st, P ++ l = E → FillInv bk sv nb E P st → FillInv bk sv nb E E (l.foldl (fillG bk sv) st) := by
  intro l
  induction l with
  | nil => intro P st hE h; simp at hE; subst hE; exact h
  | cons x l ih =>
    intro P st hE h
    exact ih (P ++ [x]) _ (by rw [← hE]; simp) (fill_step bk sv nb E P l x hE hb hlen st h)

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem wcU_acgt (B : ByteArray) (n : Nat) : ∀ i x, (∀ t < n, acgt (B.get! (i + t)) = true) →
    (wcU B i (i + n) x).toNat = (x.toNat * 4 ^ n + wc B i n) % 2 ^ 64 := by
  induction n with
  | zero =>
    intro i x _
    rw [wcU, if_neg (by omega)]
    simp [wc, Nat.mod_eq_of_lt x.toNat_lt]
  | succ n ih =>
    intro i x hA
    rw [wcU, if_pos (by omega)]
    dsimp only
    rw [if_pos (by simpa using hA 0 (by omega)), show i + (n + 1) = (i + 1) + n by omega,
      ih (i + 1) _ (fun t ht => by rw [show i + 1 + t = i + (t + 1) by omega]; exact hA _ (by omega))]
    have hw := wc_add B i 1 n
    have h1' : wc B i 1 = byteCode (B.get! i) := by simp [wc]
    rw [Nat.add_comm 1 n, h1'] at hw
    rw [hw]
    have hc := byteCode_lt (B.get! i)
    have e : (x * 4 + (byteCode (B.get! i)).toUInt64).toNat = (x.toNat * 4 + byteCode (B.get! i)) % 2 ^ 64 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]
      simp only [Nat.toUInt64, UInt64.toNat_ofNat', show (4 : UInt64).toNat = 4 from rfl]
      rw [Nat.mod_eq_of_lt (show byteCode (B.get! i) < 2 ^ 64 by omega)]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [e, Nat.pow_succ]
    have key : ∀ a P W M : Nat, ((a % M) * P + W) % M = (a * P + W) % M := by
      intro a P W M; rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    rw [key]
    congr 1
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 4 (4 ^ n), Nat.add_assoc, Nat.pow_succ]

/-- The k-word at an indexed place: its code (all ACGT, so not `BADU`). -/
theorem wcU_word (G : ByteArray) (y : Nat) (hA : ∀ t < 22, acgt (G.get! (y + t)) = true) :
    wcU G y (y + 22) 0 ≠ BADU ∧ (wcU G y (y + 22) 0).toNat = wc G y 22 := by
  have e := wcU_acgt G 22 y 0 hA
  have hl := wc_lt G y 22
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add] at e
  have h22 : (4 : Nat) ^ 22 < 2 ^ 64 := by decide
  rw [Nat.mod_eq_of_lt (by omega)] at e
  refine ⟨fun h => ?_, e⟩
  rw [h] at e
  have : (4 : Nat) ^ 22 < 2 ^ 64 - 1 := by decide
  rw [show BADU.toNat = 2 ^ 64 - 1 from rfl] at e
  omega

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem kf_ix0 (G : ByteArray) : (ix0 G).kf = min 18 (40 - (G.size.log2 + 1)) := by
  simp [mkIdx]

theorem allA_nil (B : ByteArray) (i : Nat) : allA B i i = true := by rw [allA, if_neg (Nat.lt_irrefl _)]

theorem wcGo_nil (B : ByteArray) (i x : Nat) : wcGo B i i x = x := by rw [wcGo, if_neg (Nat.lt_irrefl _)]

theorem lt_pow_log2 (n : Nat) : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self

/-- The slot of an indexed place `x`: `x · 2^kf + key`, below `2^40`. -/
theorem slotAt_ix0 (G : ByteArray) (hpb : G.size.log2 + 1 ≤ 39) (x h : Nat) (hx : x + 22 ≤ G.size) :
    (slotAt (ix0 G) G x h).toNat = x * 2 ^ (ix0 G).kf + h % 2 ^ (ix0 G).kf ∧
      x * 2 ^ (ix0 G).kf + h % 2 ^ (ix0 G).kf < 2 ^ 40 := by
  have hkf := kf_ix0 G
  unfold slotAt
  have hgood : (decide ((ix0 G).c ≤ x) && decide (x + (ix0 G).k + (ix0 G).c ≤ G.size) &&
      allA G (x - (ix0 G).c) x && allA G (x + (ix0 G).k) (x + (ix0 G).k + (ix0 G).c)) = true := by
    simp only [show (ix0 G).c = 0 from rfl, show (ix0 G).k = 22 from rfl, Nat.sub_zero, Nat.add_zero, allA_nil]
    simp [hx]
  dsimp only
  rw [if_pos hgood]
  simp only [show (ix0 G).c = 0 from rfl, show (ix0 G).k = 22 from rfl, Nat.sub_zero, Nat.add_zero, wcGo_nil,
    show (ix0 G).T = (ix0 G).kf from by simp [mkIdx], show (ix0 G).kbM = 2 ^ (ix0 G).kf - 1 from rfl]
  generalize (ix0 G).kf = kf at hkf
  have hxl : x < 2 ^ (G.size.log2 + 1) := Nat.lt_of_lt_of_le (by omega) (Nat.le_of_lt (lt_pow_log2 G.size))
  have hb : x * 2 ^ kf < 2 ^ 40 := by
    calc x * 2 ^ kf < 2 ^ (G.size.log2 + 1) * 2 ^ kf := Nat.mul_lt_mul_of_pos_right hxl (Nat.pow_pos (by omega))
      _ = 2 ^ (G.size.log2 + 1 + kf) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk : h % 2 ^ kf < 2 ^ kf := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hb2 : x * 2 ^ kf + h % 2 ^ kf < 2 ^ 40 := by
    have : x * 2 ^ kf + 2 ^ kf ≤ 2 ^ 40 := by
      have h1 : (x + 1) * 2 ^ kf ≤ 2 ^ 40 := by
        calc (x + 1) * 2 ^ kf ≤ 2 ^ (G.size.log2 + 1) * 2 ^ kf := Nat.mul_le_mul_right _ hxl
          _ = 2 ^ (G.size.log2 + 1 + kf) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
    omega
  refine ⟨?_, hb2⟩
  have hk18 : kf ≤ 18 := by omega
  have hx39 : x < 2 ^ 39 := Nat.lt_of_lt_of_le hxl (Nat.pow_le_pow_right (by omega) hpb)
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, Nat.toUInt64, UInt64.toNat_ofNat', UInt64.toNat_and,
    Nat.shiftLeft_eq, show (0 : Nat) % 2 ^ 64 = 0 from rfl, Nat.zero_mul, Nat.zero_mod, Nat.or_zero, and_mask_eq]
  rw [Nat.mod_eq_of_lt (show kf < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show kf < 64 by omega),
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show x * 2 ^ kf < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show h % 2 ^ kf < 2 ^ 64 by
      have : 2 ^ kf ≤ 2 ^ 18 := Nat.pow_le_pow_right (by omega) hk18
      omega), Nat.or_comm, or_add _ _ _ hk]
  omega

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

/-- The places the builder indexes (and `checkComp` visits). -/
abbrev EG (G : ByteArray) : List Nat := evs (ix0 G) G 0 (G.size + 1 - q) 0
/-- Bucket of place `x`. -/
abbrev bkG (G : ByteArray) (x : Nat) : Nat := (ix0 G).hsh (wc G x 22) >>> 18
/-- Slot of place `x`. -/
abbrev svG (G : ByteArray) (x : Nat) : UInt64 := slotAt (ix0 G) G x ((ix0 G).hsh (wc G x 22))

theorem good_ix0 (G : ByteArray) : Good (ix0 G) := good_of_checkParams _ (checkParams_ix0 _)

theorem pb_le (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : G.size.log2 + 1 ≤ 39 := by
  by_cases h0 : G.size = 0
  · rw [h0]; decide
  · have : G.size.log2 < 33 := (Nat.log2_lt h0).mpr (by omega)
    omega

theorem acgt_zero : acgt 0 = false := by decide

theorem EG_length (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : (EG G).length < 2 ^ 32 := by
  have := evs_length (ix0 G) G (G.size + 1 - q) 0 0
  have hq : q = 25 := rfl
  show (evs (ix0 G) G 0 (G.size + 1 - q) 0).length < _
  omega

theorem EG_mem (G : ByteArray) (x : Nat) (hx : x ∈ EG G) :
    x + 22 ≤ G.size ∧ ∀ t < 22, acgt (G.get! (x + t)) = true := by
  obtain ⟨s, _, hA, rfl⟩ := evs_mem _ _ _ _ _ _ hx
  have hA' := (allA_iff G q s).mp hA
  have hm := mini_lt (good_ix0 G) (wcGo G s (s + q) 0)
  have hw : (ix0 G).w = 4 := rfl
  have hq : q = 25 := rfl
  have hs : s + q ≤ G.size := by
    apply Classical.byContradiction; intro hlt
    have := hA' (q - 1) (by omega)
    rw [get!_ge _ _ (by omega), acgt_zero] at this; cases this
  unfold pmOf
  refine ⟨by omega, fun t ht => ?_⟩
  have := hA' ((ix0 G).mini (wcGo G s (s + q) 0) + t) (by omega)
  rwa [← Nat.add_assoc] at this

theorem EG_sorted (G : ByteArray) : (EG G).Pairwise (· < ·) :=
  (evs_sorted (ix0 G) rfl rfl rfl G _ 0 0 (Nat.zero_le _)).2

theorem bkG_lt (G : ByteArray) (x : Nat) : bkG G x < 2 ^ 26 := bucket_lt (good_ix0 G) _

theorem cntOf_spec (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) :
    (cntOf G).size = 4 * (2 ^ 26 + 1) ∧ ∀ j ≤ 2 ^ 26, getU32 (cntOf G) j = offF (bkG G) (EG G) j := by
  have hlen := EG_length G hsz
  have hfm : foldMins (ix0 G) G (zeros (4 * (2 ^ 26 + 1))) (cntStep (ix0 G)) =
      (EG G).foldl (fun cnt x => setU32 cnt (bkG G x + 1) (getU32 cnt (bkG G x + 1) + 1))
        (zeros (4 * (2 ^ 26 + 1))) := by
    rw [foldMins_evs _ (good_ix0 G)]; rfl
  obtain ⟨c1, c2⟩ := count_fold (bkG G) (2 ^ 26) (EG G) (zeros (4 * (2 ^ 26 + 1))) (size_zeros _)
    (fun x _ => bkG_lt G x) (fun j => by rw [getU32_zeros]; omega)
  have hall := offF_all (bkG G) (2 ^ 26) (EG G) (fun x _ => bkG_lt G x)
  obtain ⟨s1, s2⟩ := sum_fold (bkG G) (2 ^ 26) (EG G) _ c1 (fun j _ => by rw [c2, getU32_zeros]; omega)
    (by omega) (2 ^ 26) (Nat.le_refl _)
  unfold cntOf
  rw [hfm]
  exact ⟨s1, fun j hj => by rw [s2 j hj, if_pos hj]⟩

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

def slOf (G : ByteArray) : ByteArray :=
  (foldMins (ix0 G) G (cntOf G, zeros (5 * getU32 (cntOf G) (2 ^ 26))) (fillStep (ix0 G) G)).2

def runsOf (G : ByteArray) : Array Nat := (List.range' 0 G.size).foldl (runStep G) #[]

/-- The index `buildW` returns (`buildW_eq`). -/
def ixB (G : ByteArray) : MzIdx :=
  { (ix0 G) with
    offs := cntOf G
    sl := slOf G
    runs := runsOf G }

theorem slOf_spec (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) :
    (slOf G).size = 5 * (EG G).length ∧
    ∀ b < 2 ^ 26, ∀ r < cntB (bkG G) (EG G) b,
      rdSlot (slOf G) 5 (offF (bkG G) (EG G) b + r) = (svG G ((inB (bkG G) (EG G) b).getD r 0)).toNat % 2 ^ 40 := by
  obtain ⟨c1, c2⟩ := cntOf_spec G hsz
  have hall := offF_all (bkG G) (2 ^ 26) (EG G) (fun x _ => bkG_lt G x)
  have hfm : foldMins (ix0 G) G (cntOf G, zeros (5 * getU32 (cntOf G) (2 ^ 26))) (fillStep (ix0 G) G) =
      (EG G).foldl (fillG (bkG G) (svG G)) (cntOf G, zeros (5 * getU32 (cntOf G) (2 ^ 26))) := by
    rw [foldMins_evs _ (good_ix0 G)]; rfl
  have h0 : FillInv (bkG G) (svG G) (2 ^ 26) (EG G) [] (cntOf G, zeros (5 * getU32 (cntOf G) (2 ^ 26))) := by
    unfold FillInv
    dsimp only
    refine ⟨c1, ?_, fun b hb => ?_, fun b _ r hr => ?_⟩
    · rw [size_zeros, c2 _ (Nat.le_refl _), hall]
    · rw [c2 _ (by omega)]; rfl
    · exact absurd hr (Nat.not_lt_zero _)
  obtain ⟨_, f2, _, f4⟩ := fill_fold (bkG G) (svG G) (2 ^ 26) (EG G) (fun x _ => bkG_lt G x) (EG_length G hsz)
    (EG G) [] _ rfl h0
  unfold slOf
  rw [hfm]
  exact ⟨f2, f4⟩

theorem T_ix0 (G : ByteArray) : (ix0 G).T = (ix0 G).kf := by simp [mkIdx]

end MapSpec.Mz.BO
namespace MapSpec.Mz.BO
theorem ixB_T (G : ByteArray) : (ixB G).T = (ix0 G).T := by dsimp only [ixB]
theorem ixB_tM (G : ByteArray) : (ixB G).tM = (ix0 G).tM := by dsimp only [ixB]
theorem tM_ix0 (G : ByteArray) : (ix0 G).tM = 2 ^ (ix0 G).kf - 1 := by simp [mkIdx]

theorem posOf_def (ix : MzIdx) (e : Nat) : ix.posOf e = e >>> ix.T := rfl
theorem tagOf_def (ix : MzIdx) (e : Nat) : ix.tagOf e = e &&& ix.tM := rfl

theorem posOf_slot (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) (x : Nat) (hx : x + 22 ≤ G.size) :
    (ixB G).posOf ((svG G x).toNat % 2 ^ 40) = x ∧
    (ixB G).tagOf ((svG G x).toNat % 2 ^ 40) = (ix0 G).hsh (wc G x 22) % 2 ^ (ix0 G).kf := by
  obtain ⟨e1, e2⟩ := slotAt_ix0 G (pb_le G hsz) x ((ix0 G).hsh (wc G x 22)) hx
  have e1' : (svG G x).toNat = x * 2 ^ (ix0 G).kf + (ix0 G).hsh (wc G x 22) % 2 ^ (ix0 G).kf := e1
  rw [e1']
  have e3 := Nat.mod_eq_of_lt e2
  rw [e3]
  have hk : (ix0 G).hsh (wc G x 22) % 2 ^ (ix0 G).kf < 2 ^ (ix0 G).kf := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [posOf_def, tagOf_def]
  rw [ixB_T, ixB_tM, T_ix0, tM_ix0, shiftRight_eq, and_mask_eq]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hk, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem ixB_offs (G : ByteArray) : (ixB G).offs = cntOf G := by dsimp only [ixB]
theorem ixB_sl (G : ByteArray) : (ixB G).sl = slOf G := by dsimp only [ixB]
theorem ixB_runs (G : ByteArray) : (ixB G).runs = runsOf G := by dsimp only [ixB]
theorem ixB_sw (G : ByteArray) : (ixB G).sw = 5 := by dsimp only [ixB]; rfl
theorem ixB_ob (G : ByteArray) : (ixB G).ob = 0 := by dsimp only [ixB]; rfl
theorem ixB_k (G : ByteArray) : (ixB G).k = 22 := by dsimp only [ixB]; rfl
theorem ixB_kb (G : ByteArray) : (ixB G).kb = 18 := by dsimp only [ixB]; rfl
theorem ixB_B (G : ByteArray) : (ixB G).B = 26 := by dsimp only [ixB]; rfl
theorem ixB_c (G : ByteArray) : (ixB G).c = 0 := by dsimp only [ixB]; rfl
theorem ixB_kbM (G : ByteArray) : (ixB G).kbM = 2 ^ (ix0 G).kf - 1 := by dsimp only [ixB]; rfl
theorem ixB_fM (G : ByteArray) : (ixB G).fM = 0 := by dsimp only [ixB]; rfl
theorem ixB_fsh (G : ByteArray) : (ixB G).fsh = (ix0 G).kf := by dsimp only [ixB]; simp [mkIdx]
theorem ixB_hsh (G : ByteArray) (x : Nat) : (ixB G).hsh x = (ix0 G).hsh x := by dsimp only [ixB, MzIdx.hsh]
theorem ixB_mini (G : ByteArray) (v : Nat) : (ixB G).mini v = (ix0 G).mini v := by dsimp only [ixB, MzIdx.mini]
theorem checkParams_with (ix : MzIdx) (o s : ByteArray) (r : Array Nat) :
    checkParams { ix with offs := o, sl := s, runs := r } = checkParams ix := rfl
theorem ixB_checkParams (G : ByteArray) : checkParams (ixB G) = true := by
  dsimp only [ixB]; rw [checkParams_with]; exact checkParams_ix0 _

theorem slot_def (ix : MzIdx) (t : Nat) : ix.slot t = rdSlot ix.sl ix.sw t := rfl
theorem loB_def (ix : MzIdx) (b : Nat) : ix.loB b = getU32 ix.offs (ix.ob + b) := rfl
theorem hiB_def (ix : MzIdx) (b : Nat) : ix.hiB b = getU32 ix.offs (ix.ob + b + 1) := rfl

theorem inB_mid (bk : Nat → Nat) (P l : List Nat) (x : Nat) :
    inB bk (P ++ x :: l) (bk x) = inB bk P (bk x) ++ x :: inB bk l (bk x) := by
  simp [inB, List.filter_append, List.filter_cons]

theorem cntB_nil (bk : Nat → Nat) (b : Nat) : cntB bk [] b = 0 := rfl

theorem offF_succ (bk : Nat → Nat) (l : List Nat) (j : Nat) : offF bk l (j + 1) = offF bk l j + cntB bk l j := rfl

theorem cntB_single (bk : Nat → Nat) (x b : Nat) : cntB bk [x] b = if bk x = b then 1 else 0 := by
  rw [cntB_cons, cntB_nil, Nat.zero_add]

theorem upd_step (fill : ByteArray) (b0 : Nat) (f g : Nat → Nat) (hs : 4 * b0 + 3 < fill.size)
    (hlt : f b0 + g b0 + 1 < 2 ^ 32) (h : ∀ b < 2 ^ 26, getU32 fill b = f b + g b) :
    ∀ b < 2 ^ 26, getU32 (setU32 fill b0 (f b0 + g b0 + 1)) b = f b + (g b + if b0 = b then 1 else 0) := by
  intro b hb
  rw [getU32_setU32 _ _ _ _ hs]
  by_cases e : b = b0
  · subst e; rw [if_pos rfl, if_pos rfl, Nat.mod_eq_of_lt hlt]; omega
  · rw [if_neg e, if_neg (Ne.symm e), h b hb, Nat.add_zero]

theorem getD_mid (P l : List Nat) (x : Nat) : (P ++ x :: l).getD P.length 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]; simp

/-- The checker's completeness pass, along the builder's places. -/
theorem replay_ok (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) :
    ∀ l P fill, P ++ l = EG G → fill.size = 4 * (2 ^ 26 + 1) → (∀ b < 2 ^ 26, getU32 fill b = offF (bkG G) (EG G) b + cntB (bkG G) P b) →
      replay (ixB G) G fill l = true := by
  obtain ⟨c1, c2⟩ := cntOf_spec G hsz
  obtain ⟨s1, s2⟩ := slOf_spec G hsz
  have hlen := EG_length G hsz
  have hall := offF_all (bkG G) (2 ^ 26) (EG G) (fun x _ => bkG_lt G x)
  intro l
  induction l with
  | nil => intro _ _ _ _ _; rfl
  | cons x l ih =>
    intro P fill hE hfs hf
    have hxE : x ∈ EG G := by rw [← hE]; simp
    obtain ⟨hx22, _⟩ := EG_mem G x hxE
    have hb := bkG_lt G x
    have hcE : cntB (bkG G) (EG G) (bkG G x) = cntB (bkG G) P (bkG G x) + cntB (bkG G) (x :: l) (bkG G x) := by
      rw [← hE, cntB_append]
    have hcx : cntB (bkG G) (x :: l) (bkG G x) ≥ 1 := by rw [cntB_cons, if_pos rfl]; omega
    have hs4 : 4 * bkG G x + 3 < fill.size := by omega
    simp only [replay]
    rw [ixB_k, wcGo_zero, ixB_hsh, ixB_kb, show (ix0 G).hsh (wc G x 22) >>> 18 = bkG G x from rfl,
      loB_def, hiB_def, ixB_ob, ixB_offs, Nat.zero_add, c2 _ (by omega), c2 _ (by omega), hf _ hb, slot_def,
      ixB_sl, ixB_sw, s2 _ hb _ (by omega)]
    have hinB : (inB (bkG G) (EG G) (bkG G x)).getD (cntB (bkG G) P (bkG G x)) 0 = x := by
      have := getD_mid (inB (bkG G) P (bkG G x)) (inB (bkG G) l (bkG G x)) x
      rw [length_inB] at this
      rw [← hE, inB_mid, this]
    rw [hinB, (posOf_slot G hsz x hx22).1, offF_succ]
    simp only [decide_eq_true (Nat.le_add_right _ _), decide_eq_true (show offF (bkG G) (EG G) (bkG G x) +
      cntB (bkG G) P (bkG G x) < offF (bkG G) (EG G) (bkG G x) + cntB (bkG G) (EG G) (bkG G x) by omega),
      beq_self_eq_true, Bool.true_and]
    have hE' : P ++ [x] ++ l = EG G := by rw [← hE]; simp
    have hfs' : (setU32 fill (bkG G x) (offF (bkG G) (EG G) (bkG G x) + cntB (bkG G) P (bkG G x) + 1)).size = 4 * (2 ^ 26 + 1) := by
      rw [size_setU32, hfs]
    refine ih (P ++ [x]) _ hE' hfs' (fun b hb' => ?_)
    have hmo := offF_mono (bkG G) (EG G) (bkG G x + 1) (2 ^ 26 - (bkG G x + 1))
    rw [show bkG G x + 1 + (2 ^ 26 - (bkG G x + 1)) = 2 ^ 26 by omega, hall] at hmo
    have hof := offF_succ (bkG G) (EG G) (bkG G x)
    rw [cntB_append, cntB_single]
    exact upd_step fill (bkG G x) (offF (bkG G) (EG G)) (cntB (bkG G) P) hs4 (by omega) hf b hb'

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem checkBucket_of (ix : MzIdx) (G : ByteArray) (b hi : Nat) :
    ∀ n t, (∀ t', t ≤ t' → t' < t + n → entryOk ix G b hi t' = true) → checkBucket ix G b hi n t = true := by
  intro n
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
    intro t h
    simp only [checkBucket, Bool.and_eq_true]
    exact ⟨h t (Nat.le_refl _) (by omega), ih (t + 1) (fun t' h1 h2 => h t' (by omega) (by omega))⟩

theorem checkSound_of (ix : MzIdx) (G : ByteArray) :
    ∀ n b, (∀ b', b ≤ b' → b' < b + n →
      checkBucket ix G b' (ix.hiB b') (ix.hiB b' - ix.loB b') (ix.loB b') = true) → checkSound ix G n b = true := by
  intro n
  induction n with
  | zero => intro b _; rfl
  | succ n ih =>
    intro b h
    simp only [checkSound, Bool.and_eq_true]
    exact ⟨h b (Nat.le_refl _) (by omega), ih (b + 1) (fun b' h1 h2 => h b' (by omega) (by omega))⟩

theorem getD_mem_inB (bk : Nat → Nat) (E : List Nat) (b r : Nat) (hr : r < cntB bk E b) :
    (inB bk E b).getD r 0 ∈ E ∧ bk ((inB bk E b).getD r 0) = b := by
  rw [← length_inB] at hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  have := List.getElem_mem hr
  unfold inB at this
  rw [List.mem_filter, beq_iff_eq] at this
  exact this

theorem getD_inB_lt (bk : Nat → Nat) (E : List Nat) (hs : E.Pairwise (· < ·)) (b r : Nat)
    (hr : r + 1 < cntB bk E b) : (inB bk E b).getD r 0 < (inB bk E b).getD (r + 1) 0 := by
  rw [← length_inB] at hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  have hp : (inB bk E b).Pairwise (· < ·) := hs.filter _
  exact List.pairwise_iff_getElem.mp hp r (r + 1) (by omega) hr (by omega)

theorem befF_def (ix : MzIdx) (tg : Nat) : ix.befF tg = (tg >>> ix.bsh) &&& ix.fM := rfl
theorem aftF_def (ix : MzIdx) (tg : Nat) : ix.aftF tg = (tg >>> ix.ash) &&& ix.fM := rfl
theorem flagF_def (ix : MzIdx) (tg : Nat) : ix.flagF tg = tg >>> ix.fsh := rfl
theorem keyF_def (ix : MzIdx) (tg : Nat) : ix.keyF tg = tg &&& ix.kbM := rfl
theorem wcU_nil (B : ByteArray) (i : Nat) (x : UInt64) : wcU B i i x = x := by rw [wcU, if_neg (Nat.lt_irrefl _)]

theorem entryOk_gen (ix : MzIdx) (G : ByteArray) (b hi t y H kf : Nat)
    (hpos : ix.posOf (ix.slot t) = y) (htag : ix.tagOf (ix.slot t) = H % 2 ^ kf)
    (hk : ix.k = 22) (hc : ix.c = 0) (hkb : ix.kb = 18) (hkbM : ix.kbM = 2 ^ kf - 1) (hfsh : ix.fsh = kf)
    (hfM : ix.fM = 0) (hh : ix.hsh (wc G y 22) = H) (hb : H >>> 18 = b) (hy : y + 22 ≤ G.size)
    (hA : ∀ t < 22, acgt (G.get! (y + t)) = true)
    (hnext : hi ≤ t + 1 ∨ y < ix.posOf (ix.slot (t + 1))) : entryOk ix G b hi t = true := by
  obtain ⟨hw1, hw2⟩ := wcU_word G y hA
  unfold entryOk
  simp only [hpos, htag, hk, hc, Nat.sub_zero, Nat.add_zero, wcU_nil, hw2, hh, hkb, hb, keyF_def, flagF_def,
    befF_def, aftF_def, hkbM, hfsh, hfM, and_mask_eq, Nat.mod_mod, Nat.and_zero, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq, hy, Nat.zero_le, hw1, not_false_eq_true, true_and, and_true]
  exact ⟨Or.inr ⟨⟨⟨by decide, by decide⟩, rfl⟩, rfl⟩, hnext⟩

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem entryOk_ixB (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) (b : Nat) (hb : b < 2 ^ 26) (r : Nat)
    (hr : r < cntB (bkG G) (EG G) b) :
    entryOk (ixB G) G b (offF (bkG G) (EG G) (b + 1)) (offF (bkG G) (EG G) b + r) = true := by
  obtain ⟨s1, s2⟩ := slOf_spec G hsz
  obtain ⟨hyE, hyb⟩ := getD_mem_inB (bkG G) (EG G) b r hr
  have hslot : (ixB G).slot (offF (bkG G) (EG G) b + r) = (svG G ((inB (bkG G) (EG G) b).getD r 0)).toNat % 2 ^ 40 := by
    rw [slot_def, ixB_sl, ixB_sw, s2 b hb r hr]
  generalize hy : (inB (bkG G) (EG G) b).getD r 0 = y at hyE hyb hslot
  obtain ⟨hy22, hyA⟩ := EG_mem G y hyE
  obtain ⟨p1, p2⟩ := posOf_slot G hsz y hy22
  refine entryOk_gen (ixB G) G b _ _ y ((ix0 G).hsh (wc G y 22)) (ix0 G).kf (by rw [hslot, p1]) (by rw [hslot, p2])
    (ixB_k G) (ixB_c G) (ixB_kb G) (ixB_kbM G) (ixB_fsh G) (ixB_fM G) (ixB_hsh G _) hyb hy22 hyA ?_
  by_cases hn : r + 1 < cntB (bkG G) (EG G) b
  · right
    have hlt := getD_inB_lt (bkG G) (EG G) (EG_sorted G) b r hn
    rw [hy] at hlt
    obtain ⟨hzE, _⟩ := getD_mem_inB (bkG G) (EG G) b (r + 1) hn
    obtain ⟨hz22, _⟩ := EG_mem G _ hzE
    rw [Nat.add_assoc, slot_def, ixB_sl, ixB_sw, s2 b hb (r + 1) hn, (posOf_slot G hsz _ hz22).1]
    exact hlt
  · left; rw [offF_succ]; omega

theorem checkSound_ixB (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : checkSound (ixB G) G (2 ^ (ixB G).B) 0 = true := by
  obtain ⟨c1, c2⟩ := cntOf_spec G hsz
  rw [ixB_B]
  refine checkSound_of _ _ _ _ (fun b _ hb => ?_)
  have hb' : b < 2 ^ 26 := by omega
  rw [hiB_def, loB_def, ixB_ob, ixB_offs, Nat.zero_add, c2 _ (by omega), c2 _ (by omega), offF_succ]
  refine checkBucket_of _ _ _ _ _ _ (fun t h1 h2 => ?_)
  obtain ⟨r, rfl⟩ : ∃ r, t = offF (bkG G) (EG G) b + r := ⟨t - offF (bkG G) (EG G) b, by omega⟩
  rw [← offF_succ]
  exact entryOk_ixB G hsz b hb' r (by omega)

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

def flat : List (Nat × Nat) → List Nat
  | [] => []
  | pr :: t => pr.1 :: pr.2 :: flat t

/-- A maximal run `[a, b)` of non-ACGT bytes of `G`. -/
def GoodPair (G : ByteArray) (pr : Nat × Nat) : Prop :=
  pr.1 < pr.2 ∧ pr.2 ≤ G.size ∧ (∀ x, pr.1 ≤ x → x < pr.2 → acgt (G.get! x) = false) ∧
    (pr.1 = 0 ∨ acgt (G.get! (pr.1 - 1)) = true) ∧ (pr.2 = G.size ∨ acgt (G.get! pr.2) = true)

/-- After reading `G[0, m)` a run is open: it does not end at `m`. -/
def Opn (G : ByteArray) (m : Nat) : Prop :=
  0 < m ∧ m < G.size ∧ acgt (G.get! (m - 1)) = false ∧ acgt (G.get! m) = false

/-- The runs loop after `G[0, m)`: closed runs `prs`, maybe an open one from `oa`. -/
def RInv (G : ByteArray) (m : Nat) (R : Array Nat) : Prop :=
  ∃ prs : List (Nat × Nat), ∃ oa : Option Nat,
    R.toList = flat prs ++ oa.toList ∧ (oa.isSome ↔ Opn G m) ∧ (∀ pr ∈ prs, GoodPair G pr ∧ pr.2 ≤ m) ∧
    prs.Pairwise (fun p1 p2 => p1.2 < p2.1) ∧
    (∀ a ∈ oa, a < m ∧ (∀ x, a ≤ x → x < m → acgt (G.get! x) = false) ∧
      (a = 0 ∨ acgt (G.get! (a - 1)) = true) ∧ ∀ pr ∈ prs, pr.2 < a) ∧
    (∀ x < m, acgt (G.get! x) = false → (∃ pr ∈ prs, pr.1 ≤ x ∧ x < pr.2) ∨ (∃ a ∈ oa, a ≤ x))

theorem flat_append (l l' : List (Nat × Nat)) : flat (l ++ l') = flat l ++ flat l' := by
  induction l with
  | nil => rfl
  | cons pr t ih => simp [flat, ih]

theorem RInv_step (G : ByteArray) (m : Nat) (hm : m < G.size) (R : Array Nat) (h : RInv G m R) :
    RInv G (m + 1) (runStep G R m) := by
  obtain ⟨prs, oa, hR, hopen, hprs, hsort, hoa, hcov⟩ := h
  unfold runStep
  by_cases ha : acgt (G.get! m) = true
  · -- an ACGT letter: nothing pushed, nothing open
    have hnone : oa = none := by
      cases oa with
      | none => rfl
      | some a => have := (hopen.1 rfl).2.2.2; rw [ha] at this; cases this
    subst hnone
    simp only [ha, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    refine ⟨prs, none, hR, ?_, fun pr hp => ⟨(hprs pr hp).1, by have := (hprs pr hp).2; omega⟩, hsort,
      fun a h => by simp at h, fun x hx hodd => ?_⟩
    · constructor
      · intro h; simp at h
      · intro h; have := h.2.2.1; rw [show m + 1 - 1 = m by omega, ha] at this; cases this
    have hxm : x ≠ m := fun e => by subst e; rw [ha] at hodd; cases hodd
    exact hcov x (by omega) hodd
  · have hodd : acgt (G.get! m) = false := by simpa using ha
    -- no closed run ends at `m` (the byte at `m` is not ACGT)
    have hlt : ∀ pr ∈ prs, pr.2 < m := fun pr hp => by
      obtain ⟨⟨_, _, _, _, h5⟩, h6⟩ := hprs pr hp
      rcases Nat.lt_or_eq_of_le h6 with h | h
      · exact h
      · rcases h5 with h5 | h5
        · omega
        · rw [h, hodd] at h5; cases h5
    simp only [hodd, Bool.not_false, Bool.true_and]
    by_cases hS : (m == 0 || acgt (G.get! (m - 1))) = true
    · have hnone : oa = none := by
        cases oa with
        | none => rfl
        | some a =>
          have h := (hopen.1 rfl)
          simp only [Bool.or_eq_true, beq_iff_eq] at hS
          rcases hS with hS | hS
          · have := h.1; omega
          · rw [h.2.2.1] at hS; cases hS
      subst hnone
      simp only [List.append_nil, Option.toList] at hR
      have hS' : m = 0 ∨ acgt (G.get! (m - 1)) = true := by simpa using hS
      rw [if_pos hS]
      by_cases hE : (m + 1 == G.size || acgt (G.get! (m + 1))) = true
      · have hE' : m + 1 = G.size ∨ acgt (G.get! (m + 1)) = true := by simpa using hE
        rw [if_pos hE]
        refine ⟨prs ++ [(m, m + 1)], none, ?_, ?_, ?_, ?_, fun a h => by simp at h, ?_⟩
        · simp [hR, flat_append, flat]
        · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          intro h; rcases hE' with e | e
          · have := h.2.1; omega
          · have := h.2.2.2; rw [e] at this; cases this
        · intro pr hp
          rcases List.mem_append.mp hp with hp | hp
          · exact ⟨(hprs pr hp).1, by have := (hprs pr hp).2; omega⟩
          · simp at hp; subst hp
            refine ⟨⟨by simp, by simp; omega, fun x h1 h2 => ?_, hS', hE'⟩, Nat.le_refl _⟩
            simp at h1 h2; rw [show x = m by omega]; exact hodd
        · refine List.pairwise_append.mpr ⟨hsort, by simp, fun p1 hp1 p2 hp2 => ?_⟩
          simp at hp2; subst hp2; exact hlt p1 hp1
        · intro x hx hx'
          by_cases e : x = m
          · left; exact ⟨(m, m + 1), by simp, by simp [e], by simp [e]⟩
          · rcases hcov x (by omega) hx' with ⟨pr, hp, h1, h2⟩ | ⟨a, ha', _⟩
            · left; exact ⟨pr, List.mem_append_left _ hp, h1, h2⟩
            · simp at ha'
      · have hE' : m + 1 ≠ G.size ∧ acgt (G.get! (m + 1)) = false := by simpa using hE
        rw [if_neg hE]
        refine ⟨prs, some m, ?_, ?_, fun pr hp => ⟨(hprs pr hp).1, by have := (hprs pr hp).2; omega⟩, hsort,
          ?_, ?_⟩
        · simp [hR]
        · simp only [Option.isSome_some, true_iff]
          exact ⟨by omega, by omega, by rw [show m + 1 - 1 = m by omega]; exact hodd, hE'.2⟩
        · intro a ha'; simp at ha'; subst ha'
          refine ⟨by omega, fun x h1 h2 => by rw [show x = m by omega]; exact hodd, hS', hlt⟩
        · intro x hx hx'
          by_cases e : x = m
          · right; exact ⟨m, by simp, by omega⟩
          · rcases hcov x (by omega) hx' with h | ⟨a, ha', _⟩
            · left; exact h
            · simp at ha'
    · have hS' : m ≠ 0 ∧ acgt (G.get! (m - 1)) = false := by simpa using hS
      have hO : Opn G m := ⟨by omega, hm, hS'.2, hodd⟩
      obtain ⟨a, rfl⟩ : ∃ a, oa = some a := Option.isSome_iff_exists.mp (hopen.2 hO)
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hoa a rfl
      rw [if_neg hS]
      by_cases hE : (m + 1 == G.size || acgt (G.get! (m + 1))) = true
      · have hE' : m + 1 = G.size ∨ acgt (G.get! (m + 1)) = true := by simpa using hE
        rw [if_pos hE]
        refine ⟨prs ++ [(a, m + 1)], none, ?_, ?_, ?_, ?_, fun a h => by simp at h, ?_⟩
        · simp [hR, flat_append, flat]
        · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          intro h; rcases hE' with e | e
          · have := h.2.1; omega
          · have := h.2.2.2; rw [e] at this; cases this
        · intro pr hp
          rcases List.mem_append.mp hp with hp | hp
          · exact ⟨(hprs pr hp).1, by have := (hprs pr hp).2; omega⟩
          · simp at hp; subst hp
            refine ⟨⟨by simp; omega, by simp; omega, fun x h1 h2 => ?_, ha3, hE'⟩, Nat.le_refl _⟩
            simp at h1 h2
            by_cases e : x = m
            · rw [e]; exact hodd
            · exact ha2 x h1 (by omega)
        · refine List.pairwise_append.mpr ⟨hsort, by simp, fun p1 hp1 p2 hp2 => ?_⟩
          simp at hp2; subst hp2; exact ha4 p1 hp1
        · intro x hx hx'
          by_cases e : x = m
          · left; exact ⟨(a, m + 1), by simp, by simp; omega, by simp [e]⟩
          · rcases hcov x (by omega) hx' with ⟨pr, hp, h1, h2⟩ | ⟨a', ha', h'⟩
            · left; exact ⟨pr, List.mem_append_left _ hp, h1, h2⟩
            · simp at ha'; subst ha'
              left; exact ⟨(a, m + 1), by simp, by simp; omega, by simp; omega⟩
      · have hE' : m + 1 ≠ G.size ∧ acgt (G.get! (m + 1)) = false := by simpa using hE
        rw [if_neg hE]
        refine ⟨prs, some a, hR, ?_, fun pr hp => ⟨(hprs pr hp).1, by have := (hprs pr hp).2; omega⟩, hsort,
          ?_, ?_⟩
        · simp only [Option.isSome_some, true_iff]
          exact ⟨by omega, by omega, by rw [show m + 1 - 1 = m by omega]; exact hodd, hE'.2⟩
        · intro a' ha'; simp at ha'; subst ha'
          refine ⟨by omega, fun x h1 h2 => ?_, ha3, ha4⟩
          by_cases e : x = m
          · rw [e]; exact hodd
          · exact ha2 x h1 (by omega)
        · intro x hx hx'
          by_cases e : x = m
          · right; exact ⟨a, by simp, by omega⟩
          · exact hcov x (by omega) hx'

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem RInv_fold (G : ByteArray) : ∀ m ≤ G.size, RInv G m ((List.range' 0 m).foldl (runStep G) #[]) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], none, rfl, ?_, by simp, by simp, by simp, fun x hx => by omega⟩
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro h; have := h.1; omega
  | succ m ih =>
    intro hm
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    exact RInv_step G m (by omega) _ (ih (by omega))

theorem flat_length (prs : List (Nat × Nat)) : (flat prs).length = 2 * prs.length := by
  induction prs with
  | nil => rfl
  | cons pr t ih => simp [flat, ih]; omega

theorem flat_get (prs : List (Nat × Nat)) : ∀ i (h : i < prs.length),
    (flat prs)[2 * i]? = some prs[i].1 ∧ (flat prs)[2 * i + 1]? = some prs[i].2 := by
  induction prs with
  | nil => intro i h; simp at h
  | cons pr t ih =>
    intro i h
    cases i with
    | zero => simp [flat]
    | succ i =>
      have := ih i (by simp at h; omega)
      simp only [flat, show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by omega,
        List.getElem?_cons_succ, List.getElem_cons_succ]
      exact this

theorem arr_get! (R : Array Nat) (j v : Nat) (h : R.toList[j]? = some v) : R[j]! = v := by
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.mp h
  have hj' : j < R.size := by simpa using hj
  rw [getElem!_pos R j hj', ← e]; simp

theorem allNot_of (B : ByteArray) (b : Nat) : ∀ d a, b - a = d → (∀ x, a ≤ x → x < b → acgt (B.get! x) = false) →
    allNot B a b = true := by
  intro d
  induction d with
  | zero => intro a hd _; rw [allNot, if_neg (by omega)]
  | succ d ih =>
    intro a hd h
    rw [allNot, if_pos (by omega), h a (Nat.le_refl _) (by omega)]
    exact ih (a + 1) (by omega) (fun x h1 h2 => h x (by omega) h2)

theorem advance_spec (ix : MzIdx) (x : Nat) : ∀ fuel c, c ≤ ix.nr → ix.nr ≤ c + fuel →
    c ≤ advance ix x fuel c ∧ advance ix x fuel c ≤ ix.nr ∧
      (∀ i, c ≤ i → i < advance ix x fuel c → ix.rb i ≤ x) ∧
      (advance ix x fuel c < ix.nr → x < ix.rb (advance ix x fuel c)) := by
  intro fuel
  induction fuel with
  | zero => intro c h1 h2; simp only [advance]; exact ⟨Nat.le_refl _, h1, fun i h1 h2 => by omega, fun h => by omega⟩
  | succ fuel ih =>
    intro c h1 h2
    simp only [advance]
    by_cases hc : (c < ix.nr && ix.rb c ≤ x) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨i1, i2, i3, i4⟩ := ih (c + 1) (by omega) (by omega)
      refine ⟨by omega, i2, fun i hi1 hi2 => ?_, i4⟩
      by_cases e : i = c
      · rw [e]; exact hc.2
      · exact i3 i (by omega) hi2
    · rw [if_neg hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le] at hc
      exact ⟨Nat.le_refl _, h1, fun i h1 h2 => by omega, fun h => hc h⟩

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem ra_rb (ix : MzIdx) (prs : List (Nat × Nat)) (hR : ix.runs.toList = flat prs) (i : Nat) (hi : i < prs.length) :
    ix.ra i = prs[i].1 ∧ ix.rb i = prs[i].2 := by
  obtain ⟨h1, h2⟩ := flat_get prs i hi
  rw [← hR] at h1 h2
  exact ⟨arr_get! _ _ _ h1, arr_get! _ _ _ h2⟩

theorem nr_eq (ix : MzIdx) (prs : List (Nat × Nat)) (hR : ix.runs.toList = flat prs) : ix.nr = prs.length := by
  have : ix.runs.size = 2 * prs.length := by rw [← Array.length_toList, hR, flat_length]
  show ix.runs.size / 2 = _
  omega

theorem checkRuns_of (ix : MzIdx) (G : ByteArray) :
    ∀ n i, (∀ j, i ≤ j → j < i + n → runOk ix G j = true) → checkRuns ix G n i = true := by
  intro n
  induction n with
  | zero => intro i _; rfl
  | succ n ih =>
    intro i h
    simp only [checkRuns, Bool.and_eq_true]
    exact ⟨h i (Nat.le_refl _) (by omega), ih (i + 1) (fun j h1 h2 => h j (by omega) (by omega))⟩

/-- `checkRuns` and `checkCover` accept the maximal non-ACGT runs, in order. -/
theorem runs_ok (ix : MzIdx) (G : ByteArray) (prs : List (Nat × Nat)) (hR : ix.runs.toList = flat prs)
    (hgood : ∀ pr ∈ prs, GoodPair G pr) (hsort : prs.Pairwise (fun p1 p2 => p1.2 < p2.1))
    (hcov : ∀ x < G.size, acgt (G.get! x) = false → ∃ pr ∈ prs, pr.1 ≤ x ∧ x < pr.2) :
    checkRuns ix G ix.nr 0 = true ∧ checkCover ix G 0 G.size 0 = true := by
  have hnr := nr_eq ix prs hR
  have hrr := ra_rb ix prs hR
  have hlt : ∀ i j, i < j → j < prs.length → ix.rb i < ix.ra j := fun i j hij hj => by
    rw [(hrr i (by omega)).2, (hrr j hj).1]
    exact List.pairwise_iff_getElem.mp hsort i j (by omega) hj hij
  have hab : ∀ i < prs.length, ix.ra i < ix.rb i := fun i hi => by
    rw [(hrr i hi).1, (hrr i hi).2]; exact (hgood _ (List.getElem_mem hi)).1
  refine ⟨checkRuns_of ix G _ _ (fun j _ hj => ?_), ?_⟩
  · rw [Nat.zero_add, hnr] at hj
    obtain ⟨g1, g2, g3, g4, g5⟩ := hgood _ (List.getElem_mem hj)
    unfold runOk
    simp only [(hrr j hj).1, (hrr j hj).2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hnr]
    refine ⟨⟨⟨⟨⟨g1, g2⟩, allNot_of G _ _ _ rfl g3⟩, g5⟩, g4⟩, ?_⟩
    by_cases hj1 : j + 1 < prs.length
    · right; rw [← (hrr j hj).2]; exact hlt j (j + 1) (by omega) hj1
    · left; omega
  · have key : ∀ n x c, x + n = G.size → c ≤ ix.nr → (∀ i < c, ix.rb i ≤ x) → checkCover ix G c n x = true := by
      intro n
      induction n with
      | zero => intro x c _ _ _; rfl
      | succ n ih =>
        intro x c hx hc hinv
        simp only [checkCover]
        by_cases ha : acgt (G.get! x) = true
        · rw [if_pos ha]; exact ih (x + 1) c (by omega) hc (fun i hi => by have := hinv i hi; omega)
        · rw [if_neg ha]
          have hodd : acgt (G.get! x) = false := by simpa using ha
          obtain ⟨d1, d2, d3, d4⟩ := advance_spec ix x ix.nr c hc (by omega)
          generalize advance ix x ix.nr c = c' at d1 d2 d3 d4
          obtain ⟨pr, hp, hp1, hp2⟩ := hcov x (by omega) hodd
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
          have ej := hrr j hj
          have hjc : c' ≤ j := by
            apply Classical.byContradiction; intro hlt'
            by_cases hjc : j < c
            · have := hinv j hjc; omega
            · have := d3 j (by omega) (by omega); omega
          have hjeq : j = c' := by
            apply Classical.byContradiction; intro hne
            have h1 := d4 (by omega)
            have h2 := hlt c' j (by omega) hj
            omega
          subst hjeq
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ih (x + 1) _ (by omega) d2 (fun i hi => ?_)⟩
          by_cases hic : i < c
          · have := hinv i hic; omega
          · have := d3 i (by omega) hi; omega
    exact key G.size 0 0 (by omega) (Nat.zero_le _) (fun i hi => by omega)

end MapSpec.Mz.BO

namespace MapSpec.Mz.BO

theorem evs_congr (ix ix' : MzIdx) (G : ByteArray) (h : ∀ v, ix.mini v = ix'.mini v) :
    ∀ n last p, evs ix G last n p = evs ix' G last n p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih => intro last p; simp only [evs, pmOf, h, ih]; rfl

theorem runsOf_spec (G : ByteArray) : ∃ prs : List (Nat × Nat), (runsOf G).toList = flat prs ∧
    (∀ pr ∈ prs, GoodPair G pr) ∧ prs.Pairwise (fun p1 p2 => p1.2 < p2.1) ∧
    (∀ x < G.size, acgt (G.get! x) = false → ∃ pr ∈ prs, pr.1 ≤ x ∧ x < pr.2) := by
  obtain ⟨prs, oa, hR, hopen, hprs, hsort, _, hcov⟩ := RInv_fold G G.size (Nat.le_refl _)
  have hnone : oa = none := by
    cases oa with
    | none => rfl
    | some a => have := (hopen.1 rfl).2.1; omega
  subst hnone
  refine ⟨prs, by unfold runsOf; simpa using hR, fun pr hp => (hprs pr hp).1, hsort, fun x hx hodd => ?_⟩
  rcases hcov x hx hodd with h | ⟨a, ha, _⟩
  · exact h
  · simp at ha

theorem ixB_hint (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : (ixB G).hint = cntOf G := by
  obtain ⟨c1, _⟩ := cntOf_spec G hsz
  rw [MzIdx.hint, ixB_offs, ixB_ob, ixB_B, Nat.mul_zero, Nat.zero_add, ← c1, ByteArray.extract_zero_size]

/-- **The index the builder makes from the bytes `G` passes the checker.** -/
theorem check_ixB (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : check (ixB G) G = true := by
  obtain ⟨c1, c2⟩ := cntOf_spec G hsz
  obtain ⟨prs, hR, hgood, hsort, hcov⟩ := runsOf_spec G
  obtain ⟨r1, r2⟩ := runs_ok (ixB G) G prs (by rw [ixB_runs]; exact hR) hgood hsort hcov
  unfold check
  rw [ixB_checkParams, checkSound_ixB G hsz, r1, r2, checkComp_eq, ixB_hint G hsz,
    evs_congr (ixB G) (ix0 G) G (ixB_mini G)]
  simp only [Bool.true_and, Bool.and_true]
  exact replay_ok G hsz (EG G) [] (cntOf G) rfl c1 (fun b hb => by rw [c2 _ (by omega)]; rfl)

theorem buildW_ixB (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : buildW G 22 26 0 5 6 = ixB G := by
  rw [buildW_eq G (pb_le G hsz)]
  unfold ixB slOf runsOf
  rfl

end MapSpec.Mz.BO

namespace MapSpec.Mz

/-- **The builder's index passes the checker**: `Mz.buildW G 22 26 0 5 6` (`k = 22`, `2^26` buckets,
no context letters, 5-byte slots, `t = 6`) is accepted by `Mz.check` whenever the genome has at most
`2^32 + 23` letters (at most `2^32 - 1` entries: bucket offsets are `UInt32`s). -/
theorem check_buildW (G : ByteArray) (hsz : G.size ≤ 2 ^ 32 + 23) : check (buildW G 22 26 0 5 6) G = true := by
  rw [BO.buildW_ixB G hsz]; exact BO.check_ixB G hsz

end MapSpec.Mz

#print axioms MapSpec.Mz.check_buildW
