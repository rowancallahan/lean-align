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
