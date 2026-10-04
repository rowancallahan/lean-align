import AlignmentWfaU32Fill

/-!
# `uext2 = uext`

The free extension with two inline comparisons and the `USize` loop `lcpU`
(AlignmentWfaU32Fill.lean) computes the same `UInt32` as the proven `uext`
(AlignmentWfaU32Level.lean) under the no-wrap bounds `UBound`.

Route: both sides are compared through `.toNat`.  The right side is
`extR` (`uext_toNat`), i.e. `off + lcp (xa.drop off) (ya.drop j) + 1`
(`lcpArr_eq`).  The left side is case-split as `uext2` is; `lcp` is unfolded
once per inline comparison (`List.drop_eq_getElem_cons`) and `lcpU_toNat`
covers the loop.
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- Small helpers
-- ══════════════════════════════════════════════════════════════════

theorem lcp_nil_left (ys : List Char) : lcp [] ys = 0 := by
  cases ys <;> rfl

theorem lcp_le_length (xs ys : List Char) : lcp xs ys ≤ xs.length := by
  induction xs generalizing ys with
  | nil => rw [lcp_nil_left]; exact Nat.zero_le _
  | cons x xr ih =>
    cases ys with
    | nil => rw [lcp_nil_right]; exact Nat.zero_le _
    | cons y yr =>
      simp only [lcp, List.length_cons]
      split
      · exact Nat.succ_le_succ (ih yr)
      · exact Nat.zero_le _

/-- `lcp` is zero as soon as one of the two suffixes is empty. -/
theorem lcp_drop_eq_zero (xa ya : Array Char) (i j : Nat) (h : ¬ (i < xa.size ∧ j < ya.size)) :
    lcp (xa.toList.drop i) (ya.toList.drop j) = 0 := by
  rcases Nat.lt_or_ge i xa.size with hi | hi
  · have hj : ya.size ≤ j := Nat.le_of_not_lt (fun hc => h ⟨hi, hc⟩)
    rw [List.drop_of_length_le (l := ya.toList) (by rw [Array.length_toList]; exact hj),
      lcp_nil_right]
  · rw [List.drop_of_length_le (l := xa.toList) (by rw [Array.length_toList]; exact hi),
      lcp_nil_left]

theorem drop_cons_of_lt (xa : Array Char) (i : Nat) (hi : i < xa.size) :
    xa.toList.drop i = xa[i] :: xa.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp

theorem Bool.toNat_toUInt32 (b : Bool) : b.toUInt32.toNat = b.toNat := by
  cases b <;> rfl

theorem Bool.toUInt32_and (b c : Bool) : b.toUInt32 &&& c.toUInt32 = (b && c).toUInt32 := by
  cases b <;> cases c <;> decide

theorem Bool.toUInt32_true : (true : Bool).toUInt32 = 1 := rfl

theorem Bool.toUInt32_false : (false : Bool).toUInt32 = 0 := rfl

/-- The loop result, converted back to `UInt32` and incremented, as a `Nat`. -/
theorem lcpU_toUInt32_succ (xa ya : Array Char) (i j fuel : USize)
    (hi : i.toNat + fuel.toNat ≤ xa.size) (hj : j.toNat + fuel.toNat ≤ ya.size)
    (hsx : xa.size < USize.size) (hsy : ya.size < USize.size)
    (hfull : fuel.toNat = min (xa.size - i.toNat) (ya.size - j.toNat))
    (hx30 : xa.size < 2 ^ 30) :
    ((lcpU xa ya i j fuel hi hj hsx hsy).toUInt32 + 1).toNat =
      i.toNat + lcp (xa.toList.drop i.toNat) (ya.toList.drop j.toNat) + 1 := by
  have hl := lcpU_toNat xa ya i j fuel hi hj hsx hsy hfull
  have hle := lcp_le_length (xa.toList.drop i.toNat) (ya.toList.drop j.toNat)
  rw [List.length_drop, Array.length_toList] at hle
  have hv : (lcpU xa ya i j fuel hi hj hsx hsy).toUInt32.toNat =
      i.toNat + lcp (xa.toList.drop i.toNat) (ya.toList.drop j.toNat) := by
    rw [USize.toNat_toUInt32, hl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_succ _ (by rw [hv]; omega), hv]

-- ══════════════════════════════════════════════════════════════════
-- The theorem
-- ══════════════════════════════════════════════════════════════════

theorem uext2_eq (m n t a : UInt32) (xa ya : Array Char) (hm : m.toNat = xa.size)
    (hn : n.toNat = ya.size) (hb : UBound m n t a) :
    uext2 m n xa ya hm hn t a = uext m xa ya t a := by
  obtain ⟨hm30, hn30, ht30, ha30⟩ := hb
  apply UInt32.toNat_inj.mp
  rw [uext_toNat m n t a xa ya ⟨hm30, hn30, ht30, ha30⟩ (by omega)]
  unfold uext2 extR
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos ((UInt32.toNat_eq_zero_iff a).mp h0)]; rfl
  · rw [if_neg h0, if_neg (fun h => h0 ((UInt32.toNat_eq_zero_iff a).mpr h))]
    have ha0 : a.toNat ≠ 0 := fun he => h0 ((UInt32.toNat_eq_zero_iff a).mpr he)
    have hoff := UInt32.toNat_pred a h0
    have hj := ujoff_toNat m t (a - 1) (by omega)
    rw [hoff] at hj
    have hjle : joffOf m.toNat t.toNat (a.toNat - 1) ≤ a.toNat - 1 + t.toNat := by
      unfold joffOf; omega
    dsimp only
    rw [lcpArr_eq]
    by_cases h : a - 1 < m ∧ ujoff m t (a - 1) < n
    · rw [dif_pos h]
      have hoffm : a.toNat - 1 < xa.size := by
        have := UInt32.lt_iff_toNat_lt.mp h.1; omega
      have hjn : joffOf m.toNat t.toNat (a.toNat - 1) < ya.size := by
        have := UInt32.lt_iff_toNat_lt.mp h.2; omega
      have hoff1 : (a - 1 + 1).toNat = a.toNat := by
        rw [UInt32.toNat_succ _ (by omega), hoff]; omega
      have hj1 : (ujoff m t (a - 1) + 1).toNat = joffOf m.toNat t.toNat (a.toNat - 1) + 1 := by
        rw [UInt32.toNat_succ _ (by omega), hj]
      have hxl := drop_cons_of_lt xa _ hoffm
      have hyl := drop_cons_of_lt ya _ hjn
      have hoffN1 : a.toNat - 1 + 1 = a.toNat := by omega
      rw [hoffN1] at hxl
      simp only [Array.uget, UInt32.toNat_toUSize, hoff, hj, hoff1, hj1]
      by_cases h1 : a - 1 + 1 < m ∧ ujoff m t (a - 1) + 1 < n
      · rw [dif_pos h1]
        have hoffm1 : a.toNat < xa.size := by
          have := UInt32.lt_iff_toNat_lt.mp h1.1; omega
        have hjn1 : joffOf m.toNat t.toNat (a.toNat - 1) + 1 < ya.size := by
          have := UInt32.lt_iff_toNat_lt.mp h1.2; omega
        have hxl2 := drop_cons_of_lt xa _ hoffm1
        have hyl2 := drop_cons_of_lt ya _ hjn1
        have hoff2 : (a - 1 + 1 + 1).toNat = a.toNat + 1 := by
          rw [UInt32.toNat_succ _ (by omega), hoff1]
        have hj2 : (ujoff m t (a - 1) + 1 + 1).toNat = joffOf m.toNat t.toNat (a.toNat - 1) + 1 + 1 := by
          rw [UInt32.toNat_succ _ (by omega), hj1]
        rw [hxl, hyl, lcp, hxl2, hyl2, lcp, Bool.toUInt32_and]
        by_cases hc0 : xa[a.toNat - 1] = ya[joffOf m.toNat t.toNat (a.toNat - 1)]
        · by_cases hc1 : xa[a.toNat] = ya[joffOf m.toNat t.toNat (a.toNat - 1) + 1]
          · rw [if_pos hc0, if_pos hc1, beq_iff_eq.mpr hc0, beq_iff_eq.mpr hc1, Bool.true_and,
              Bool.toUInt32_true, if_pos rfl]
            have hle1 : a - 1 + 1 + 1 ≤ m := by
              rw [UInt32.le_iff_toNat_le, hoff2]; have := UInt32.lt_iff_toNat_lt.mp h1.1; omega
            have hle2 : ujoff m t (a - 1) + 1 + 1 ≤ n := by
              rw [UInt32.le_iff_toNat_le, hj2]; have := UInt32.lt_iff_toNat_lt.mp h1.2; omega
            have e1 := UInt32.toNat_sub_of_le m _ hle1
            have e2 := UInt32.toNat_sub_of_le n _ hle2
            rw [hoff2] at e1
            rw [hj2] at e2
            rw [lcpU_toUInt32_succ]
            · simp only [UInt32.toNat_toUSize, hoff2, hj2]; omega
            · simp only [UInt32.toNat_toUSize, hoff2, hj2]
              split
              · rename_i hc; rw [UInt32.le_iff_toNat_le] at hc; rw [e1]; omega
              · rename_i hc; rw [UInt32.le_iff_toNat_le] at hc; rw [e2]; omega
            · omega
          · rw [if_pos hc0, if_neg hc1, beq_iff_eq.mpr hc0, beq_eq_false_iff_ne.mpr hc1, Bool.and_false,
              Bool.toUInt32_true, Bool.toUInt32_false, if_neg (by decide), UInt32.add_zero,
              UInt32.toNat_succ _ (by omega)]
            omega
        · rw [if_neg hc0, beq_eq_false_iff_ne.mpr hc0, Bool.false_and, Bool.toUInt32_false,
            if_neg (by decide), UInt32.add_zero, UInt32.add_zero]
          omega
      · rw [dif_neg h1]
        have hz : lcp (xa.toList.drop a.toNat)
            (ya.toList.drop (joffOf m.toNat t.toNat (a.toNat - 1) + 1)) = 0 := by
          apply lcp_drop_eq_zero
          intro hc
          apply h1
          constructor
          · rw [UInt32.lt_iff_toNat_lt, hoff1, hm]; exact hc.1
          · rw [UInt32.lt_iff_toNat_lt, hj1, hn]; exact hc.2
        rw [hxl, hyl, lcp, hz]
        by_cases hc : xa[a.toNat - 1] = ya[joffOf m.toNat t.toNat (a.toNat - 1)]
        · rw [if_pos hc, beq_iff_eq.mpr hc, UInt32.toNat_add_of_lt _ _ (by rw [Bool.toNat_toUInt32]; simp; omega),
            Bool.toNat_toUInt32]
          simp; omega
        · rw [if_neg hc, beq_eq_false_iff_ne.mpr hc, UInt32.toNat_add_of_lt _ _ (by rw [Bool.toNat_toUInt32]; simp; omega),
            Bool.toNat_toUInt32]
          simp; omega
    · rw [dif_neg h]
      have hz : lcp (xa.toList.drop (a.toNat - 1))
          (ya.toList.drop (joffOf m.toNat t.toNat (a.toNat - 1))) = 0 := by
        apply lcp_drop_eq_zero
        intro hc
        apply h
        constructor
        · rw [UInt32.lt_iff_toNat_lt, hoff, hm]; exact hc.1
        · rw [UInt32.lt_iff_toNat_lt, hj, hn]; exact hc.2
      rw [hz]; omega

#print axioms AlignmentSpec.U32Proof.uext2_eq

end AlignmentSpec.U32Proof
