import AlignmentWfaU32FillS

/-!
Functional specification of the single-source cell loop `uFillS`: after the
loop, index `mg + j'` of the output array (for `i ≤ j' < w`) holds
`cellS … j' (t32 + (j' - i))`; every other index is unchanged.

The loop carries `prev` / `cur` as the source values at (Nat) indices
`i + sh1 - 2` and `i + sh1 - 1`; these are the two hypotheses of the
statement and they are re-established for `i + 1` (one-cell tail) and
`i + 2` (two-cell body) in the inductive step.
-/

namespace AlignmentSpec.U32Proof

/-- A bounded `uget` at a `UInt32` index is the `getD` read (default `0`). -/
theorem uget_eq_getD_S (a : Array UInt32) (n : UInt32) (h : n.toUSize.toNat < a.size) :
    a.uget n.toUSize h = a.getD n.toNat 0 := by
  simp only [Array.uget, UInt32.toNat_toUSize] at h ⊢
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- Diagonal bookkeeping of the loop: `(t32 + 1) + (k - (i + 1)) = t32 + (k - i)`. -/
theorem add_one_add_sub_succ_S (t k i : UInt32) : (t + 1) + (k - (i + 1)) = t + (k - i) := by
  grind

/-- `(i + 1) - i = 1` in `UInt32`. -/
theorem add_one_sub_self_S (i : UInt32) : i + 1 - i = 1 := by
  grind

/-- One-cell tail of the loop (`i < w`, `¬ i + 1 < w`): with `prev` / `cur` the source
values at `i + sh1 - 2` and `i + sh1 - 1`, the written value is `cellS … i t32` and the
next `prev` / `cur` are `cur` and the source at `i + sh1`. -/
theorem uFillS_step (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32) (hw : w.toNat + 1 < 2 ^ 32) (srcA : Array UInt32)
    (sh1 mg : UInt32) (size : Nat)
    (hsrc : w.toNat + sh1.toNat ≤ srcA.size) (hsrc' : srcA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32)
    (i : UInt32) (hi0 : i ≤ w) (t32 prev cur : UInt32) (mf : Array UInt32) (hmf : mf.size = size)
    (hi : i < w) (h2 : ¬ i + 1 < w)
    (hprev : prev = srcA.getD (i.toNat + sh1.toNat - 2) 0)
    (hcur : cur = srcA.getD (i.toNat + sh1.toNat - 1) 0) :
    uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz i hi0 t32 prev cur mf hmf =
      uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
        (i + 1) (succ_le_of_lt2 hi) (t32 + 1) cur (srcA.getD (i.toNat + sh1.toNat) 0)
        (mf.uset (i + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 i t32)
          (by rw [hmf]; exact idx2 hi hout hsz))
        (by rw [Array.size_uset]; exact hmf) := by
  have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have hnext : (i + sh1).toNat = i.toNat + sh1.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  subst hprev; subst hcur
  rw [uFillS, dif_neg h2, dif_pos hi]
  simp only [uget_eq_getD_S, hnext, cellS]

/-- Two-cell body of the loop (`i + 1 < w`): the written values are `cellS … i t32` (at
`i + mg`) and `cellS … (i + 1) (t32 + 1)` (at `i + 1 + mg`), and the next `prev` / `cur`
are the source at `i + sh1` and `i + 1 + sh1`. -/
theorem uFillS_step2 (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32) (hw : w.toNat + 1 < 2 ^ 32) (srcA : Array UInt32)
    (sh1 mg : UInt32) (size : Nat)
    (hsrc : w.toNat + sh1.toNat ≤ srcA.size) (hsrc' : srcA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32)
    (i : UInt32) (hi0 : i ≤ w) (t32 prev cur : UInt32) (mf : Array UInt32) (hmf : mf.size = size)
    (h2 : i + 1 < w)
    (hprev : prev = srcA.getD (i.toNat + sh1.toNat - 2) 0)
    (hcur : cur = srcA.getD (i.toNat + sh1.toNat - 1) 0) :
    uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz i hi0 t32 prev cur mf hmf =
      uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
        (i + 1 + 1) (succ_le_of_lt2 h2) (t32 + 1 + 1)
        (srcA.getD (i.toNat + sh1.toNat) 0) (srcA.getD (i.toNat + 1 + sh1.toNat) 0)
        ((mf.uset (i + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 i t32)
            (by rw [hmf]; exact idx2 (lt_of_succ_lt2 hi0 hw h2) hout hsz)).uset
          (i + 1 + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 (i + 1) (t32 + 1))
          (by rw [Array.size_uset, hmf]; exact idx2 h2 hout hsz))
        (by rw [Array.size_uset, Array.size_uset]; exact hmf) := by
  have hi : i < w := lt_of_succ_lt2 hi0 hw h2
  have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hnext : (i + sh1).toNat = i.toNat + sh1.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hnext2 : (i + 1 + sh1).toNat = i.toNat + 1 + sh1.toNat := by
    rw [UInt32.toNat_add, hi1]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : i.toNat + 1 + sh1.toNat - 2 = i.toNat + sh1.toNat - 1 := by omega
  have e3 : i.toNat + 1 + sh1.toNat - 1 = i.toNat + sh1.toNat := by omega
  subst hprev; subst hcur
  rw [uFillS, dif_pos h2]
  simp only [uget_eq_getD_S, hnext, hnext2, cellS, hi1, e2, e3]

theorem uFillS_spec (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32) (hw : w.toNat + 1 < 2 ^ 32) (srcA : Array UInt32)
    (sh1 mg : UInt32) (size : Nat)
    (hsrc : w.toNat + sh1.toNat ≤ srcA.size) (hsrc' : srcA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32) :
    ∀ (i : UInt32) (hi : i ≤ w) (t32 prev cur : UInt32) (mf : Array UInt32) (hmf : mf.size = size),
      prev = srcA.getD (i.toNat + sh1.toNat - 2) 0 →
      cur = srcA.getD (i.toNat + sh1.toNat - 1) 0 →
      let r := uFillS xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz i hi t32 prev cur mf hmf
      r.size = size ∧
      (∀ j, r[j]? = if mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat then
          some (cellS xa ya m32 n32 len32 hm hn srcA sh1 (j - mg.toNat).toUInt32
            (t32 + ((j - mg.toNat).toUInt32 - i))) else mf[j]?) := by
  intro i hi0
  generalize hk : w.toNat - i.toNat = k
  induction k using Nat.strongRecOn generalizing i hi0 with
  | _ k ih =>
  intro t32 prev cur mf hmf hprev hcur
  dsimp only
  by_cases h2 : i + 1 < w
  · -- two cells: unfold the two-cell body and use the induction hypothesis on the tail
    have hi : i < w := lt_of_succ_lt2 hi0 hw h2
    have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have h2' : i.toNat + 1 < w.toNat := hi1 ▸ UInt32.lt_iff_toNat_lt.mp h2
    have hi2 : (i + 1 + 1).toNat = i.toNat + 2 := by
      rw [UInt32.toNat_add, UInt32.toNat_one, hi1]; exact Nat.mod_eq_of_lt (by omega)
    have him : (i + mg).toUSize.toNat = i.toNat + mg.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have him1 : (i + 1 + mg).toUSize.toNat = i.toNat + 1 + mg.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add, hi1]; exact Nat.mod_eq_of_lt (by omega)
    have hlt : w.toNat - (i + 1 + 1).toNat < k :=
      hk ▸ Nat.lt_trans (succ_lt_toNat2 h2) (succ_lt_toNat2 hi)
    rw [uFillS_step2 xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
      i hi0 t32 prev cur mf hmf h2 hprev hcur]
    have key := ih _ hlt (i + 1 + 1) (succ_le_of_lt2 h2) rfl (t32 + 1 + 1)
      (srcA.getD (i.toNat + sh1.toNat) 0) (srcA.getD (i.toNat + 1 + sh1.toNat) 0)
      ((mf.uset (i + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 i t32)
          (by rw [hmf]; exact idx2 hi hout hsz)).uset
        (i + 1 + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 (i + 1) (t32 + 1))
        (by rw [Array.size_uset, hmf]; exact idx2 h2 hout hsz))
      (by rw [Array.size_uset, Array.size_uset]; exact hmf)
      (by rw [hi2, show i.toNat + 2 + sh1.toNat - 2 = i.toNat + sh1.toNat by omega])
      (by rw [hi2, show i.toNat + 2 + sh1.toNat - 1 = i.toNat + 1 + sh1.toNat by omega])
    dsimp only at key
    obtain ⟨h1, hM⟩ := key
    have e1 : (i.toNat + mg.toNat - mg.toNat).toUInt32 = i := by simp
    have e1' : (i.toNat + 1 + mg.toNat - mg.toNat).toUInt32 = i + 1 := by
      have hlt : i.toNat + 1 < UInt32.size := Nat.lt_trans h2' (UInt32.toNat_lt_size w)
      rw [Nat.add_sub_cancel]
      apply UInt32.toNat_inj.mp
      rw [hi1, UInt32.toNat_ofNat_of_lt' hlt]
    refine ⟨h1, ?_⟩
    intro j
    rw [hM j]
    simp only [Array.uset, Array.getElem?_set, him, him1]
    by_cases hj1 : j = i.toNat + 1 + mg.toNat
    · subst hj1
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega), e1', add_one_sub_self_S]
    · by_cases hj : j = i.toNat + mg.toNat
      · subst hj
        rw [if_neg (by omega), if_neg (Ne.symm hj1), if_pos rfl, if_pos (by omega), e1,
          UInt32.sub_self, UInt32.add_zero]
      · by_cases hj2 : mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat
        · rw [if_pos (by omega), if_pos hj2, add_one_add_sub_succ_S, add_one_add_sub_succ_S]
        · rw [if_neg (by omega), if_neg (Ne.symm hj1), if_neg (Ne.symm hj), if_neg hj2]
  · by_cases hi : i < w
    · -- one more cell: unfold one step and use the induction hypothesis on the tail
      have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
      have him : (i + mg).toUSize.toNat = i.toNat + mg.toNat := by
        rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hlt : w.toNat - (i + 1).toNat < k := hk ▸ succ_lt_toNat2 hi
      rw [uFillS_step xa ya m32 n32 len32 hm hn w hw srcA sh1 mg size hsrc hsrc' hout hsz
        i hi0 t32 prev cur mf hmf hi h2 hprev hcur]
      have key := ih _ hlt (i + 1) (succ_le_of_lt2 hi) rfl (t32 + 1) cur
        (srcA.getD (i.toNat + sh1.toNat) 0)
        (mf.uset (i + mg).toUSize (cellS xa ya m32 n32 len32 hm hn srcA sh1 i t32)
          (by rw [hmf]; exact idx2 hi hout hsz))
        (by rw [Array.size_uset]; exact hmf)
        (by rw [hcur, hi1, show i.toNat + 1 + sh1.toNat - 2 = i.toNat + sh1.toNat - 1 by omega])
        (by rw [hi1, show i.toNat + 1 + sh1.toNat - 1 = i.toNat + sh1.toNat by omega])
      dsimp only at key
      obtain ⟨h1, hM⟩ := key
      have e1 : (i.toNat + mg.toNat - mg.toNat).toUInt32 = i := by simp
      refine ⟨h1, ?_⟩
      intro j
      rw [hM j, Array.uset, Array.getElem?_set, him]
      by_cases hj : j = i.toNat + mg.toNat
      · subst hj
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), e1, UInt32.sub_self, UInt32.add_zero]
      · by_cases hj2 : mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat
        · rw [if_pos (by omega), if_pos hj2, add_one_add_sub_succ_S]
        · rw [if_neg (by omega), if_neg (Ne.symm hj), if_neg hj2]
    · -- loop exit: nothing written
      have hi' : w.toNat ≤ i.toNat := Nat.le_of_not_lt (fun h => hi (UInt32.lt_iff_toNat_lt.mpr h))
      rw [uFillS, dif_neg h2, dif_neg hi]
      refine ⟨hmf, ?_⟩
      intro j
      rw [if_neg (by omega)]

end AlignmentSpec.U32Proof

#print axioms AlignmentSpec.U32Proof.uFillS_spec
#print axioms AlignmentSpec.U32Proof.uFillS_step
#print axioms AlignmentSpec.U32Proof.uFillS_step2
#print axioms AlignmentSpec.U32Proof.uget_eq_getD_S
#print axioms AlignmentSpec.U32Proof.add_one_add_sub_succ_S
#print axioms AlignmentSpec.U32Proof.add_one_sub_self_S
