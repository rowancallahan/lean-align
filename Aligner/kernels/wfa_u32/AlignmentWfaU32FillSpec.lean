import AlignmentWfaU32Fill

/-!
Functional specification of the cell loop `uFillGo2`: after the loop, index
`mg + j'` of each output array (for `i ≤ j' < w`) holds the value of the
corresponding cell function (`cellX2`, `cellY2`, `cellM2`) at cell `j'` and
diagonal `t32 + (j' - i)`; every other index is unchanged.
-/

namespace AlignmentSpec.U32Proof

/-- A bounded `uget` at a `UInt32` index is the `getD` read (default `0`). -/
theorem uget_eq_getD (a : Array UInt32) (n : UInt32) (h : n.toUSize.toNat < a.size) :
    a.uget n.toUSize h = a.getD n.toNat 0 := by
  simp only [Array.uget, UInt32.toNat_toUSize] at h ⊢
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- Diagonal bookkeeping of the loop: `(t32 + 1) + (k - (i + 1)) = t32 + (k - i)`. -/
theorem add_one_add_sub_succ (t k i : UInt32) : (t + 1) + (k - (i + 1)) = t + (k - i) := by
  grind

/-- One step of the loop, with the written values expressed through the cell functions. -/
theorem uFillGo2_step (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm mg : UInt32) (size : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32)
    (i t32 : UInt32) (mf xf yf : Array UInt32)
    (hmf : mf.size = size) (hxf : xf.size = size) (hyf : yf.size = size) (hi : i < w) :
    uFillGo2 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm mg size
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hout hsz i t32 mf xf yf hmf hxf hyf =
      uFillGo2 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm mg size
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hout hsz (i + 1) (t32 + 1)
        (mf.uset (i + mg).toUSize
          (cellM2 m32 n32 xa ya hm hn dmA shDm i t32
            (cellX2 m32 n32 xeA xoA shXe shXo i t32) (cellY2 m32 len32 yeA yoA shYe shYo i t32))
          (by rw [hmf]; exact idx2 hi hout hsz))
        (xf.uset (i + mg).toUSize (cellX2 m32 n32 xeA xoA shXe shXo i t32)
          (by rw [hxf]; exact idx2 hi hout hsz))
        (yf.uset (i + mg).toUSize (cellY2 m32 len32 yeA yoA shYe shYo i t32)
          (by rw [hyf]; exact idx2 hi hout hsz))
        (by rw [Array.size_uset]; exact hmf) (by rw [Array.size_uset]; exact hxf)
        (by rw [Array.size_uset]; exact hyf) := by
  rw [uFillGo2, dif_pos hi]
  simp only [uget_eq_getD, cellX2, cellY2, cellM2]

theorem uFillGo2_spec (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm mg : UInt32) (size : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hout : w.toNat + mg.toNat ≤ size) (hsz : size < 2 ^ 32) :
    ∀ (i t32 : UInt32) (mf xf yf : Array UInt32)
      (hmf : mf.size = size) (hxf : xf.size = size) (hyf : yf.size = size),
      let r := uFillGo2 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm mg size
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hout hsz i t32 mf xf yf hmf hxf hyf
      r.1.size = size ∧ r.2.1.size = size ∧ r.2.2.size = size ∧
      (∀ j, r.2.1[j]? = if mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat then
          some (cellX2 m32 n32 xeA xoA shXe shXo (j - mg.toNat).toUInt32
            (t32 + ((j - mg.toNat).toUInt32 - i))) else xf[j]?) ∧
      (∀ j, r.2.2[j]? = if mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat then
          some (cellY2 m32 len32 yeA yoA shYe shYo (j - mg.toNat).toUInt32
            (t32 + ((j - mg.toNat).toUInt32 - i))) else yf[j]?) ∧
      (∀ j, r.1[j]? = if mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat then
          some (cellM2 m32 n32 xa ya hm hn dmA shDm (j - mg.toNat).toUInt32
            (t32 + ((j - mg.toNat).toUInt32 - i))
            (cellX2 m32 n32 xeA xoA shXe shXo (j - mg.toNat).toUInt32 (t32 + ((j - mg.toNat).toUInt32 - i)))
            (cellY2 m32 len32 yeA yoA shYe shYo (j - mg.toNat).toUInt32 (t32 + ((j - mg.toNat).toUInt32 - i))))
          else mf[j]?) := by
  intro i
  generalize hk : w.toNat - i.toNat = k
  induction k using Nat.strongRecOn generalizing i with
  | _ k ih =>
  intro t32 mf xf yf hmf hxf hyf
  dsimp only
  by_cases hi : i < w
  · -- one more cell: unfold one step and use the induction hypothesis on the tail
    have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
    have hw : w.toNat < 2 ^ 32 := UInt32.toNat_lt_size w
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have him : (i + mg).toUSize.toNat = i.toNat + mg.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hlt : w.toNat - (i + 1).toNat < k := hk ▸ succ_lt_toNat2 hi
    rw [uFillGo2_step xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm mg
      size hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hout hsz i t32 mf xf yf hmf hxf hyf hi]
    have key := ih _ hlt (i + 1) rfl (t32 + 1)
      (mf.uset (i + mg).toUSize
        (cellM2 m32 n32 xa ya hm hn dmA shDm i t32
          (cellX2 m32 n32 xeA xoA shXe shXo i t32) (cellY2 m32 len32 yeA yoA shYe shYo i t32))
        (by rw [hmf]; exact idx2 hi hout hsz))
      (xf.uset (i + mg).toUSize (cellX2 m32 n32 xeA xoA shXe shXo i t32)
        (by rw [hxf]; exact idx2 hi hout hsz))
      (yf.uset (i + mg).toUSize (cellY2 m32 len32 yeA yoA shYe shYo i t32)
        (by rw [hyf]; exact idx2 hi hout hsz))
      (by rw [Array.size_uset]; exact hmf) (by rw [Array.size_uset]; exact hxf)
      (by rw [Array.size_uset]; exact hyf)
    dsimp only at key
    obtain ⟨h1, h2, h3, hX, hY, hM⟩ := key
    have e1 : (i.toNat + mg.toNat - mg.toNat).toUInt32 = i := by simp
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · intro j
      rw [hX j, Array.uset, Array.getElem?_set, him]
      by_cases hj : j = i.toNat + mg.toNat
      · subst hj
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), e1, UInt32.sub_self, UInt32.add_zero]
      · by_cases hj2 : mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat
        · rw [if_pos (by omega), if_pos hj2, add_one_add_sub_succ]
        · rw [if_neg (by omega), if_neg (Ne.symm hj), if_neg hj2]
    · intro j
      rw [hY j, Array.uset, Array.getElem?_set, him]
      by_cases hj : j = i.toNat + mg.toNat
      · subst hj
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), e1, UInt32.sub_self, UInt32.add_zero]
      · by_cases hj2 : mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat
        · rw [if_pos (by omega), if_pos hj2, add_one_add_sub_succ]
        · rw [if_neg (by omega), if_neg (Ne.symm hj), if_neg hj2]
    · intro j
      rw [hM j, Array.uset, Array.getElem?_set, him]
      by_cases hj : j = i.toNat + mg.toNat
      · subst hj
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), e1, UInt32.sub_self, UInt32.add_zero]
      · by_cases hj2 : mg.toNat + i.toNat ≤ j ∧ j < mg.toNat + w.toNat
        · rw [if_pos (by omega), if_pos hj2, add_one_add_sub_succ]
        · rw [if_neg (by omega), if_neg (Ne.symm hj), if_neg hj2]
  · -- loop exit: nothing written
    have hi' : w.toNat ≤ i.toNat := Nat.le_of_not_lt (fun h => hi (UInt32.lt_iff_toNat_lt.mpr h))
    rw [uFillGo2, dif_neg hi]
    refine ⟨hmf, hxf, hyf, ?_, ?_, ?_⟩ <;> intro j <;> rw [if_neg (by omega)]

end AlignmentSpec.U32Proof

#print axioms AlignmentSpec.U32Proof.uFillGo2_spec
#print axioms AlignmentSpec.U32Proof.uFillGo2_step
#print axioms AlignmentSpec.U32Proof.add_one_add_sub_succ
