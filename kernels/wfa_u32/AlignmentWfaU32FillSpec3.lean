import AlignmentWfaU32FillSpec

/-!
# Functional specification of the block-layout cell loop `uFillGo3`

`uFillGo3` is `uFillGo2` with the three fronts written into ONE array `f`
(of size `size3`): cell `j'` (for `i ≤ j' < w`) is written at `oM + j'`
(the M value `cellM2`), `oX + j'` (the X value `cellX2`) and `oY + j'`
(the Y value `cellY2`), each at diagonal `t32 + (j' - i)`.

The loop itself only assumes the three write ranges fit in the array; the
specification below additionally assumes they are laid out in the order
M, X, Y without overlap (`oM + w ≤ oX`, `oX + w ≤ oY`, which the caller in
`AlignmentWfaU32Fill3.lean` satisfies), so that every index of the result
is described by exactly one of the three cell functions or is unchanged.

The proof follows `uFillGo2_spec`: a step lemma `uFillGo3_step` rewrites
one iteration (with `uget` turned into `getD` so the written values are
literally the cell functions), then strong induction on `w - i`.
-/

namespace AlignmentSpec.U32Proof

/-- One step of the block-layout loop, with the written values expressed
through the cell functions. -/
theorem uFillGo3_step (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm oM oX oY : UInt32) (size3 : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hoM : w.toNat + oM.toNat ≤ size3) (hoX : w.toNat + oX.toNat ≤ size3)
    (hoY : w.toNat + oY.toNat ≤ size3) (hsz : size3 < 2 ^ 32)
    (i t32 : UInt32) (f : Array UInt32) (hf : f.size = size3) (hi : i < w) :
    uFillGo3 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm oM oX oY size3
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hoM hoX hoY hsz i t32 f hf =
      uFillGo3 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm oM oX oY size3
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hoM hoX hoY hsz (i + 1) (t32 + 1)
        (((f.uset (i + oM).toUSize
            (cellM2 m32 n32 xa ya hm hn dmA shDm i t32
              (cellX2 m32 n32 xeA xoA shXe shXo i t32) (cellY2 m32 len32 yeA yoA shYe shYo i t32))
            (by rw [hf]; exact idx2 hi hoM hsz)).uset (i + oX).toUSize
            (cellX2 m32 n32 xeA xoA shXe shXo i t32)
            (by rw [Array.size_uset, hf]; exact idx2 hi hoX hsz)).uset (i + oY).toUSize
            (cellY2 m32 len32 yeA yoA shYe shYo i t32)
            (by rw [Array.size_uset, Array.size_uset, hf]; exact idx2 hi hoY hsz))
        (by rw [Array.size_uset, Array.size_uset, Array.size_uset]; exact hf) := by
  rw [uFillGo3, dif_pos hi]
  simp only [uget_eq_getD, cellX2, cellY2, cellM2]

theorem uFillGo3_spec (xa ya : Array Char) (m32 n32 len32 : UInt32) (hm : m32.toNat = xa.size)
    (hn : n32.toNat = ya.size) (w : UInt32)
    (xeA xoA yeA yoA dmA : Array UInt32) (shXe shXo shYe shYo shDm oM oX oY : UInt32) (size3 : Nat)
    (hxe : w.toNat + shXe.toNat ≤ xeA.size) (hxe' : xeA.size < 2 ^ 32)
    (hxo : w.toNat + shXo.toNat ≤ xoA.size) (hxo' : xoA.size < 2 ^ 32)
    (hye : w.toNat + shYe.toNat ≤ yeA.size) (hye' : yeA.size < 2 ^ 32)
    (hyo : w.toNat + shYo.toNat ≤ yoA.size) (hyo' : yoA.size < 2 ^ 32)
    (hdm : w.toNat + shDm.toNat ≤ dmA.size) (hdm' : dmA.size < 2 ^ 32)
    (hoM : w.toNat + oM.toNat ≤ size3) (hoX : w.toNat + oX.toNat ≤ size3)
    (hoY : w.toNat + oY.toNat ≤ size3) (hsz : size3 < 2 ^ 32)
    (hMX : oM.toNat + w.toNat ≤ oX.toNat) (hXY : oX.toNat + w.toNat ≤ oY.toNat) :
    ∀ (i t32 : UInt32) (f : Array UInt32) (hf : f.size = size3),
      let r := uFillGo3 xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm oM oX oY size3
        hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hoM hoX hoY hsz i t32 f hf
      r.size = size3 ∧
      ∀ j, r[j]? =
        if oM.toNat + i.toNat ≤ j ∧ j < oM.toNat + w.toNat then
          some (cellM2 m32 n32 xa ya hm hn dmA shDm (j - oM.toNat).toUInt32
            (t32 + ((j - oM.toNat).toUInt32 - i))
            (cellX2 m32 n32 xeA xoA shXe shXo (j - oM.toNat).toUInt32 (t32 + ((j - oM.toNat).toUInt32 - i)))
            (cellY2 m32 len32 yeA yoA shYe shYo (j - oM.toNat).toUInt32 (t32 + ((j - oM.toNat).toUInt32 - i))))
        else if oX.toNat + i.toNat ≤ j ∧ j < oX.toNat + w.toNat then
          some (cellX2 m32 n32 xeA xoA shXe shXo (j - oX.toNat).toUInt32 (t32 + ((j - oX.toNat).toUInt32 - i)))
        else if oY.toNat + i.toNat ≤ j ∧ j < oY.toNat + w.toNat then
          some (cellY2 m32 len32 yeA yoA shYe shYo (j - oY.toNat).toUInt32 (t32 + ((j - oY.toNat).toUInt32 - i)))
        else f[j]? := by
  intro i
  generalize hk : w.toNat - i.toNat = k
  induction k using Nat.strongRecOn generalizing i with
  | _ k ih =>
  intro t32 f hf
  dsimp only
  by_cases hi : i < w
  · -- one more cell: unfold one step and use the induction hypothesis on the tail
    have hi' : i.toNat < w.toNat := UInt32.lt_iff_toNat_lt.mp hi
    have hw : w.toNat < 2 ^ 32 := UInt32.toNat_lt_size w
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have hiM : (i + oM).toUSize.toNat = i.toNat + oM.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hiX : (i + oX).toUSize.toNat = i.toNat + oX.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hiY : (i + oY).toUSize.toNat = i.toNat + oY.toNat := by
      rw [UInt32.toNat_toUSize, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hlt : w.toNat - (i + 1).toNat < k := hk ▸ succ_lt_toNat2 hi
    rw [uFillGo3_step xa ya m32 n32 len32 hm hn w xeA xoA yeA yoA dmA shXe shXo shYe shYo shDm
      oM oX oY size3 hxe hxe' hxo hxo' hye hye' hyo hyo' hdm hdm' hoM hoX hoY hsz i t32 f hf hi]
    have key := ih _ hlt (i + 1) rfl (t32 + 1)
      (((f.uset (i + oM).toUSize
          (cellM2 m32 n32 xa ya hm hn dmA shDm i t32
            (cellX2 m32 n32 xeA xoA shXe shXo i t32) (cellY2 m32 len32 yeA yoA shYe shYo i t32))
          (by rw [hf]; exact idx2 hi hoM hsz)).uset (i + oX).toUSize
          (cellX2 m32 n32 xeA xoA shXe shXo i t32)
          (by rw [Array.size_uset, hf]; exact idx2 hi hoX hsz)).uset (i + oY).toUSize
          (cellY2 m32 len32 yeA yoA shYe shYo i t32)
          (by rw [Array.size_uset, Array.size_uset, hf]; exact idx2 hi hoY hsz))
      (by rw [Array.size_uset, Array.size_uset, Array.size_uset]; exact hf)
    dsimp only at key
    obtain ⟨h1, hAll⟩ := key
    have e1 : (i.toNat + oM.toNat - oM.toNat).toUInt32 = i := by simp
    have e2 : (i.toNat + oX.toNat - oX.toNat).toUInt32 = i := by simp
    have e3 : (i.toNat + oY.toNat - oY.toNat).toUInt32 = i := by simp
    refine ⟨h1, ?_⟩
    intro j
    rw [hAll j]
    simp only [Array.uset_eq_set, Array.getElem?_set, hiM, hiX, hiY, hi1]
    by_cases hjM : j = i.toNat + oM.toNat
    · -- the M cell written in this step
      subst hjM
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl, if_pos (by omega), e1, UInt32.sub_self, UInt32.add_zero]
    by_cases hjX : j = i.toNat + oX.toNat
    · -- the X cell written in this step
      subst hjX
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos rfl, if_neg (by omega), if_pos (by omega), e2, UInt32.sub_self, UInt32.add_zero]
    by_cases hjY : j = i.toNat + oY.toNat
    · -- the Y cell written in this step
      subst hjY
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl,
        if_neg (by omega), if_neg (by omega), if_pos (by omega), e3, UInt32.sub_self, UInt32.add_zero]
    -- an index not written in this step: the tail's description carries over
    by_cases hj1 : oM.toNat + i.toNat ≤ j ∧ j < oM.toNat + w.toNat
    · rw [if_pos (by omega), if_pos hj1, add_one_add_sub_succ]
    by_cases hj2 : oX.toNat + i.toNat ≤ j ∧ j < oX.toNat + w.toNat
    · rw [if_neg (by omega), if_pos (by omega), if_neg hj1, if_pos hj2, add_one_add_sub_succ]
    by_cases hj3 : oY.toNat + i.toNat ≤ j ∧ j < oY.toNat + w.toNat
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg hj1, if_neg hj2,
        if_pos hj3, add_one_add_sub_succ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg hj1, if_neg hj2, if_neg hj3]
  · -- loop exit: nothing written
    have hi' : w.toNat ≤ i.toNat := Nat.le_of_not_lt (fun h => hi (UInt32.lt_iff_toNat_lt.mpr h))
    rw [uFillGo3, dif_neg hi]
    refine ⟨hf, ?_⟩
    intro j
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end AlignmentSpec.U32Proof

#print axioms AlignmentSpec.U32Proof.uFillGo3_spec
#print axioms AlignmentSpec.U32Proof.uFillGo3_step
