import AlignmentWfaU32Fill3
import AlignmentWfaU32Level2

/-!
# Block-history bookkeeping

The glue between the block-layout run (`uLoop3`/`uRun3`, one array history
indexed by level, AlignmentWfaU32Fill3.lean) and the three-array run
(`uLoop`, list window `hist`, AlignmentWfaU32Loop.lean):

* the view `toU` of the empty block level is `uEmpty`, and of the block seed
  `seedB` is the three-array seed `seedU` (`toU_bEmpty`, `toU_seedB`);
* the corner test on the M block is the corner test of the view
  (`corner3_eq`), under the block-size discipline of the builder;
* the source relation `toU margin (srcOf3 trace p d) = frontAtU hist d` for
  `1 ≤ d ≤ K` is established by the seed (`srcRel_seed`) and carried by one
  push / one cons-and-take step (`srcRel_step`);
* a source is either `bEmpty` or a level of the trace (`srcOf3_mem`).
-/
namespace AlignmentSpec.U32Proof

-- ── views of the empty level and of the seed ──

theorem toU_bEmpty (margin : Nat) : toU margin bEmpty = uEmpty := by
  simp only [toU, bEmpty, blockOf, Array.extract_empty]
  rfl

/-- Reads of a three-block concatenation of equal-size blocks. -/
theorem blk3_getElem? (a b c : Array UInt32) (k : Nat) (ha : a.size = k) (hb : b.size = k)
    (hc : c.size = k) (i : Nat) :
    (a ++ b ++ c)[i]? = if i < k then a[i]? else if i < 2 * k then b[i - k]? else c[i - 2 * k]? := by
  rw [Array.getElem?_append, Array.getElem?_append, Array.size_append, ha, hb]
  by_cases h1 : i < k
  · rw [if_pos (show i < k + k by omega), if_pos h1, if_pos h1]
  · by_cases h2 : i < 2 * k
    · rw [if_pos (show i < k + k by omega), if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg (show ¬ i < k + k by omega), if_neg h1, if_neg h2]
      have e : i - (k + k) = i - 2 * k := by omega
      rw [e]

/-- A read of block `b < 3` of a level whose array has exactly three blocks. -/
theorem blockOf_getElem? (margin b : Nat) (s : BLevel) (hsz : s.blk.size = 3 * (s.w + 2 * margin))
    (hb : b < 3) (i : Nat) :
    (blockOf margin b s)[i]? =
      if i < s.w + 2 * margin then s.blk[b * (s.w + 2 * margin) + i]? else none := by
  unfold blockOf
  rw [Array.getElem?_extract, hsz]
  have hle : b * (s.w + 2 * margin) ≤ 2 * (s.w + 2 * margin) := Nat.mul_le_mul_right _ (by omega)
  have e : min ((b + 1) * (s.w + 2 * margin)) (3 * (s.w + 2 * margin)) - b * (s.w + 2 * margin)
      = s.w + 2 * margin := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [e]

/-- The view of a block level built from three fronts of the right size. -/
theorem toU_mk (margin lo w : Nat) (a b c : Array UInt32) (ha : a.size = w + 2 * margin)
    (hb : b.size = w + 2 * margin) (hc : c.size = w + 2 * margin) :
    toU margin ⟨lo, w, a ++ b ++ c⟩ = ⟨lo, w, a, b, c⟩ := by
  have hsz : (a ++ b ++ c).size = 3 * (w + 2 * margin) := by
    simp only [Array.size_append, ha, hb, hc]; omega
  have h0 : blockOf margin 0 ⟨lo, w, a ++ b ++ c⟩ = a := by
    apply arr_ext?; intro i
    rw [blockOf_getElem? margin 0 ⟨lo, w, a ++ b ++ c⟩ hsz (by omega) i]
    dsimp only
    rw [blk3_getElem? a b c _ ha hb hc]
    by_cases hi : i < w + 2 * margin
    · rw [if_pos hi, Nat.zero_mul, Nat.zero_add, if_pos hi]
    · rw [if_neg hi, Array.getElem?_eq_none (by omega)]
  have h1 : blockOf margin 1 ⟨lo, w, a ++ b ++ c⟩ = b := by
    apply arr_ext?; intro i
    rw [blockOf_getElem? margin 1 ⟨lo, w, a ++ b ++ c⟩ hsz (by omega) i]
    dsimp only
    rw [blk3_getElem? a b c _ ha hb hc]
    by_cases hi : i < w + 2 * margin
    · rw [if_pos hi, Nat.one_mul, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    · rw [if_neg hi, Array.getElem?_eq_none (by omega)]
  have h2 : blockOf margin 2 ⟨lo, w, a ++ b ++ c⟩ = c := by
    apply arr_ext?; intro i
    rw [blockOf_getElem? margin 2 ⟨lo, w, a ++ b ++ c⟩ hsz (by omega) i]
    dsimp only
    rw [blk3_getElem? a b c _ ha hb hc]
    by_cases hi : i < w + 2 * margin
    · rw [if_pos hi, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    · rw [if_neg hi, Array.getElem?_eq_none (by omega)]
  unfold toU
  rw [h0, h1, h2]

theorem seedU_mf_size (m margin : Nat) (xa ya : Array Char) :
    (seedU m margin xa ya).mf.size = 1 + 2 * margin := by
  show (pushZeros margin ((pushZeros margin (Array.emptyWithCapacity (2 * margin + 1))).push
    ((lcpArr xa ya 0 0).toUInt32 + 1))).size = _
  rw [pushZeros_size, (seed_arr_spec margin _).1]
  omega

theorem toU_seedB (m margin : Nat) (xa ya : Array Char) :
    toU margin (seedB m margin xa ya) = seedU m margin xa ya :=
  toU_mk margin m 1 (seedU m margin xa ya).mf (seedU m margin xa ya).xf (seedU m margin xa ya).yf
    (seedU_mf_size m margin xa ya)
    (by show (Array.replicate (2 * margin + 1) (0 : UInt32)).size = _; rw [Array.size_replicate]; omega)
    (by show (Array.replicate (2 * margin + 1) (0 : UInt32)).size = _; rw [Array.size_replicate]; omega)

-- ── the corner test ──

theorem toUInt32_succ_ne_zero (m : Nat) (hm : m + 2 < 2 ^ 30) : m.toUInt32 + 1 ≠ 0 := by
  intro h
  have := congrArg UInt32.toNat h
  rw [UInt32.toNat_add, toNat_toUInt32_of_lt m (by omega)] at this
  simp at this
  omega

theorem corner3_eq (margin m n : Nat) (lv : BLevel) (hm : m + 2 < 2 ^ 30)
    (hsz : lv.w ≠ 0 → lv.blk.size = 3 * (lv.w + 2 * margin)) (hw : lv.w = 0 → lv.blk = #[]) :
    corner3 margin m n lv = cornerU margin m n (toU margin lv) := by
  have hne := toUInt32_succ_ne_zero m hm
  by_cases hw0 : lv.w = 0
  · have hb := hw hw0
    have hL : corner3 margin m n lv = false := by
      simp only [corner3]
      rw [hw0, bne_self_eq_false, Bool.false_and]
    have hR : cornerU margin m n (toU margin lv) = false := by
      simp only [cornerU, uget, ugetA, toU, blockOf]
      rw [hb, Array.extract_empty, Array.getD_eq_getD_getElem?, Array.getElem?_empty, Option.getD_none,
        beq_eq_false_iff_ne]
      exact fun h => hne h.symm
    rw [hL, hR]
  · have hs := hsz hw0
    have hL : corner3 margin m n lv =
        (decide (n + margin - lv.lo < lv.w + 2 * margin) &&
          (lv.blk.getD (n + margin - lv.lo) 0 == m.toUInt32 + 1)) := by
      simp only [corner3]
      rw [bne_iff_ne.mpr hw0, Bool.true_and]
    rw [hL]
    simp only [cornerU, uget, ugetA, toU]
    rw [Array.getD_eq_getD_getElem? (xs := blockOf margin 0 lv), blockOf_getElem? margin 0 lv hs (by omega),
      Nat.zero_mul, Nat.zero_add]
    by_cases hi : n + margin - lv.lo < lv.w + 2 * margin
    · rw [if_pos hi, decide_eq_true hi, Bool.true_and, Array.getD_eq_getD_getElem?]
    · rw [if_neg hi, decide_eq_false hi, Bool.false_and, Option.getD_none]
      rw [eq_comm, beq_eq_false_iff_ne]
      exact fun h => hne h.symm

-- ── history bookkeeping ──

theorem srcOf3_push_one (trace : Array BLevel) (lv : BLevel) (p : Nat) (hp : trace.size = p) :
    srcOf3 (trace.push lv) (p + 1) 1 = lv := by
  simp only [srcOf3]
  rw [if_pos (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_push, hp, if_pos (by omega)]
  rfl

theorem srcOf3_push_succ (trace : Array BLevel) (lv : BLevel) (p d : Nat) (hp : trace.size = p)
    (hd : 1 ≤ d) : srcOf3 (trace.push lv) (p + 1) (d + 1) = srcOf3 trace p d := by
  simp only [srcOf3]
  by_cases h : d ≤ p
  · rw [if_pos (by omega), if_pos h, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_push, hp, if_neg (by omega)]
    have e : p + 1 - (d + 1) = p - d := by omega
    rw [e]
  · rw [if_neg (by omega), if_neg h]

theorem frontAtU_cons_one (lv : ULevel) (hist : List ULevel) : frontAtU (lv :: hist) 1 = lv := rfl

theorem frontAtU_cons_succ (lv : ULevel) (hist : List ULevel) (d : Nat) (hd : 1 ≤ d) :
    frontAtU (lv :: hist) (d + 1) = frontAtU hist d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold frontAtU
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, List.getElem?_cons_succ]

theorem frontAtU_take (hist : List ULevel) (K d : Nat) (hd : 1 ≤ d) (hdK : d ≤ K) :
    frontAtU (hist.take K) d = frontAtU hist d := by
  unfold frontAtU
  rw [List.getElem?_take_of_lt (by omega)]

theorem srcRel_step (margin K : Nat) (trace : Array BLevel) (hist : List ULevel) (p : Nat)
    (lv : BLevel) (hp : trace.size = p)
    (hrel : ∀ d, 1 ≤ d → d ≤ K → toU margin (srcOf3 trace p d) = frontAtU hist d) :
    ∀ d, 1 ≤ d → d ≤ K →
      toU margin (srcOf3 (trace.push lv) (p + 1) d) = frontAtU ((toU margin lv :: hist).take K) d := by
  intro d hd hdK
  rw [frontAtU_take _ K d hd hdK]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  by_cases he : e = 0
  · subst he
    show toU margin (srcOf3 (trace.push lv) (p + 1) 1) = frontAtU (toU margin lv :: hist) 1
    rw [srcOf3_push_one trace lv p hp, frontAtU_cons_one]
  · rw [srcOf3_push_succ trace lv p e hp (by omega), frontAtU_cons_succ _ _ e (by omega)]
    exact hrel e (by omega) (by omega)

theorem srcRel_seed (margin : Nat) (b : BLevel) :
    ∀ d, 1 ≤ d → toU margin (srcOf3 #[b] 1 d) = frontAtU [toU margin b] d := by
  intro d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  cases e with
  | zero =>
    show toU margin (srcOf3 ((#[] : Array BLevel).push b) (0 + 1) 1) = frontAtU (toU margin b :: []) 1
    rw [srcOf3_push_one #[] b 0 rfl, frontAtU_cons_one]
  | succ e =>
    simp only [srcOf3]
    rw [if_neg (by omega), toU_bEmpty]
    unfold frontAtU
    have h : e + 1 + 1 - 1 = e + 1 := by omega
    rw [h, List.getElem?_cons_succ, List.getElem?_nil]

theorem srcOf3_mem (trace : Array BLevel) (p d : Nat) :
    srcOf3 trace p d = bEmpty ∨ srcOf3 trace p d ∈ trace := by
  unfold srcOf3
  split
  · rw [Array.getD_eq_getD_getElem?]
    cases h : trace[p - d]? with
    | none => left; rfl
    | some x => right; exact Array.mem_of_getElem? h
  · left; rfl

#print axioms toU_seedB
#print axioms corner3_eq
#print axioms srcRel_step

end AlignmentSpec.U32Proof
