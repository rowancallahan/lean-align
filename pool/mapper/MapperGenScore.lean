import MapperFastKernel
import MapperFastScore

/-!
Window penalties capped at any `Q`, exact up to `lim = min Q 15`.

`penQ Q xs ys` = minus the optimal score when it is `≥ −Q`, else `Q + 1`.
A walk scoring `≥ −15` is gapless or has one gap run of length `≤ 4`
(`shape15`), so (`penQ_same`, `penQ_ins`, `penQ_del`):

* same length: `penQ = 4·hamming` when `penQ ≤ min Q 15`;
* lengths `n` and `n + L` (or `n − L`): `penQ = 6 + 2L + 4·M` (`M` the fewest
  mismatches over the gap positions) when `penQ ≤ min Q 15`;

and these formulas bound `penQ` from above.  Hence `min penQ (lim + 1)` is the
formula capped at `lim + 1` (`min_eq_of`), which the byte kernel `kerG`
computes (`kerG_window`): `hamming` for the same length, `gappedPen2` (exact for
`lim ≤ 15`, `gappedPen2_specX`) for one gap.
-/

namespace MapSpec

open AlignmentSpec

/-- Penalty capped at `Q`. -/
def penQ (Q : Nat) (xs ys : List Char) : Nat :=
  match getBestAlignment sc0 xs ys with
  | some (_, bs) => if -(Q : Int) ≤ bs then (-bs).toNat else Q + 1
  | none => Q + 1

theorem penQ_of (Q : Nat) (xs ys : List Char) (path : List Step) (bs : Int)
    (h : getBestAlignment sc0 xs ys = some (path, bs)) :
    penQ Q xs ys = if -(Q : Int) ≤ bs then (-bs).toNat else Q + 1 := by
  simp [penQ, h]

theorem penQ_le (Q : Nat) (xs ys : List Char) : penQ Q xs ys ≤ Q + 1 := by
  unfold penQ; split
  · split <;> omega
  · omega

/-- Mismatches, runs and columns of a walk scoring `≥ −15`. -/
theorem counts15 (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -15 ≤ walkScore sc0 xs ys path) :
    4 * mism path xs ys + 6 * runs .gapX path none + 6 * runs .gapY path none +
      2 * cnt .gapX path + 2 * cnt .gapY path ≤ 15 ∧
    (0 < cnt .gapX path → 0 < runs .gapX path none) ∧
    (0 < cnt .gapY path → 0 < runs .gapY path none) ∧
    runs .gapX path none ≤ cnt .gapX path ∧ runs .gapY path none ≤ cnt .gapY path := by
  obtain ⟨hx, hy⟩ := hw
  have h := scoreWalk_le_counts sc0 valid_sc0 path xs ys none hx hy
  unfold walkScore at hs
  simp only [sc0] at h hs
  exact ⟨by omega, runs_pos _ _ _ (by simp), runs_pos _ _ _ (by simp), runs_le_cnt _ _ _, runs_le_cnt _ _ _⟩

/-- A walk scoring `≥ −15` is gapless, or one gap run of length `≤ 4`. -/
theorem shape15 (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -15 ≤ walkScore sc0 xs ys path) :
    path = List.replicate xs.length .diag ∨
    (∃ i L j, 0 < L ∧ L ≤ 4 ∧ path = List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) ∨
    (∃ i L j, 0 < L ∧ L ≤ 4 ∧ path = List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := counts15 path xs ys hw hs
  by_cases hX : cnt .gapX path = 0
  · by_cases hY : cnt .gapY path = 0
    · left
      exact (eq_diags_of_no_gap path xs ys hw (by
        intro h; rcases h with h | h
        · exact cnt_eq_zero _ _ hX h
        · exact cnt_eq_zero _ _ hY h)).2
    · right; right
      obtain ⟨i, l, j, hl, he⟩ := shape_one_run .gapY (by decide) path none (by simp)
        (not_mem_iff_all' path (cnt_eq_zero _ _ hX)) (by have := h3 (by omega); omega)
      refine ⟨i, l, j, hl, ?_, he⟩
      have : cnt .gapY path = l := by rw [he, cnt_shape _ _ (by decide)]; simp
      omega
  · right; left
    have hY : cnt .gapY path = 0 := by have := h2 (by omega); omega
    obtain ⟨i, l, j, hl, he⟩ := shape_one_run .gapX (by decide) path none (by simp)
      (not_mem_iff_all path (cnt_eq_zero _ _ hY)) (by have := h2 (by omega); omega)
    refine ⟨i, l, j, hl, ?_, he⟩
    have : cnt .gapX path = l := by rw [he, cnt_shape _ _ (by decide)]; simp
    omega

/-- **Same length.** -/
theorem penQ_same (Q : Nat) (xs ys : List Char) (hl : xs.length = ys.length) :
    (4 * hamming xs ys ≤ Q → penQ Q xs ys ≤ 4 * hamming xs ys) ∧
    (penQ Q xs ys ≤ Q → penQ Q xs ys ≤ 15 → penQ Q xs ys = 4 * hamming xs ys) := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penQ_of Q xs ys path bs hb]
  have hlo := hmax _ (diags_isMonotoneWalk xs ys hl)
  rw [walkScore, score_diags_all xs ys none hl _ rfl] at hlo
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [if_pos (by omega)]; omega
  · split at h1
    · rw [if_pos (by omega)] at h2 ⊢
      rcases shape15 path xs ys hw (by omega) with he | ⟨i, L, j, hL, -, he⟩ | ⟨i, L, j, hL, -, he⟩
      · rw [← hs, he, walkScore, score_diags_all xs ys none hl _ rfl]; omega
      · have := lengths_ins (he ▸ hw); omega
      · have := lengths_del (he ▸ hw); omega
    · omega

/-- **Insertion.**  `|ys| = |xs| + L`. -/
theorem penQ_ins (Q : Nat) (xs ys : List Char) (L : Nat) (hl : ys.length = xs.length + L) (h1 : 1 ≤ L) :
    (6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length ≤ Q →
      penQ Q xs ys ≤ 6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length) ∧
    (penQ Q xs ys ≤ Q → penQ Q xs ys ≤ 15 →
      penQ Q xs ys = 6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length) := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penQ_of Q xs ys path bs hb]
  obtain ⟨i0, hi0, hM⟩ := minUpTo_mem (misIns xs ys L) xs.length
  have hlo := hmax _ (walk_ins xs ys i0 L (xs.length - i0) (by omega) (by omega))
  rw [score_ins xs ys i0 L (xs.length - i0) (by omega) (by omega) (by omega), ← hM] at hlo
  refine ⟨fun h => ?_, fun h2 h3 => ?_⟩
  · rw [if_pos (by omega)]; omega
  · split at h2
    · rw [if_pos (by omega)] at h3 ⊢
      rcases shape15 path xs ys hw (by omega) with he | ⟨i, l, j, hL, -, he⟩ | ⟨i, l, j, hL, -, he⟩
      · have := length_of_diags hw he; omega
      · have hlen := lengths_ins (he ▸ hw)
        have hlL : l = L := by omega
        subst hlL
        have hle := minUpTo_le (misIns xs ys l) xs.length i (by omega)
        rw [← hs, he, score_ins xs ys i l j hL hlen.1 hlen.2] at *
        omega
      · have := lengths_del (he ▸ hw); omega
    · omega

/-- **Deletion.**  `|xs| = |ys| + L`. -/
theorem penQ_del (Q : Nat) (xs ys : List Char) (L : Nat) (hl : xs.length = ys.length + L) (h1 : 1 ≤ L) :
    (6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length ≤ Q →
      penQ Q xs ys ≤ 6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length) ∧
    (penQ Q xs ys ≤ Q → penQ Q xs ys ≤ 15 →
      penQ Q xs ys = 6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length) := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penQ_of Q xs ys path bs hb]
  obtain ⟨i0, hi0, hM⟩ := minUpTo_mem (misDel xs ys L) ys.length
  have hlo := hmax _ (walk_del xs ys i0 L (ys.length - i0) (by omega) (by omega))
  rw [score_del xs ys i0 L (ys.length - i0) (by omega) (by omega) (by omega), ← hM] at hlo
  refine ⟨fun h => ?_, fun h2 h3 => ?_⟩
  · rw [if_pos (by omega)]; omega
  · split at h2
    · rw [if_pos (by omega)] at h3 ⊢
      rcases shape15 path xs ys hw (by omega) with he | ⟨i, l, j, hL, -, he⟩ | ⟨i, l, j, hL, -, he⟩
      · have := length_of_diags hw he; omega
      · have := lengths_ins (he ▸ hw); omega
      · have hlen := lengths_del (he ▸ hw)
        have hlL : l = L := by omega
        subst hlL
        have hle := minUpTo_le (misDel xs ys l) ys.length i (by omega)
        rw [← hs, he, score_del xs ys i l j hL hlen.1 hlen.2] at *
        omega
    · omega

/-- An upper bound that is exact up to `min Q 15` fixes the penalty capped at `lim + 1`. -/
theorem min_eq_of (Q lim pen f : Nat) (hl1 : lim ≤ Q) (hl2 : lim ≤ 15)
    (h1 : f ≤ Q → pen ≤ f) (h2 : pen ≤ Q → pen ≤ 15 → pen = f) :
    min pen (lim + 1) = min f (lim + 1) := by
  by_cases hp : pen ≤ lim
  · rw [h2 (by omega) (by omega)]
  · by_cases hf : f ≤ lim
    · have := h1 (by omega); omega
    · omega

end MapSpec

namespace MapSpec.Fast

open MapSpec

/-- The window formula: `4·mismatches` for the same length, else one gap. -/
def fB (R G : ByteArray) (st len : Nat) : Nat :=
  if len = R.size then 4 * preB R G st R.size
  else 6 + 2 * gapLen R.size len + 4 * minMis R G st len

/-- **Bytes.**  Over a byte genome, the capped penalty of a window is the formula
capped at `lim + 1`. -/
theorem penQ_window (Q lim : Nat) (hl1 : lim ≤ Q) (hl2 : lim ≤ 15) (R G : ByteArray) (xs seq : List Char)
    (hr : Encodes R xs) (hg : Encodes G seq) (st len : Nat) (hfit : st + len ≤ seq.length) :
    min (penQ Q xs ((seq.drop st).take len)) (lim + 1) = min (fB R G st len) (lim + 1) := by
  have hn : R.size = xs.length := hr.1
  have hG : G.size = seq.length := hg.1
  generalize hys : (seq.drop st).take len = ys
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  have hpre : ∀ i, i ≤ xs.length → i ≤ len →
      MapSpec.hamming (xs.take i) (ys.take i) = preB R G st i := by
    intro i h1 h2
    unfold preB
    rw [hamming_cnt _ _ (fun k => R.get! k != G.get! (st + k)) (fun k h1' h2' => by
      simp only [List.getElem_take]
      rw [neq_bytes hr hg k (st + k) (by simp at h1'; omega) (by simp at h2'; omega), hyk k (by simp at h2'; omega)])]
    congr 1; simp; omega
  unfold fB
  by_cases hsame : len = R.size
  · rw [if_pos hsame]
    have := hpre xs.length (Nat.le_refl _) (by omega)
    rw [List.take_length, List.take_of_length_le (by omega)] at this
    rw [hn, ← this]
    obtain ⟨a, b⟩ := penQ_same Q xs ys (by omega)
    exact min_eq_of Q lim _ _ hl1 hl2 a b
  rw [if_neg hsame]
  unfold minMis gapLen skipOf
  by_cases hlt : R.size < len
  · -- insertion
    simp only [hlt, if_true, show ¬ len < R.size by omega, if_false]
    have hM : minUpTo (misIns xs ys (len - R.size)) xs.length =
        minUpTo (misB R G st len 0) (R.size - 0) := by
      rw [Nat.sub_zero, hn]
      apply minUpTo_congr
      intro i hi
      unfold misIns misB
      rw [hpre i hi (by omega), Nat.add_zero]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + k) != G.get! (st + len + (i + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg (i + k) (st + len + (i + k) - R.size) (by omega) (by omega),
          hyk _ (by omega)]
        have e : st + (i + (len - xs.length) + k) = st + len + (i + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) i 0]
      congr 1 <;> simp <;> omega
    rw [← hM]
    obtain ⟨a, b⟩ := penQ_ins Q xs ys (len - R.size) (by omega) (by omega)
    exact min_eq_of Q lim _ _ hl1 hl2 a b
  · -- deletion
    have hlt' : len < R.size := by omega
    simp only [hlt, hlt', if_true, if_false]
    have hM : minUpTo (misDel xs ys (R.size - len)) ys.length =
        minUpTo (misB R G st len (R.size - len)) (R.size - (R.size - len)) := by
      rw [show R.size - (R.size - len) = ys.length by omega]
      apply minUpTo_congr
      intro i hi
      unfold misDel misB
      rw [hpre i (by omega) (by omega)]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + (R.size - len) + k) !=
          G.get! (st + len + (i + (R.size - len) + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg _ _ (by omega) (by omega), hyk (i + k) (by omega)]
        have e : st + (i + k) = st + len + (i + (R.size - len) + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + (R.size - len)) 0]
      congr 1 <;> simp <;> omega
    rw [← hM]
    obtain ⟨a, b⟩ := penQ_del Q xs ys (R.size - len) (by omega) (by omega)
    exact min_eq_of Q lim _ _ hl1 hl2 a b

/-- **One-gap windows** for `lim ≤ 15`: `gappedPen2` is the one-gap formula capped at `lim + 1`. -/
theorem gappedPen2_specX (R G : ByteArray) (st len lim : Nat) (hne : len ≠ R.size)
    (hlim : lim ≤ 15) :
    gappedPen2 R G st len lim = min (6 + 2 * gapLen R.size len + 4 * minMis R G st len) (lim + 1) := by
  have hL : gapLen R.size len = if len > R.size then len - R.size else R.size - len := rfl
  have hsk : skipOf R.size len = if len < R.size then gapLen R.size len else 0 := by
    unfold skipOf gapLen; split <;> (try split) <;> omega
  unfold gappedPen2 minMis
  simp only []
  rw [← hL, ← hsk]
  generalize hLv : gapLen R.size len = L at *
  generalize hskv : skipOf R.size len = skip at *
  have hL1 : 1 ≤ L := by rw [← hLv]; unfold gapLen; split <;> omega
  have hstop : skip ≤ R.size := by rw [← hskv]; unfold skipOf; split <;> omega
  by_cases hl : lim < 6 + 2 * L
  · rw [if_pos hl]; omega
  rw [if_neg hl]
  obtain ⟨f1a, f1b, f1⟩ := fwdMis_spec R G st (R.size - skip) _ 0 1 rfl (by omega) (Nat.le_refl _)
  obtain ⟨f2a, f2b, f2⟩ := fwdMis_spec R G st (R.size - skip) _ 0 2 rfl (by omega) (by omega)
  obtain ⟨e1a, e1b, e1⟩ := bwdMis_spec R G st len skip _ R.size 1 rfl hstop (Nat.le_refl _)
  obtain ⟨e2a, e2b, e2⟩ := bwdMis_spec R G st len skip _ R.size 2 rfl hstop (by omega)
  generalize fwdMis R G st (R.size - skip) 0 1 = F1 at *
  generalize fwdMis R G st (R.size - skip) 0 2 = F2 at *
  generalize bwdMis R G st len skip R.size 1 = E1 at *
  generalize bwdMis R G st len skip R.size 2 = E2 at *
  have hmis : ∀ i, i ≤ R.size - skip → misB R G st len skip i =
      cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) +
        cntP (fun x => R.get! x != G.get! (st + len + x - R.size)) (i + skip) (R.size - (i + skip)) := by
    intro i _; rfl
  have hM0 : minUpTo (misB R G st len skip) (R.size - skip) = 0 ↔ E1 - skip ≤ F1 := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
      rw [h, hmis i hi] at he
      have := (f1 i (by omega) hi).1 (by omega)
      have := (e1 (i + skip) (by omega) (by omega)).1 (by omega)
      omega
    · intro h
      have := minUpTo_le (misB R G st len skip) (R.size - skip) F1 f1b
      rw [hmis F1 f1b] at this
      have := (f1 F1 (by omega) f1b).2 (Nat.le_refl _)
      have := (e1 (F1 + skip) (by omega) (by omega)).2 (by omega)
      omega
  have hM1 : minUpTo (misB R G st len skip) (R.size - skip) ≤ 1 ↔ (E1 - skip ≤ F2 ∨ E2 - skip ≤ F1) := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := minUpTo_mem (misB R G st len skip) (R.size - skip)
      rw [hmis i hi] at he
      by_cases hpre : cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) = 0
      · right
        have := (f1 i (by omega) hi).1 (by omega)
        have := (e2 (i + skip) (by omega) (by omega)).1 (by omega)
        omega
      · left
        have := (f2 i (by omega) hi).1 (by omega)
        have := (e1 (i + skip) (by omega) (by omega)).1 (by omega)
        omega
    · rintro (h | h)
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F2 f2b
        rw [hmis F2 f2b] at this
        have := (f2 F2 (by omega) f2b).2 (Nat.le_refl _)
        have := (e1 (F2 + skip) (by omega) (by omega)).2 (by omega)
        omega
      · have := minUpTo_le (misB R G st len skip) (R.size - skip) F1 f1b
        rw [hmis F1 f1b] at this
        have := (f1 F1 (by omega) f1b).2 (Nat.le_refl _)
        have := (e2 (F1 + skip) (by omega) (by omega)).2 (by omega)
        omega
  generalize minUpTo (misB R G st len skip) (R.size - skip) = M at *
  by_cases h0 : E1 - skip ≤ F1
  · rw [if_pos h0, hM0.2 h0]; omega
  · rw [if_neg h0]
    have hM0' : M ≠ 0 := fun h => h0 (hM0.1 h)
    by_cases hl2 : lim < 10 + 2 * L
    · rw [if_pos hl2]; omega
    · rw [if_neg hl2]
      by_cases h1 : (decide (E1 - skip ≤ F2) || decide (E2 - skip ≤ F1)) = true
      · rw [if_pos h1]
        have := hM1.2 (by simpa using h1)
        omega
      · rw [if_neg h1]
        have : ¬ M ≤ 1 := fun h => h1 (by simpa using hM1.1 h)
        omega

/-- The window kernel: penalty of window `(st, len)` capped at `lim + 1` (`lim ≤ 15`). -/
def kerG (R G : ByteArray) (st len lim : Nat) : Nat :=
  if st + len ≤ G.size then
    if len = R.size then
      let h := hamming R G st (lim / 4) 0 R.size 0
      if 4 * h ≤ lim then 4 * h else lim + 1
    else gappedPen2 R G st len lim
  else lim + 1

theorem kerG_eq (R G : ByteArray) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerG R G st len lim = if st + len ≤ G.size then min (fB R G st len) (lim + 1) else lim + 1 := by
  unfold kerG
  split
  · unfold fB
    split
    · next hs =>
      dsimp only
      rw [hamming_spec R G st (lim / 4) R.size _ 0 0 rfl (Nat.zero_le _), Nat.zero_add]
      unfold preB
      rw [Nat.sub_zero]
      generalize cntP (fun k => R.get! k != G.get! (st + k)) 0 R.size = c
      by_cases hc : c ≤ lim / 4
      · rw [Nat.min_eq_left (by omega), if_pos (by omega)]; omega
      · rw [Nat.min_eq_right (by omega), if_neg (by omega)]; omega
    · next hs => exact gappedPen2_specX R G st len lim hs hlim
  · rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.penQ_window
#print axioms MapSpec.Fast.kerG_eq
