import MapperWalk2

/-! Clean seed among any chosen seeds.  `exists_clean_seed2` with the seeds
cut by a fixed `k` (the mapper's seed count) and the error bound taken at a
threshold `T` that may be higher than the mapper's: a walk scoring at least
`T` spoils at most `seedBound sc T` seeds, so among any `seedBound sc T + 1`
distinct seeds — in any order — one is clean, and its window shape obeys the
bounds at `T`. -/

namespace MapSpec

open AlignmentSpec

/-- Default scoring: a window within penalty `P` of a perfect match spoils at
most `P / 4` seeds (`P = 0, 4, 8, 12`). -/
example : seedBound ⟨0, -4, -6, -2⟩ 0 = 0 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-4) = 1 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-8) = 2 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-12) = 3 := by decide

/-- **Clean seed among chosen seeds.**  For a walk of `xs` against `ys` scoring
at least `T`, cut `xs` into `k + 1` seeds of `q = |xs| / (k + 1)` letters.
Any `J` of more than `seedBound sc T` distinct seed indices `≤ k` contains a
clean seed `j`: its `q` letters equal `ys` at some `o`, with window shape
`shapeOk (gapBound sc T) (gapBound2 sc T)`. -/
theorem exists_clean_seed_among (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (xs ys : List Char) (path : List Step)
    (hw : IsMonotoneWalk path xs ys) (hs : T ≤ walkScore sc xs ys path)
    (k : Nat) (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBound sc T < J.length) :
    ∃ j ∈ J, ∃ o,
      o + xs.length / (k + 1) ≤ ys.length ∧
      (ys.drop o).take (xs.length / (k + 1)) =
        (xs.drop (j * (xs.length / (k + 1)))).take (xs.length / (k + 1)) ∧
      shapeOk (gapBound sc T) (gapBound2 sc T)
        ((o : Int) - (j * (xs.length / (k + 1)) : Nat))
        (((ys.length : Int) - o) - ((xs.length : Int) - (j * (xs.length / (k + 1)) : Nat))) := by
  obtain ⟨hx, hy⟩ := hw
  have hv' := hv
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hcost := scoreWalk_le_counts sc hv' path xs ys none hx hy
  unfold walkScore at hs
  have hN := errReps_length_le path xs ys 0 none
  have hb := cost_bounds (-sc.mismatchScore) (-sc.gapOpen) (-sc.gapExtend) T
    (by omega) (by omega) (by omega)
    (mism path xs ys) (runs .gapX path none) (runs .gapY path none) (cnt .gapX path) (cnt .gapY path)
    (errReps path xs ys 0 none).length hN
    (runs_le_cnt _ _ _) (runs_le_cnt _ _ _)
    (runs_pos _ _ _ (by simp)) (runs_pos _ _ _ (by simp))
    (by simp only [Int.neg_mul]; omega)
  have e1 : -(sc.gapOpen + sc.gapExtend) = -sc.gapOpen + -sc.gapExtend := by omega
  have e2 : -T + sc.gapOpen = -T - -sc.gapOpen := by omega
  have e3 : -T + 2 * sc.gapOpen = -T - 2 * -sc.gapOpen := by omega
  have hE : (errReps path xs ys 0 none).length ≤ seedBound sc T := by
    unfold seedBound; rw [e1, e2]; exact hb.1
  have hG : cnt .gapX path + cnt .gapY path ≤ gapBound sc T := by
    unfold gapBound; rw [e2]; exact hb.2.1
  have hG2 : 0 < cnt .gapX path → 0 < cnt .gapY path →
      cnt .gapX path + cnt .gapY path ≤ gapBound2 sc T := by
    unfold gapBound2; rw [e3]; exact hb.2.2
  clear hb hcost hN
  generalize hl : xs.length / (k + 1) = l
  have hlk : (k + 1) * l ≤ xs.length := by
    rw [← hl, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hex : ∃ j ∈ J, ∀ c ∈ errReps path xs ys 0 none,
      ¬(2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l)) := by
    by_cases hl0 : l = 0
    · cases J with
      | nil => simp at hJl
      | cons j _ => exact ⟨j, List.mem_cons_self, fun c _ => by subst hl0; omega⟩
    apply Classical.byContradiction
    intro hno
    have hsub : J ⊆ (errReps path xs ys 0 none).map (fun c => c / (2 * l)) := by
      intro j hj
      have : ∃ c ∈ errReps path xs ys 0 none, 2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l) := by
        apply Classical.byContradiction
        intro hc
        exact hno ⟨j, hj, fun c hcm hcc => hc ⟨c, hcm, hcc⟩⟩
      obtain ⟨c, hcm, hc1, hc2⟩ := this
      refine List.mem_map.mpr ⟨c, hcm, ?_⟩
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_left_comm]; omega
      · rw [Nat.add_mul, Nat.mul_left_comm]; omega
    have := hJn.length_le_of_subset hsub
    simp at this
    omega
  obtain ⟨j, hjJ, hc⟩ := hex
  have hj := hJk j hjJ
  have hjl : j * l + l ≤ xs.length := by
    have : j * l ≤ k * l := Nat.mul_le_mul_right l hj
    rw [Nat.add_mul] at hlk; omega
  obtain ⟨o, pre, post, h0, hpx, hpy, ho, hseed⟩ :=
    prefix_clean2 path xs ys 0 none (j * l) l hx hy hjl hc
  subst h0
  have dpre := sum_diff_eq pre
  have dpost := sum_diff_eq post
  rw [List.map_append, List.sum_append] at hx hy
  rw [cnt_append, cnt_append] at hG hG2
  refine ⟨j, hjJ, o, ho, hseed, ?_, ?_⟩
  · omega
  · by_cases hx0 : 0 < cnt .gapX pre + cnt .gapX post
    · by_cases hy0 : 0 < cnt .gapY pre + cnt .gapY post
      · have := hG2 hx0 hy0; omega
      · omega
    · omega

end MapSpec

#print axioms MapSpec.exists_clean_seed_among
