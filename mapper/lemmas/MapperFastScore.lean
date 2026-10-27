import MapperGapless
import MapperWalk2

/-!
Window penalties for the scoring (0, −4, −6, −2) and `T = −12`, list level.

The penalty of a read `xs` against a window `ys` is minus the optimal score
when that is `≥ −12`, else `13` (`penL`).

* (a) a walk scoring `≥ −12` has at most one gap run, of length `≤ 3`, and it
  is `|ys| − |xs|` (or `|xs| − |ys|`) long;
* (b) same length: `penL = 4·hamming` when `hamming ≤ 3`, else `13` (`penL_same`);
* (c) one gap of length `L ∈ 1..3`: `penL = 6 + 2L + 4·M` when that is `≤ 12`,
  else `13`, where `M` is the fewest mismatches over the gap positions, prefix
  on the start diagonal and suffix on the end one (`penL_ins`, `penL_del`);
* lengths differing by `≥ 4`: `penL = 13` (`penL_far`).
-/

namespace MapSpec

open AlignmentSpec

/-- The default scoring: match 0, mismatch −4, a gap of length `L` costs `6 + 2L`. -/
def sc0 : Scoring := ⟨0, -4, -6, -2⟩

theorem valid_sc0 : ValidScoring sc0 := by
  unfold ValidScoring sc0; decide

/-- Penalty of an optional score: `−s` when `−12 ≤ s`, else `13`. -/
def penOf : Option Int → Nat
  | some s => if -12 ≤ s then (-s).toNat else 13
  | none => 13

/-- Penalty of the read `xs` against the window `ys`. -/
def penL (xs ys : List Char) : Nat := penOf ((getBestAlignment sc0 xs ys).map (·.2))

/-- Least of `f 0, …, f k`. -/
def minUpTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | k + 1 => min (minUpTo f k) (f (k + 1))

theorem minUpTo_le (f : Nat → Nat) (k i : Nat) (h : i ≤ k) : minUpTo f k ≤ f i := by
  induction k with
  | zero => rw [show i = 0 by omega]; exact Nat.le_refl _
  | succ k ih =>
    simp only [minUpTo]
    by_cases hi : i = k + 1
    · subst hi; exact Nat.min_le_right _ _
    · exact Nat.le_trans (Nat.min_le_left _ _) (ih (by omega))

theorem minUpTo_mem (f : Nat → Nat) (k : Nat) : ∃ i, i ≤ k ∧ minUpTo f k = f i := by
  induction k with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    obtain ⟨i, hi, he⟩ := ih
    simp only [minUpTo]
    by_cases h : minUpTo f k ≤ f (k + 1)
    · exact ⟨i, by omega, by rw [Nat.min_eq_left h, he]⟩
    · exact ⟨k + 1, Nat.le_refl _, Nat.min_eq_right (by omega)⟩

/-- Mismatches with an insertion of `L` letters after read letter `i`. -/
def misIns (xs ys : List Char) (L i : Nat) : Nat :=
  hamming (xs.take i) (ys.take i) + hamming (xs.drop i) (ys.drop (i + L))

/-- Mismatches with read letters `i ..< i+L` deleted. -/
def misDel (xs ys : List Char) (L i : Nat) : Nat :=
  hamming (xs.take i) (ys.take i) + hamming (xs.drop (i + L)) (ys.drop i)

/-! ## Walk shapes -/

theorem cnt_eq_zero (s : Step) (path : List Step) (h : cnt s path = 0) : s ∉ path := by
  induction path with
  | nil => simp
  | cons t rest ih =>
    simp only [cnt] at h
    simp only [List.mem_cons, not_or]
    by_cases ht : t = s
    · simp [ht] at h
    · simp [ht] at h; exact ⟨fun e => ht e.symm, ih h⟩

theorem runs_zero_all (s : Step) (path : List Step) (prev : Option Step) (hp : prev ≠ some s)
    (hall : ∀ x ∈ path, x = .diag ∨ x = s) (h : runs s path prev = 0) :
    path = List.replicate path.length .diag := by
  apply List.eq_replicate_of_mem
  intro x hx
  rcases hall x hx with h1 | h1
  · exact h1
  · subst h1
    have hc : 0 < cnt x path := by
      clear hall h hp
      induction path with
      | nil => simp at hx
      | cons t rest ih =>
        simp only [cnt]
        rcases List.mem_cons.mp hx with h2 | h2
        · subst h2; simp; omega
        · have := ih h2; omega
    have := runs_pos x path prev hp hc
    omega

theorem shape_cont (s : Step) (hsd : s ≠ .diag) (path : List Step)
    (hall : ∀ x ∈ path, x = .diag ∨ x = s) (h : runs s path (some s) = 0) :
    ∃ k j, path = List.replicate k s ++ List.replicate j .diag := by
  induction path with
  | nil => exact ⟨0, 0, rfl⟩
  | cons t rest ih =>
    have hr : ∀ x ∈ rest, x = .diag ∨ x = s := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    rcases hall t (List.mem_cons_self) with ht | ht
    · subst ht
      simp only [runs] at h
      have h0 : runs s rest (some .diag) = 0 := by
        have : ¬(Step.diag = s ∧ some s ≠ some s) := by simp
        simp [this] at h; exact h
      have := runs_zero_all s rest (some .diag) (by intro e; cases e; exact hsd rfl) hr h0
      exact ⟨0, rest.length + 1, by
        rw [List.replicate_zero, List.nil_append, List.replicate_succ, ← this]⟩
    · subst ht
      simp only [runs] at h
      have h0 : runs t rest (some t) = 0 := by simpa using h
      obtain ⟨k, j, hkj⟩ := ih hr h0
      exact ⟨k + 1, j, by rw [hkj]; simp [List.replicate_succ]⟩

/-- A walk over `diag` and one gap kind `s` with exactly one run of `s` is
`diag^i s^l diag^j`. -/
theorem shape_one_run (s : Step) (hsd : s ≠ .diag) (path : List Step) (prev : Option Step)
    (hp : prev ≠ some s) (hall : ∀ x ∈ path, x = .diag ∨ x = s) (h : runs s path prev = 1) :
    ∃ i l j, 0 < l ∧ path = List.replicate i .diag ++ List.replicate l s ++ List.replicate j .diag := by
  induction path generalizing prev with
  | nil => simp [runs] at h
  | cons t rest ih =>
    have hr : ∀ x ∈ rest, x = .diag ∨ x = s := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    rcases hall t (List.mem_cons_self) with ht | ht
    · subst ht
      simp only [runs] at h
      have h0 : runs s rest (some .diag) = 1 := by
        have : ¬(Step.diag = s ∧ prev ≠ some s) := by intro e; exact hsd e.1.symm
        simp [this] at h; exact h
      obtain ⟨i, l, j, hl, he⟩ := ih (some .diag) (by intro e; cases e; exact hsd rfl) hr h0
      exact ⟨i + 1, l, j, hl, by rw [he]; simp [List.replicate_succ]⟩
    · subst ht
      simp only [runs] at h
      have h0 : runs t rest (some t) = 0 := by simp [hp] at h; omega
      obtain ⟨k, j, hkj⟩ := shape_cont t hsd rest hr h0
      exact ⟨0, k + 1, j, by omega, by rw [hkj]; simp [List.replicate_succ]⟩

theorem not_mem_iff_all (path : List Step) (h : Step.gapY ∉ path) : ∀ x ∈ path, x = .diag ∨ x = .gapX := by
  intro x hx; cases x <;> simp_all

theorem not_mem_iff_all' (path : List Step) (h : Step.gapX ∉ path) : ∀ x ∈ path, x = .diag ∨ x = .gapY := by
  intro x hx; cases x <;> simp_all

/-! ## Scores of the shapes -/

theorem score_diags (i : Nat) (rest : List Step) (xs ys : List Char) (prev : Option Step)
    (hx : i ≤ xs.length) (hy : i ≤ ys.length) :
    scoreWalk sc0 (List.replicate i .diag ++ rest) xs ys prev =
      -4 * (hamming (xs.take i) (ys.take i) : Int) +
        scoreWalk sc0 rest (xs.drop i) (ys.drop i) (if i = 0 then prev else some .diag) := by
  induction i generalizing xs ys prev with
  | zero => simp [hamming]
  | succ i ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        simp only [List.replicate_succ, List.cons_append, List.take_succ_cons, List.drop_succ_cons]
        simp only [List.length_cons] at hx hy
        rw [scoreWalk, ih xs ys (some .diag) (by omega) (by omega)]
        simp only [hamming, sc0, Nat.add_one_ne_zero, if_false]
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy]; omega

theorem score_gapX_cont (l : Nat) (rest : List Step) (xs ys : List Char) (hy : l ≤ ys.length) :
    scoreWalk sc0 (List.replicate l .gapX ++ rest) xs ys (some .gapX) =
      -2 * (l : Int) + scoreWalk sc0 rest xs (ys.drop l) (some .gapX) := by
  induction l generalizing ys with
  | zero => simp
  | succ l ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
      simp only [List.length_cons] at hy
      have := ih ys (by omega)
      cases xs <;> (simp only [scoreWalk, if_true]; rw [this]; simp only [sc0]; push_cast; omega)

theorem score_gapX (l : Nat) (rest : List Step) (xs ys : List Char) (prev : Option Step)
    (hp : prev ≠ some .gapX) (hl : 0 < l) (hy : l ≤ ys.length) :
    scoreWalk sc0 (List.replicate l .gapX ++ rest) xs ys prev =
      -(6 + 2 * (l : Int)) + scoreWalk sc0 rest xs (ys.drop l) (some .gapX) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  cases ys with
  | nil => simp at hy
  | cons y ys =>
    simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
    simp only [List.length_cons] at hy
    have := score_gapX_cont m rest xs ys (by omega)
    cases xs <;> (simp only [scoreWalk, if_neg hp]; rw [this]; simp only [sc0]; push_cast; omega)

theorem score_gapY_cont (l : Nat) (rest : List Step) (xs ys : List Char) (hx : l ≤ xs.length) :
    scoreWalk sc0 (List.replicate l .gapY ++ rest) xs ys (some .gapY) =
      -2 * (l : Int) + scoreWalk sc0 rest (xs.drop l) ys (some .gapY) := by
  induction l generalizing xs with
  | zero => simp
  | succ l ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
      simp only [List.length_cons] at hx
      have := ih xs (by omega)
      cases ys <;> (simp only [scoreWalk, if_true]; rw [this]; simp only [sc0]; push_cast; omega)

theorem score_gapY (l : Nat) (rest : List Step) (xs ys : List Char) (prev : Option Step)
    (hp : prev ≠ some .gapY) (hl : 0 < l) (hx : l ≤ xs.length) :
    scoreWalk sc0 (List.replicate l .gapY ++ rest) xs ys prev =
      -(6 + 2 * (l : Int)) + scoreWalk sc0 rest (xs.drop l) ys (some .gapY) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  cases xs with
  | nil => simp at hx
  | cons x xs =>
    simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
    simp only [List.length_cons] at hx
    have := score_gapY_cont m rest xs ys (by omega)
    cases ys <;> (simp only [scoreWalk, if_neg hp]; rw [this]; simp only [sc0]; push_cast; omega)

theorem score_diags_all (xs ys : List Char) (prev : Option Step) (h : xs.length = ys.length) (j : Nat)
    (hj : j = xs.length) :
    scoreWalk sc0 (List.replicate j .diag) xs ys prev = -4 * (hamming xs ys : Int) := by
  subst hj
  rw [scoreWalk_diags_counts sc0 xs ys prev h]
  simp [sc0]

/-- Score of `diag^i gapX^L diag^j`. -/
theorem score_ins (xs ys : List Char) (i L j : Nat) (hL : 0 < L) (hx : i + j = xs.length)
    (hy : i + L + j = ys.length) :
    walkScore sc0 xs ys (List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) =
      -(6 + 2 * (L : Int)) - 4 * (misIns xs ys L i : Int) := by
  unfold walkScore misIns
  rw [List.append_assoc, score_diags i _ xs ys none (by omega) (by omega),
    score_gapX L _ _ _ _ (by split <;> simp) hL (by simp; omega),
    score_diags_all _ _ _ (by simp; omega) j (by simp; omega)]
  rw [List.drop_drop]
  push_cast; omega

/-- Score of `diag^i gapY^L diag^j`. -/
theorem score_del (xs ys : List Char) (i L j : Nat) (hL : 0 < L) (hx : i + L + j = xs.length)
    (hy : i + j = ys.length) :
    walkScore sc0 xs ys (List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) =
      -(6 + 2 * (L : Int)) - 4 * (misDel xs ys L i : Int) := by
  unfold walkScore misDel
  rw [List.append_assoc, score_diags i _ xs ys none (by omega) (by omega),
    score_gapY L _ _ _ _ (by split <;> simp) hL (by simp; omega),
    score_diags_all _ _ _ (by simp; omega) j (by simp; omega)]
  rw [List.drop_drop]
  push_cast; omega

theorem walk_shape (i L j : Nat) (s : Step) :
    ((List.replicate i Step.diag ++ List.replicate L s ++ List.replicate j Step.diag).map xConsumed).sum
      = i + L * xConsumed s + j ∧
    ((List.replicate i Step.diag ++ List.replicate L s ++ List.replicate j Step.diag).map yConsumed).sum
      = i + L * yConsumed s + j := by
  cases s <;> simp [xConsumed, yConsumed] <;> omega

theorem cnt_replicate (s t : Step) (l : Nat) : cnt s (List.replicate l t) = if t = s then l else 0 := by
  induction l with
  | zero => simp [cnt]
  | succ l ih => rw [List.replicate_succ, cnt, ih]; split <;> omega

theorem cnt_shape (s t : Step) (hs : s ≠ .diag) (i l j : Nat) :
    cnt s (List.replicate i .diag ++ List.replicate l t ++ List.replicate j .diag) = if t = s then l else 0 := by
  rw [cnt_append, cnt_append, cnt_replicate, cnt_replicate, cnt_replicate]
  have : (Step.diag = s) = False := by simp; exact fun e => hs e.symm
  simp only [this, if_false]; omega

/-! ## (a): a walk scoring `≥ −12` -/

/-- Mismatches, runs and columns of a walk scoring `≥ −12`. -/
theorem counts_of_score (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -12 ≤ walkScore sc0 xs ys path) :
    4 * mism path xs ys + 6 * runs .gapX path none + 6 * runs .gapY path none +
      2 * cnt .gapX path + 2 * cnt .gapY path ≤ 12 ∧
    (0 < cnt .gapX path → 0 < runs .gapX path none) ∧
    (0 < cnt .gapY path → 0 < runs .gapY path none) ∧
    runs .gapX path none ≤ cnt .gapX path ∧ runs .gapY path none ≤ cnt .gapY path ∧
    (ys.length : Int) - xs.length = (cnt .gapX path : Int) - cnt .gapY path := by
  obtain ⟨hx, hy⟩ := hw
  have h := scoreWalk_le_counts sc0 valid_sc0 path xs ys none hx hy
  unfold walkScore at hs
  simp only [sc0] at h hs
  refine ⟨by omega, runs_pos _ _ _ (by simp), runs_pos _ _ _ (by simp), runs_le_cnt _ _ _,
    runs_le_cnt _ _ _, ?_⟩
  have := sum_diff_eq path
  rw [hx, hy] at this
  exact this

/-- (a) As shapes: a walk scoring `≥ −12` is gapless, or one gap run of length `≤ 3`. -/
theorem shape_of_score (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -12 ≤ walkScore sc0 xs ys path) :
    path = List.replicate xs.length .diag ∨
    (∃ i L j, 0 < L ∧ L ≤ 3 ∧ path = List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) ∨
    (∃ i L j, 0 < L ∧ L ≤ 3 ∧ path = List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := counts_of_score path xs ys hw hs
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

/-! ## (b), (c): penalties -/

theorem best_facts (xs ys : List Char) : ∃ path bs, getBestAlignment sc0 xs ys = some (path, bs) ∧
    IsMonotoneWalk path xs ys ∧ walkScore sc0 xs ys path = bs ∧
    ∀ c, IsMonotoneWalk c xs ys → walkScore sc0 xs ys c ≤ bs := by
  obtain ⟨⟨path, bs⟩, h⟩ := getBestAlignment_returns_some sc0 xs ys
  obtain ⟨hw, hs⟩ := getBestAlignment_returns_a_valid_walk sc0 xs ys path bs h
  exact ⟨path, bs, h, hw, hs, fun c hc => getBestAlignment_returns_a_maximum_score sc0 xs ys path bs c h hc⟩

theorem penL_of (xs ys : List Char) (path : List Step) (bs : Int)
    (h : getBestAlignment sc0 xs ys = some (path, bs)) :
    penL xs ys = if -12 ≤ bs then (-bs).toNat else 13 := by
  simp [penL, h, penOf]

theorem lengths_ins {xs ys : List Char} {i L j : Nat}
    (hw : IsMonotoneWalk (List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) xs ys) :
    i + j = xs.length ∧ i + L + j = ys.length := by
  obtain ⟨hx, hy⟩ := hw
  have := walk_shape i L j .gapX
  simp only [xConsumed, yConsumed] at this
  omega

theorem lengths_del {xs ys : List Char} {i L j : Nat}
    (hw : IsMonotoneWalk (List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) xs ys) :
    i + L + j = xs.length ∧ i + j = ys.length := by
  obtain ⟨hx, hy⟩ := hw
  have := walk_shape i L j .gapY
  simp only [xConsumed, yConsumed] at this
  omega

theorem walk_ins (xs ys : List Char) (i L j : Nat) (hx : i + j = xs.length) (hy : i + L + j = ys.length) :
    IsMonotoneWalk (List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) xs ys := by
  have := walk_shape i L j .gapX
  simp only [xConsumed, yConsumed] at this
  exact ⟨by omega, by omega⟩

theorem walk_del (xs ys : List Char) (i L j : Nat) (hx : i + L + j = xs.length) (hy : i + j = ys.length) :
    IsMonotoneWalk (List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) xs ys := by
  have := walk_shape i L j .gapY
  simp only [xConsumed, yConsumed] at this
  exact ⟨by omega, by omega⟩

theorem length_of_diags {xs ys : List Char} {path : List Step} (hw : IsMonotoneWalk path xs ys)
    (h : path = List.replicate xs.length .diag) : xs.length = ys.length := by
  obtain ⟨-, hy⟩ := hw
  rw [h] at hy
  simp [yConsumed] at hy
  omega

/-- **(b) Same length.**  Penalty `4·hamming` when at most 3 mismatches, else 13. -/
theorem penL_same (xs ys : List Char) (hl : xs.length = ys.length) :
    penL xs ys = if hamming xs ys ≤ 3 then 4 * hamming xs ys else 13 := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penL_of xs ys path bs hb]
  have hlo := hmax _ (diags_isMonotoneWalk xs ys hl)
  rw [walkScore, score_diags_all xs ys none hl _ rfl] at hlo
  have hup : -12 ≤ bs → bs = -4 * (hamming xs ys : Int) := by
    intro h12
    rcases shape_of_score path xs ys hw (by omega) with he | ⟨i, L, j, hL, -, he⟩ | ⟨i, L, j, hL, -, he⟩
    · rw [← hs, he, walkScore, score_diags_all xs ys none hl _ rfl]
    · have := lengths_ins (he ▸ hw); omega
    · have := lengths_del (he ▸ hw); omega
  by_cases hh : hamming xs ys ≤ 3
  · rw [if_pos hh, if_pos (by omega), hup (by omega)]; omega
  · rw [if_neg hh, if_neg]; intro h; have := hup h; omega

/-- **(c) Insertion.**  `|ys| = |xs| + L`, `1 ≤ L ≤ 3`. -/
theorem penL_ins (xs ys : List Char) (L : Nat) (hl : ys.length = xs.length + L) (h1 : 1 ≤ L) (h3 : L ≤ 3) :
    penL xs ys = (if 6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length ≤ 12
      then 6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length else 13) := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penL_of xs ys path bs hb]
  obtain ⟨i0, hi0, hM⟩ := minUpTo_mem (misIns xs ys L) xs.length
  have hlo := hmax _ (walk_ins xs ys i0 L (xs.length - i0) (by omega) (by omega))
  rw [score_ins xs ys i0 L (xs.length - i0) (by omega) (by omega) (by omega), ← hM] at hlo
  have hup : -12 ≤ bs → bs = -(6 + 2 * (L : Int)) - 4 * (minUpTo (misIns xs ys L) xs.length : Int) := by
    intro h12
    rcases shape_of_score path xs ys hw (by omega) with he | ⟨i, l, j, hL, -, he⟩ | ⟨i, l, j, hL, -, he⟩
    · have := length_of_diags hw he; omega
    · have hlen := lengths_ins (he ▸ hw)
      have hlL : l = L := by omega
      subst hlL
      have hle := minUpTo_le (misIns xs ys l) xs.length i (by omega)
      rw [← hs, he, score_ins xs ys i l j hL hlen.1 hlen.2] at *
      omega
    · have := lengths_del (he ▸ hw); omega
  by_cases hh : 6 + 2 * L + 4 * minUpTo (misIns xs ys L) xs.length ≤ 12
  · rw [if_pos hh, if_pos (by omega), hup (by omega)]; omega
  · rw [if_neg hh, if_neg]; intro h; have := hup h; omega

/-- **(c) Deletion.**  `|xs| = |ys| + L`, `1 ≤ L ≤ 3`. -/
theorem penL_del (xs ys : List Char) (L : Nat) (hl : xs.length = ys.length + L) (h1 : 1 ≤ L) (h3 : L ≤ 3) :
    penL xs ys = (if 6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length ≤ 12
      then 6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length else 13) := by
  obtain ⟨path, bs, hb, hw, hs, hmax⟩ := best_facts xs ys
  rw [penL_of xs ys path bs hb]
  obtain ⟨i0, hi0, hM⟩ := minUpTo_mem (misDel xs ys L) ys.length
  have hlo := hmax _ (walk_del xs ys i0 L (ys.length - i0) (by omega) (by omega))
  rw [score_del xs ys i0 L (ys.length - i0) (by omega) (by omega) (by omega), ← hM] at hlo
  have hup : -12 ≤ bs → bs = -(6 + 2 * (L : Int)) - 4 * (minUpTo (misDel xs ys L) ys.length : Int) := by
    intro h12
    rcases shape_of_score path xs ys hw (by omega) with he | ⟨i, l, j, hL, -, he⟩ | ⟨i, l, j, hL, -, he⟩
    · have := length_of_diags hw he; omega
    · have := lengths_ins (he ▸ hw); omega
    · have hlen := lengths_del (he ▸ hw)
      have hlL : l = L := by omega
      subst hlL
      have hle := minUpTo_le (misDel xs ys l) ys.length i (by omega)
      rw [← hs, he, score_del xs ys i l j hL hlen.1 hlen.2] at *
      omega
  by_cases hh : 6 + 2 * L + 4 * minUpTo (misDel xs ys L) ys.length ≤ 12
  · rw [if_pos hh, if_pos (by omega), hup (by omega)]; omega
  · rw [if_neg hh, if_neg]; intro h; have := hup h; omega

/-- Lengths differing by 4 or more: penalty 13. -/
theorem penL_far (xs ys : List Char) (hl : xs.length + 4 ≤ ys.length ∨ ys.length + 4 ≤ xs.length) :
    penL xs ys = 13 := by
  obtain ⟨path, bs, hb, hw, hs, -⟩ := best_facts xs ys
  rw [penL_of xs ys path bs hb]
  rw [if_neg]
  intro h12
  rcases shape_of_score path xs ys hw (by omega) with he | ⟨i, l, j, hL, hL3, he⟩ | ⟨i, l, j, hL, hL3, he⟩
  · have := length_of_diags hw he; omega
  · have := lengths_ins (he ▸ hw); omega
  · have := lengths_del (he ▸ hw); omega

end MapSpec

#print axioms MapSpec.penL_same
#print axioms MapSpec.penL_ins
#print axioms MapSpec.penL_del
#print axioms MapSpec.penL_far
