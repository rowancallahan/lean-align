import MapperSeedsAmong

/-! Event-based pigeonhole.  `errReps` charges every inserted read letter (a
`gapY` column) as a separate spoiling coordinate, so a walk within penalty `P`
may spoil `(P − 6) / 2` seeds.  Here a `gapY` run is charged once per seed it
reaches: its first column, and each column at a seed boundary (`i % l = 0`,
`l` the seed length).  A seed with none of these coordinates has none of
`errReps`' (`errRepsL_clean`), and for `l ≥ 2` the coordinates number at most
`(−T) / min(M, O, 2E)` (`seedBoundE`; `P / 4` for the default scoring). -/

namespace MapSpec

open AlignmentSpec

/-- `errReps` with a `gapY` run charged at its start and at each seed boundary. -/
def errRepsL (l : Nat) : List Step → List Char → List Char → Nat → Option Step → List Nat
  | [], _, _, _, _ => []
  | .diag :: rest, x :: xs, y :: ys, i, _ =>
      (if x = y then [] else [2*i+1]) ++ errRepsL l rest xs ys (i+1) (some .diag)
  | .gapX :: rest, xs, _ :: ys, i, prev =>
      (if prev = some .gapX then [] else [2*i]) ++ errRepsL l rest xs ys i (some .gapX)
  | .gapY :: rest, _ :: xs, ys, i, prev =>
      (if prev = some .gapY ∧ i % l ≠ 0 then [] else [2*i+1]) ++ errRepsL l rest xs ys (i+1) (some .gapY)
  | _, _, _, _, _ => []

/-- The seeds' error bound with each error event charged once per seed. -/
def seedBoundE (sc : Scoring) (T : Int) : Nat :=
  ((-T) / min (-sc.mismatchScore) (min (-sc.gapOpen) (-2 * sc.gapExtend))).toNat

example : seedBoundE ⟨0, -4, -6, -2⟩ (-16) = 4 := by decide
example : seedBoundE ⟨0, -4, -6, -2⟩ (-39) = 9 := by decide

/-- A block `[a, a + m)` starting at a seed boundary with no `errRepsL`
coordinate inside has no `errReps` coordinate inside. -/
theorem errRepsL_clean (l a m : Nat) (hal : a % l = 0) (path : List Step) :
    ∀ (xs ys : List Char) (i : Nat) (prev : Option Step),
      (prev = some .gapY → ¬(a + 1 ≤ i ∧ i ≤ a + m)) →
      (∀ c ∈ errRepsL l path xs ys i prev, ¬(2 * a < c ∧ c < 2 * (a + m))) →
      ∀ c ∈ errReps path xs ys i prev, ¬(2 * a < c ∧ c < 2 * (a + m)) := by
  induction path with
  | nil => intro xs ys i prev _ _ c hc; simp [errReps] at hc
  | cons s rest ih =>
    intro xs ys i prev hp h c hc
    cases s with
    | diag =>
      cases xs with
      | nil => simp [errReps] at hc
      | cons x xs =>
        cases ys with
        | nil => simp [errReps] at hc
        | cons y ys =>
          simp only [errReps, List.mem_append] at hc
          simp only [errRepsL, List.mem_append] at h
          rcases hc with hc | hc
          · exact h c (Or.inl hc)
          · exact ih xs ys (i+1) (some .diag) (by simp) (fun c hc => h c (Or.inr hc)) c hc
    | gapX =>
      cases ys with
      | nil => cases xs <;> simp [errReps] at hc
      | cons y ys =>
        simp only [errReps, List.mem_append] at hc
        simp only [errRepsL, List.mem_append] at h
        rcases hc with hc | hc
        · exact h c (Or.inl hc)
        · exact ih xs ys i (some .gapX) (by simp) (fun c hc => h c (Or.inr hc)) c hc
    | gapY =>
      cases xs with
      | nil => cases ys <;> simp [errReps] at hc
      | cons x xs =>
        simp only [errReps, List.mem_cons] at hc
        simp only [errRepsL, List.mem_append] at h
        -- this column's letter `i` is outside the block
        have hi : ¬(a ≤ i ∧ i < a + m) := by
          intro ⟨h1, h2⟩
          by_cases hk : prev = some .gapY ∧ i % l ≠ 0
          · have : i ≠ a := by intro e; subst e; exact hk.2 hal
            exact hp hk.1 ⟨by omega, by omega⟩
          · exact h (2*i+1) (Or.inl (by simp [hk])) ⟨by omega, by omega⟩
        rcases hc with rfl | hc
        · omega
        · exact ih xs ys (i+1) (some .gapY) (fun _ => by omega) (fun c hc => h c (Or.inr hc)) c hc

/-- Count: with seeds of `l ≥ 2` letters, twice the coordinates are at most twice
the mismatches and gap runs plus the `gapY` columns (plus one when the next
column would open a new seed inside a `gapY` run). -/
theorem errRepsL_length_le (l : Nat) (hl : 2 ≤ l) (path : List Step) :
    ∀ (xs ys : List Char) (i : Nat) (prev : Option Step),
      2 * (errRepsL l path xs ys i prev).length ≤
        2 * mism path xs ys + 2 * runs .gapX path prev + 2 * runs .gapY path prev + cnt .gapY path +
          (if prev = some .gapY ∧ i % l = 0 then 1 else 0) := by
  induction path with
  | nil => intro xs ys i prev; simp [errRepsL]
  | cons s rest ih =>
    intro xs ys i prev
    cases s with
    | diag =>
      cases xs with
      | nil => simp [errRepsL]
      | cons x xs =>
        cases ys with
        | nil => simp [errRepsL]
        | cons y ys =>
          have := ih xs ys (i+1) (some .diag)
          simp only [errRepsL, mism, runs, cnt, List.length_append] at this ⊢
          by_cases hxy : x = y <;> simp [hxy] at this ⊢ <;> omega
    | gapX =>
      cases ys with
      | nil => cases xs <;> simp [errRepsL]
      | cons y ys =>
        have := ih xs ys i (some .gapX)
        cases xs with
        | nil =>
          simp only [errRepsL, mism, runs, cnt, List.length_append] at this ⊢
          by_cases hp : prev = some .gapX <;> simp [hp] at this ⊢ <;> (try split) <;> omega
        | cons x xs =>
          simp only [errRepsL, mism, runs, cnt, List.length_append] at this ⊢
          by_cases hp : prev = some .gapX <;> simp [hp] at this ⊢ <;> (try split) <;> omega
    | gapY =>
      cases xs with
      | nil => cases ys <;> simp [errRepsL]
      | cons x xs =>
        have := ih xs ys (i+1) (some .gapY)
        have hmod : i % l = 0 → (i + 1) % l ≠ 0 := by
          intro h0 h1
          rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.one_mod_eq_one.2 (by omega)] at h1
          omega
        simp only [errRepsL, mism, runs, cnt, List.length_append, true_and] at this ⊢
        have hf : (if (i + 1) % l = 0 then 1 else 0) ≤ 1 := by split <;> omega
        by_cases hp : prev = some .gapY
        · by_cases hi : i % l = 0
          · rw [if_neg (hmod hi)] at this
            simp [hp, hi]; omega
          · simp [hp, hi]; omega
        · simp [hp]; omega

theorem le_toNat_divE (n : Nat) (b c : Int) (hc : 0 < c) (h : c * n ≤ b) : n ≤ (b / c).toNat := by
  have := Int.le_ediv_of_mul_le hc (by rw [Int.mul_comm]; exact h)
  omega

/-- The cost side: `2N ≤ 2 mis + 2 xr + 2 yr + yc` coordinates fit the budget. -/
theorem cost_boundE (M O E T : Int) (hM : 0 < M) (hO : 0 < O) (hE : 0 < E)
    (mis xr yr xc yc N : Nat) (hN : 2 * N ≤ 2 * mis + 2 * xr + 2 * yr + yc)
    (hc : M * mis + O * xr + O * yr + E * xc + E * yc ≤ -T) :
    N ≤ ((-T) / min M (min O (2 * E))).toNat := by
  generalize hC : min M (min O (2 * E)) = C
  have hCM : C ≤ M := by rw [← hC]; exact Int.min_le_left _ _
  have hCO : C ≤ O := by rw [← hC]; exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
  have hCE : C ≤ 2 * E := by rw [← hC]; exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
  have hC0 : 0 < C := by rw [← hC]; omega
  have a1 : C * mis ≤ M * mis := Int.mul_le_mul_of_nonneg_right hCM (Int.natCast_nonneg _)
  have a2 : C * xr ≤ O * xr := Int.mul_le_mul_of_nonneg_right hCO (Int.natCast_nonneg _)
  have a3 : C * yr ≤ O * yr := Int.mul_le_mul_of_nonneg_right hCO (Int.natCast_nonneg _)
  have a4 : C * yc ≤ (2 * E) * yc := Int.mul_le_mul_of_nonneg_right hCE (Int.natCast_nonneg _)
  have a5 : (0 : Int) ≤ E * xc := Int.mul_nonneg (Int.le_of_lt hE) (Int.natCast_nonneg _)
  have a6 : C * (2 * N) ≤ C * (2 * mis + 2 * xr + 2 * yr + yc) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (Int.le_of_lt hC0)
  rw [Int.mul_assoc] at a4
  push_cast at a6
  simp only [Int.mul_add, Int.mul_left_comm C 2] at a6
  exact le_toNat_divE N (-T) C hC0 (by omega)

/-- **Clean seed among chosen seeds, events counted.**  As
`exists_clean_seed_among`, with seeds of at least two letters and the bound
`seedBoundE sc T` (each mismatch or gap run spoils one seed, a `gapY` run one
more per seed boundary it crosses). -/
theorem exists_clean_seed_amongE (sc : Scoring) (hv : ValidScoring sc) (hO : sc.gapOpen < 0) (T : Int)
    (xs ys : List Char) (path : List Step)
    (hw : IsMonotoneWalk path xs ys) (hs : T ≤ walkScore sc xs ys path)
    (k : Nat) (hl2 : 2 ≤ xs.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBoundE sc T < J.length) :
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
  generalize hl : xs.length / (k + 1) = l at hl2 ⊢
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
  have hNL := errRepsL_length_le l hl2 path xs ys 0 none
  simp only [reduceCtorEq, false_and, if_false, Nat.add_zero] at hNL
  have hbE := cost_boundE (-sc.mismatchScore) (-sc.gapOpen) (-sc.gapExtend) T
    (by omega) (by omega) (by omega)
    (mism path xs ys) (runs .gapX path none) (runs .gapY path none) (cnt .gapX path) (cnt .gapY path)
    (errRepsL l path xs ys 0 none).length hNL
    (by simp only [Int.neg_mul]; omega)
  have e2 : -T + sc.gapOpen = -T - -sc.gapOpen := by omega
  have e3 : -T + 2 * sc.gapOpen = -T - 2 * -sc.gapOpen := by omega
  have e4 : -2 * sc.gapExtend = 2 * -sc.gapExtend := by omega
  have hE : (errRepsL l path xs ys 0 none).length ≤ seedBoundE sc T := by
    unfold seedBoundE; rw [e4]; exact hbE
  have hG : cnt .gapX path + cnt .gapY path ≤ gapBound sc T := by
    unfold gapBound; rw [e2]; exact hb.2.1
  have hG2 : 0 < cnt .gapX path → 0 < cnt .gapY path →
      cnt .gapX path + cnt .gapY path ≤ gapBound2 sc T := by
    unfold gapBound2; rw [e3]; exact hb.2.2
  clear hb hbE hcost hN hNL
  have hlk : (k + 1) * l ≤ xs.length := by
    rw [← hl, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hex : ∃ j ∈ J, ∀ c ∈ errRepsL l path xs ys 0 none,
      ¬(2 * (j * l) < c ∧ c < 2 * (j * l + l)) := by
    apply Classical.byContradiction
    intro hno
    have hsub : J ⊆ (errRepsL l path xs ys 0 none).map (fun c => c / (2 * l)) := by
      intro j hj
      have : ∃ c ∈ errRepsL l path xs ys 0 none, 2 * (j * l) < c ∧ c < 2 * (j * l + l) := by
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
  obtain ⟨j, hjJ, hcL⟩ := hex
  have hc : ∀ c ∈ errReps path xs ys 0 none, ¬(2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l)) := by
    have := errRepsL_clean l (j * l) l (Nat.mul_mod_left _ _) path xs ys 0 none (by simp) hcL
    simpa using this
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
