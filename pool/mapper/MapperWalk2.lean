import MapperWalk

/-! Sharper bounds for the seed-and-index mapper, using the affine gap cost.

* Seeds: each mismatch, each gap-in-x run (one coordinate between read
  letters) and each gap-in-y column spoils at most one seed.  A walk scoring
  at least `T` has at most `seedBound sc T` of them.
* Window shape: if seed `j` is clean and sits at `o` in the window, the start
  shift `s = o - j*q` and end shift `t = (|ys| - o) - (|xs| - j*q)` are
  (gap-in-x columns) − (gap-in-y columns) before and after the seed, so
  `|s| + |t| ≤ gapBound sc T`, and `s`, `t` have the same sign unless
  `|s| + |t| ≤ gapBound2 sc T` (both kinds of gap occur). -/

namespace MapSpec

open AlignmentSpec

/-- Most spoiling coordinates: first term with no gap in y, second with one. -/
def seedBound (sc : Scoring) (T : Int) : Nat :=
  max ((-T) / min (-sc.mismatchScore) (-(sc.gapOpen + sc.gapExtend))).toNat
      ((-T + sc.gapOpen) / min (-sc.mismatchScore) (-sc.gapExtend)).toNat

/-- Most gap columns. -/
def gapBound (sc : Scoring) (T : Int) : Nat :=
  ((-T + sc.gapOpen) / (-sc.gapExtend)).toNat

/-- Most gap columns when both kinds of gap occur. -/
def gapBound2 (sc : Scoring) (T : Int) : Nat :=
  ((-T + 2 * sc.gapOpen) / (-sc.gapExtend)).toNat

/-- Default scoring (match 0, mismatch −4, gap 6 + 2L), `T = −12`: 4 seeds,
at most 3 gap columns, never both kinds. -/
example : seedBound ⟨0, -4, -6, -2⟩ (-12) = 3 := by decide
example : gapBound ⟨0, -4, -6, -2⟩ (-12) = 3 := by decide
example : gapBound2 ⟨0, -4, -6, -2⟩ (-12) = 0 := by decide

/-- Allowed (start shift, end shift) pairs. -/
def shapeOk (d d2 : Nat) (s t : Int) : Prop :=
  s.natAbs + t.natAbs ≤ d ∧ ((0 ≤ s ∧ 0 ≤ t) ∨ (s ≤ 0 ∧ t ≤ 0) ∨ s.natAbs + t.natAbs ≤ d2)

/-- Like `errCoords`, but a gap-in-x run gives one coordinate (its first column). -/
def errReps : List Step → List Char → List Char → Nat → Option Step → List Nat
  | [], _, _, _, _ => []
  | .diag :: rest, x :: xs, y :: ys, i, _ =>
      (if x = y then [] else [2*i+1]) ++ errReps rest xs ys (i+1) (some .diag)
  | .gapX :: rest, xs, _ :: ys, i, prev =>
      (if prev = some .gapX then [] else [2*i]) ++ errReps rest xs ys i (some .gapX)
  | .gapY :: rest, _ :: xs, ys, i, _ => (2*i+1) :: errReps rest xs ys (i+1) (some .gapY)
  | _, _, _, _, _ => []

def mism : List Step → List Char → List Char → Nat
  | .diag :: rest, x :: xs, y :: ys => (if x = y then 0 else 1) + mism rest xs ys
  | .gapX :: rest, xs, _ :: ys => mism rest xs ys
  | .gapY :: rest, _ :: xs, ys => mism rest xs ys
  | _, _, _ => 0

/-- Columns of kind `s`. -/
def cnt (s : Step) : List Step → Nat
  | [] => 0
  | t :: rest => (if t = s then 1 else 0) + cnt s rest

/-- Runs of kind `s` (columns of kind `s` whose previous column is not `s`). -/
def runs (s : Step) : List Step → Option Step → Nat
  | [], _ => 0
  | t :: rest, prev => (if t = s ∧ prev ≠ some s then 1 else 0) + runs s rest (some t)

theorem cnt_append (s : Step) (a b : List Step) : cnt s (a ++ b) = cnt s a + cnt s b := by
  induction a with
  | nil => simp [cnt]
  | cons t a ih => simp [cnt, ih]; omega

theorem runs_le_cnt (s : Step) (path : List Step) (prev : Option Step) :
    runs s path prev ≤ cnt s path := by
  induction path generalizing prev with
  | nil => simp [runs, cnt]
  | cons t rest ih =>
    have := ih (some t)
    simp only [runs, cnt]
    by_cases ht : t = s
    · subst ht; by_cases hp : prev = some t <;> simp [hp] <;> omega
    · simp [ht]; omega

theorem runs_pos (s : Step) (path : List Step) (prev : Option Step) (hp : prev ≠ some s)
    (h : 0 < cnt s path) : 0 < runs s path prev := by
  induction path generalizing prev with
  | nil => simp [cnt] at h
  | cons t rest ih =>
    simp only [runs, cnt] at h ⊢
    by_cases ht : t = s
    · simp [ht, hp]; omega
    · have := ih (some t) (by simpa using ht) (by simpa [ht] using h)
      omega

/-- `|ys| - |xs|` is (gap-in-x columns) − (gap-in-y columns). -/
theorem sum_diff_eq (path : List Step) :
    ((path.map yConsumed).sum : Int) - (path.map xConsumed).sum
      = (cnt .gapX path : Int) - cnt .gapY path := by
  induction path with
  | nil => simp [cnt]
  | cons t rest ih => cases t <;> simp [cnt, xConsumed, yConsumed] <;> omega

theorem errReps_length_le (path : List Step) (xs ys : List Char) (i : Nat) (prev : Option Step) :
    (errReps path xs ys i prev).length ≤ mism path xs ys + runs .gapX path prev + cnt .gapY path := by
  induction path generalizing xs ys i prev with
  | nil => simp [errReps]
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [errReps]
      | cons x xs =>
        cases ys with
        | nil => simp [errReps]
        | cons y ys =>
          have := ih xs ys (i+1) (some .diag)
          clear ih
          simp [errReps, mism, runs, cnt]
          split <;> simp <;> omega
    | gapX =>
      cases ys with
      | nil => cases xs <;> simp [errReps]
      | cons y ys =>
        have := ih xs ys i (some .gapX)
        clear ih
        cases xs <;> (simp [errReps, mism, runs, cnt]; split <;> simp <;> omega)
    | gapY =>
      cases xs with
      | nil => cases ys <;> simp [errReps]
      | cons x xs =>
        have := ih xs ys (i+1) (some .gapY)
        clear ih
        cases ys <;> (simp [errReps, mism, runs, cnt]; omega)

/-- The score of a walk is at most what its mismatches, gap runs and gap columns cost. -/
theorem scoreWalk_le_counts (sc : Scoring) (hv : ValidScoring sc)
    (path : List Step) (xs ys : List Char) (prev : Option Step)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length) :
    scoreWalk sc path xs ys prev ≤ sc.mismatchScore * mism path xs ys
      + sc.gapOpen * runs .gapX path prev + sc.gapOpen * runs .gapY path prev
      + sc.gapExtend * cnt .gapX path + sc.gapExtend * cnt .gapY path := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  induction path generalizing xs ys prev with
  | nil => simp [scoreWalk, mism, runs, cnt]
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          simp [xConsumed, yConsumed] at hx hy
          have := ih xs ys (some .diag) (by omega) (by omega)
          clear ih
          by_cases hxy : x = y
          · simp [scoreWalk, mism, runs, cnt, hxy]; omega
          · simp [scoreWalk, mism, runs, cnt, hxy, Int.mul_add]; omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        simp [xConsumed, yConsumed] at hx hy
        have := ih xs ys (some .gapX) (by omega) (by omega)
        clear ih
        by_cases hp : prev = some .gapX
        · cases xs <;> simp [scoreWalk, mism, runs, cnt, hp, Int.mul_add] <;> omega
        · cases xs <;> simp [scoreWalk, mism, runs, cnt, hp, Int.mul_add] <;> omega
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        simp [xConsumed, yConsumed] at hx hy
        have := ih xs ys (some .gapY) (by omega) (by omega)
        clear ih
        by_cases hp : prev = some .gapY
        · cases ys <;> simp [scoreWalk, mism, runs, cnt, hp, Int.mul_add] <;> omega
        · cases ys <;> simp [scoreWalk, mism, runs, cnt, hp, Int.mul_add] <;> omega

theorem le_toNat_div (n : Nat) (b c : Int) (hc : 0 < c) (h : c * n ≤ b) : n ≤ (b / c).toNat := by
  have := Int.le_ediv_of_mul_le hc (by rw [Int.mul_comm]; exact h)
  omega

theorem cost_bounds (M O E T : Int) (hM : 0 < M) (hO : 0 ≤ O) (hE : 0 < E)
    (mis xr yr xc yc N : Nat) (hN : N ≤ mis + xr + yc) (hxr : xr ≤ xc) (hyr : yr ≤ yc)
    (hxp : 0 < xc → 0 < xr) (hyp : 0 < yc → 0 < yr)
    (hc : M * mis + O * xr + O * yr + E * xc + E * yc ≤ -T) :
    N ≤ max ((-T) / min M (O + E)).toNat ((-T - O) / min M E).toNat ∧
    xc + yc ≤ ((-T - O) / E).toNat ∧
    (0 < xc → 0 < yc → xc + yc ≤ ((-T - 2 * O) / E).toNat) := by
  have pM : (0 : Int) ≤ M * mis := Int.mul_nonneg (Int.le_of_lt hM) (Int.natCast_nonneg _)
  have pOx : (0 : Int) ≤ O * xr := Int.mul_nonneg hO (Int.natCast_nonneg _)
  have pOy : (0 : Int) ≤ O * yr := Int.mul_nonneg hO (Int.natCast_nonneg _)
  have pEx : (0 : Int) ≤ E * xc := Int.mul_nonneg (Int.le_of_lt hE) (Int.natCast_nonneg _)
  have pEy : (0 : Int) ≤ E * yc := Int.mul_nonneg (Int.le_of_lt hE) (Int.natCast_nonneg _)
  -- `O * n ≥ O` once `n ≥ 1`
  have oge : ∀ n : Nat, 0 < n → O ≤ O * n := fun n hn => by
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ n by omega) hO
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · by_cases hy : yc = 0
    · have hyr0 : yr = 0 := by omega
      subst hy; subst hyr0
      have hc0 : 0 < min M (O + E) := by omega
      have a1 : min M (O + E) * mis ≤ M * mis :=
        Int.mul_le_mul_of_nonneg_right (Int.min_le_left _ _) (Int.natCast_nonneg _)
      have a2 : min M (O + E) * xr ≤ (O + E) * xr :=
        Int.mul_le_mul_of_nonneg_right (Int.min_le_right _ _) (Int.natCast_nonneg _)
      have a3 : E * xr ≤ E * xc := Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hE)
      have a4 : min M (O + E) * N ≤ min M (O + E) * ((mis : Int) + xr) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hc0)
      rw [Int.add_mul] at a2
      rw [Int.mul_add] at a4
      have := le_toNat_div N (-T) _ hc0 (by simp at hc; omega)
      omega
    · have hc0 : 0 < min M E := by omega
      have a1 : min M E * mis ≤ M * mis :=
        Int.mul_le_mul_of_nonneg_right (Int.min_le_left _ _) (Int.natCast_nonneg _)
      have a2 : min M E * xr ≤ E * xr :=
        Int.mul_le_mul_of_nonneg_right (Int.min_le_right _ _) (Int.natCast_nonneg _)
      have a2' : min M E * yc ≤ E * yc :=
        Int.mul_le_mul_of_nonneg_right (Int.min_le_right _ _) (Int.natCast_nonneg _)
      have a3 : E * xr ≤ E * xc := Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hE)
      have a4 : min M E * N ≤ min M E * ((mis : Int) + xr + yc) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hc0)
      rw [Int.mul_add, Int.mul_add] at a4
      have := oge yr (hyp (by omega))
      have := le_toNat_div N (-T - O) _ hc0 (by omega)
      omega
  · by_cases h0 : xc + yc = 0
    · omega
    · have : O ≤ O * xr + O * yr := by
        by_cases hx : 0 < xc
        · have := oge xr (hxp hx); omega
        · have := oge yr (hyp (by omega)); omega
      have := le_toNat_div (xc + yc) (-T - O) E hE (by push_cast; rw [Int.mul_add]; omega)
      omega
  · intro hx hy
    have := oge xr (hxp hx)
    have := oge yr (hyp hy)
    have := le_toNat_div (xc + yc) (-T - 2 * O) E hE (by push_cast; rw [Int.mul_add]; omega)
    omega

theorem inside_clean2 (path : List Step) (xs ys : List Char) (i a m : Nat)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length)
    (ha : a < i) (hm : m ≤ xs.length)
    (h : ∀ c ∈ errReps path xs ys i (some .diag), ¬(2 * a < c ∧ c < 2 * (i + m))) :
    m ≤ ys.length ∧ ys.take m = xs.take m := by
  induction path generalizing xs ys i m with
  | nil =>
    simp at hx hy
    have : m = 0 := by omega
    subst this; simp
  | cons s rest ih =>
    cases m with
    | zero => simp
    | succ m =>
      cases s with
      | diag =>
        cases xs with
        | nil => simp [xConsumed] at hx
        | cons x xs =>
          cases ys with
          | nil => simp [yConsumed] at hy
          | cons y ys =>
            simp [xConsumed, yConsumed] at hx hy
            have hxy : x = y := by
              apply Classical.byContradiction
              intro hxy
              exact h (2*i+1) (by simp [errReps, hxy]) (by omega)
            have := ih xs ys (i+1) m (by omega) (by omega) (by omega) (by simpa using hm)
              (fun c hc => by
                have := h c (by simp [errReps]; exact Or.inr hc)
                omega)
            simp [hxy, this]
      | gapX =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          exfalso
          exact h (2*i) (by cases xs <;> simp [errReps]) (by omega)
      | gapY =>
        cases xs with
        | nil => simp [xConsumed] at hx
        | cons x xs =>
          exfalso
          exact h (2*i+1) (by cases ys <;> simp [errReps]) (by omega)

/-- A clean stretch of `m` read letters starting at `d` splits the walk: the
part before it consumes `d` read letters and `o` window letters, and the
stretch matches the window at `o`. -/
theorem prefix_clean2 (path : List Step) (xs ys : List Char) (i : Nat) (prev : Option Step)
    (d m : Nat)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length)
    (hm : d + m ≤ xs.length)
    (h : ∀ c ∈ errReps path xs ys i prev, ¬(2 * (i + d) < c ∧ c < 2 * (i + d + m))) :
    ∃ o pre post, path = pre ++ post ∧ (pre.map xConsumed).sum = d ∧
      (pre.map yConsumed).sum = o ∧ o + m ≤ ys.length ∧
      (ys.drop o).take m = (xs.drop d).take m := by
  induction path generalizing xs ys i prev d with
  | nil =>
    simp at hx hy
    have h1 : m = 0 := by omega
    have h2 : d = 0 := by omega
    subst h1; subst h2
    exact ⟨0, [], [], by simp⟩
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          simp [xConsumed, yConsumed] at hx hy
          cases d with
          | zero =>
            cases m with
            | zero => exact ⟨0, [], _, rfl, by simp⟩
            | succ m =>
              have hxy : x = y := by
                apply Classical.byContradiction
                intro hxy
                exact h (2*i+1) (by simp [errReps, hxy]) (by omega)
              have := inside_clean2 rest xs ys (i+1) i m (by omega) (by omega) (by omega)
                (by simpa using hm)
                (fun c hc => by
                  have := h c (by simp [errReps]; exact Or.inr hc)
                  omega)
              exact ⟨0, [], _, rfl, by simp, by simp, by simp; exact this.1, by simp [hxy, this.2]⟩
          | succ d =>
            obtain ⟨o, pre, post, h0, h1, h2, h3, h4⟩ := ih xs ys (i+1) (some .diag) d
              (by omega) (by omega) (by simp at hm; omega)
              (fun c hc => by
                have := h c (by simp [errReps]; exact Or.inr hc)
                omega)
            refine ⟨o+1, .diag :: pre, post, by simp [h0], ?_, ?_, by simp; omega, by simpa using h4⟩
            · simp [xConsumed]; omega
            · simp [yConsumed]; omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        simp [xConsumed, yConsumed] at hx hy
        obtain ⟨o, pre, post, h0, h1, h2, h3, h4⟩ := ih xs ys i (some .gapX) d (by omega) (by omega) hm
          (fun c hc => h c (by cases xs <;> simp only [errReps] <;> exact List.mem_append_right _ hc))
        refine ⟨o+1, .gapX :: pre, post, by simp [h0], ?_, ?_, by simp; omega, by simpa using h4⟩
        · simp [xConsumed]; omega
        · simp [yConsumed]; omega
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        simp [xConsumed, yConsumed] at hx hy
        cases d with
        | zero =>
          cases m with
          | zero => exact ⟨0, [], _, rfl, by simp⟩
          | succ m =>
            exfalso
            exact h (2*i+1) (by cases ys <;> simp [errReps]) (by omega)
        | succ d =>
          obtain ⟨o, pre, post, h0, h1, h2, h3, h4⟩ := ih xs ys (i+1) (some .gapY) d
            (by omega) (by omega) (by simp at hm; omega)
            (fun c hc => by
              have := h c (by cases ys <;> simp [errReps] <;> exact Or.inr hc)
              omega)
          refine ⟨o, .gapY :: pre, post, by simp [h0], ?_, ?_, h3, by simpa using h4⟩
          · simp [xConsumed]; omega
          · simp [yConsumed]; omega


/-- **Clean seed and window shape.**  For a walk of `xs` against `ys` scoring
at least `T`, cut `xs` into `seedBound sc T + 1` seeds of `q` letters.  Some
seed `j` is untouched: all `q` letters equal `ys` at some `o`.  The start
shift `o - j*q` and end shift `(|ys| - o) - (|xs| - j*q)` satisfy `shapeOk`. -/
theorem exists_clean_seed2 (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (xs ys : List Char) (path : List Step)
    (hw : IsMonotoneWalk path xs ys) (hs : T ≤ walkScore sc xs ys path) :
    ∃ j, j ≤ seedBound sc T ∧ ∃ o,
      o + xs.length / (seedBound sc T + 1) ≤ ys.length ∧
      (ys.drop o).take (xs.length / (seedBound sc T + 1)) =
        (xs.drop (j * (xs.length / (seedBound sc T + 1)))).take (xs.length / (seedBound sc T + 1)) ∧
      shapeOk (gapBound sc T) (gapBound2 sc T)
        ((o : Int) - (j * (xs.length / (seedBound sc T + 1)) : Nat))
        (((ys.length : Int) - o) - ((xs.length : Int) - (j * (xs.length / (seedBound sc T + 1)) : Nat))) := by
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
  generalize seedBound sc T = k at *
  generalize hl : xs.length / (k + 1) = l
  have hlk : (k + 1) * l ≤ xs.length := by
    rw [← hl, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hex : ∃ j, j ≤ k ∧ ∀ c ∈ errReps path xs ys 0 none,
      ¬(2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l)) := by
    by_cases hl0 : l = 0
    · exact ⟨0, by omega, fun c _ => by subst hl0; omega⟩
    apply Classical.byContradiction
    intro hno
    have hall : ∀ j, j < k + 1 → j ∈ (errReps path xs ys 0 none).map (fun c => c / (2 * l)) := by
      intro j hj
      have : ∃ c ∈ errReps path xs ys 0 none, 2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l) := by
        apply Classical.byContradiction
        intro hc
        exact hno ⟨j, by omega, fun c hcm hcc => hc ⟨c, hcm, hcc⟩⟩
      obtain ⟨c, hcm, hc1, hc2⟩ := this
      refine List.mem_map.mpr ⟨c, hcm, ?_⟩
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_left_comm]; omega
      · rw [Nat.add_mul, Nat.mul_left_comm]; omega
    have := le_length_of_all_mem (k + 1) _ hall
    simp at this
    omega
  obtain ⟨j, hj, hc⟩ := hex
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
  refine ⟨j, hj, o, ho, hseed, ?_, ?_⟩
  · omega
  · by_cases hx0 : 0 < cnt .gapX pre + cnt .gapX post
    · by_cases hy0 : 0 < cnt .gapY pre + cnt .gapY post
      · have := hG2 hx0 hy0; omega
      · omega
    · omega

end MapSpec

#print axioms MapSpec.exists_clean_seed2
