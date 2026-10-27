import MapperDefs

/-! A walk scoring at least `T` leaves one of `errBound + 1` seeds untouched. -/

namespace MapSpec

open AlignmentSpec

/-- Coordinates of the non-match columns: a gap in x before letter `i` of xs
is `2*i`, a mismatch or deletion of letter `i` is `2*i+1`. -/
def errCoords : List Step → List Char → List Char → Nat → List Nat
  | [], _, _, _ => []
  | .diag :: rest, x :: xs, y :: ys, i =>
      (if x = y then [] else [2*i+1]) ++ errCoords rest xs ys (i+1)
  | .gapX :: rest, xs, _ :: ys, i => (2*i) :: errCoords rest xs ys i
  | .gapY :: rest, _ :: xs, ys, i => (2*i+1) :: errCoords rest xs ys (i+1)
  | _, _, _, _ => []

theorem scoreWalk_add_errs_le (sc : Scoring) (hv : ValidScoring sc) (c : Int)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ -sc.mismatchScore) (hc2 : c ≤ -sc.gapExtend)
    (path : List Step) (xs ys : List Char) (prev : Option Step) (i : Nat) :
    scoreWalk sc path xs ys prev + c * ((errCoords path xs ys i).length : Int) ≤ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  induction path generalizing xs ys prev i with
  | nil => simp [scoreWalk, errCoords]
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [scoreWalk, errCoords]
      | cons x xs =>
        cases ys with
        | nil => simp [scoreWalk, errCoords]
        | cons y ys =>
          have := ih xs ys (some .diag) (i+1)
          by_cases hxy : x = y
          · simp [scoreWalk, errCoords, hxy]; omega
          · simp [scoreWalk, errCoords, hxy, Int.mul_add]; omega
    | gapX =>
      cases ys with
      | nil => cases xs <;> simp [scoreWalk, errCoords]
      | cons y ys =>
        have := ih xs ys (some .gapX) i
        cases xs <;> (simp [scoreWalk, errCoords, Int.mul_add]; split <;> omega)
    | gapY =>
      cases xs with
      | nil => cases ys <;> simp [scoreWalk, errCoords]
      | cons x xs =>
        have := ih xs ys (some .gapY) (i+1)
        cases ys <;> (simp [scoreWalk, errCoords, Int.mul_add]; split <;> omega)

theorem errs_le_errBound (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (xs ys : List Char) (path : List Step) (hs : T ≤ walkScore sc xs ys path) :
    (errCoords path xs ys 0).length ≤ errBound sc T := by
  have hv' := hv
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hc : 0 < min (-sc.mismatchScore) (-sc.gapExtend) := by omega
  have h := scoreWalk_add_errs_le sc hv' (min (-sc.mismatchScore) (-sc.gapExtend))
    (by omega) (by omega) (by omega) path xs ys none 0
  unfold walkScore at hs
  have h' : ((errCoords path xs ys 0).length : Int) * min (-sc.mismatchScore) (-sc.gapExtend) ≤ -T := by
    rw [Int.mul_comm]; omega
  have := Int.le_ediv_of_mul_le hc h'
  unfold errBound
  omega

theorem length_diff_le_errs (path : List Step) (xs ys : List Char) (i : Nat)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length) :
    ys.length ≤ xs.length + (errCoords path xs ys i).length ∧
    xs.length ≤ ys.length + (errCoords path xs ys i).length := by
  induction path generalizing xs ys i with
  | nil => simp at hx hy; omega
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
          have := ih xs ys (i+1) (by omega) (by omega)
          simp [errCoords]; omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        simp [xConsumed, yConsumed] at hx hy
        have := ih xs ys i (by omega) (by omega)
        cases xs <;> (simp [errCoords]; simp at this; omega)
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        simp [xConsumed, yConsumed] at hx hy
        have := ih xs ys (i+1) (by omega) (by omega)
        cases ys <;> (simp [errCoords]; simp at this; omega)

theorem inside_clean (path : List Step) (xs ys : List Char) (i a m : Nat)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length)
    (ha : a < i) (hm : m ≤ xs.length)
    (h : ∀ c ∈ errCoords path xs ys i, ¬(2 * a < c ∧ c < 2 * (i + m))) :
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
              exact h (2*i+1) (by simp [errCoords, hxy]) (by omega)
            have := ih xs ys (i+1) m (by omega) (by omega) (by omega) (by simpa using hm)
              (fun c hc => by
                have := h c (by simp [errCoords]; exact Or.inr hc)
                omega)
            simp [hxy, this]
      | gapX =>
        cases ys with
        | nil => simp [yConsumed] at hy
        | cons y ys =>
          exfalso
          exact h (2*i) (by cases xs <;> simp [errCoords]) (by omega)
      | gapY =>
        cases xs with
        | nil => simp [xConsumed] at hx
        | cons x xs =>
          exfalso
          exact h (2*i+1) (by cases ys <;> simp [errCoords]) (by omega)

theorem prefix_clean (path : List Step) (xs ys : List Char) (i d m : Nat)
    (hx : (path.map xConsumed).sum = xs.length) (hy : (path.map yConsumed).sum = ys.length)
    (hm : d + m ≤ xs.length)
    (h : ∀ c ∈ errCoords path xs ys i, ¬(2 * (i + d) < c ∧ c < 2 * (i + d + m))) :
    ∃ o, o + m ≤ ys.length ∧ (ys.drop o).take m = (xs.drop d).take m ∧
      o ≤ d + (errCoords path xs ys i).length ∧ d ≤ o + (errCoords path xs ys i).length := by
  induction path generalizing xs ys i d with
  | nil =>
    simp at hx hy
    have h1 : m = 0 := by omega
    have h2 : d = 0 := by omega
    subst h1; subst h2
    exact ⟨0, by simp⟩
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
            | zero => exact ⟨0, by simp⟩
            | succ m =>
              have hxy : x = y := by
                apply Classical.byContradiction
                intro hxy
                exact h (2*i+1) (by simp [errCoords, hxy]) (by omega)
              have := inside_clean rest xs ys (i+1) i m (by omega) (by omega) (by omega)
                (by simpa using hm)
                (fun c hc => by
                  have := h c (by simp [errCoords]; exact Or.inr hc)
                  omega)
              exact ⟨0, by simp; exact this.1, by simp [hxy, this.2], by omega, by omega⟩
          | succ d =>
            obtain ⟨o, h1, h2, h3, h4⟩ := ih xs ys (i+1) d (by omega) (by omega)
              (by simp at hm; omega)
              (fun c hc => by
                have := h c (by simp [errCoords]; exact Or.inr hc)
                omega)
            refine ⟨o+1, by simp; omega, by simpa using h2, ?_, ?_⟩
            · simp [errCoords]; omega
            · simp [errCoords]; omega
    | gapX =>
      cases ys with
      | nil => simp [yConsumed] at hy
      | cons y ys =>
        simp [xConsumed, yConsumed] at hx hy
        have hE : (errCoords (Step.gapX :: rest) xs (y :: ys) i).length
            = (errCoords rest xs ys i).length + 1 := by
          cases xs <;> simp [errCoords]
        obtain ⟨o, h1, h2, h3, h4⟩ := ih xs ys i d (by omega) (by omega) hm
          (fun c hc => h c (by cases xs <;> simp [errCoords] <;> exact Or.inr hc))
        exact ⟨o+1, by simp; omega, by simpa using h2, by omega, by omega⟩
    | gapY =>
      cases xs with
      | nil => simp [xConsumed] at hx
      | cons x xs =>
        simp [xConsumed, yConsumed] at hx hy
        have hE : (errCoords (Step.gapY :: rest) (x :: xs) ys i).length
            = (errCoords rest xs ys (i+1)).length + 1 := by
          cases ys <;> simp [errCoords]
        cases d with
        | zero =>
          cases m with
          | zero => exact ⟨0, by simp⟩
          | succ m =>
            exfalso
            exact h (2*i+1) (by cases ys <;> simp [errCoords]) (by omega)
        | succ d =>
          obtain ⟨o, h1, h2, h3, h4⟩ := ih xs ys (i+1) d (by omega) (by omega)
            (by simp at hm; omega)
            (fun c hc => by
              have := h c (by cases ys <;> simp [errCoords] <;> exact Or.inr hc)
              omega)
          exact ⟨o, h1, by simpa using h2, by omega, by omega⟩

theorem le_length_of_all_mem (n : Nat) (l : List Nat) (h : ∀ j, j < n → j ∈ l) :
    n ≤ l.length := by
  induction n generalizing l with
  | zero => omega
  | succ n ih =>
    have hn : n ∈ l := h n (by omega)
    have := ih (l.erase n) (fun j hj => (List.mem_erase_of_ne (by omega)).mpr (h j (by omega)))
    rw [List.length_erase_of_mem hn] at this
    have : 0 < l.length := List.length_pos_of_mem hn
    omega

theorem exists_clean_seed (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (xs ys : List Char) (path : List Step)
    (hw : IsMonotoneWalk path xs ys) (hs : T ≤ walkScore sc xs ys path) :
    ys.length ≤ xs.length + errBound sc T ∧ xs.length ≤ ys.length + errBound sc T ∧
    ∃ j, j ≤ errBound sc T ∧ ∃ o,
      o + xs.length / (errBound sc T + 1) ≤ ys.length ∧
      (ys.drop o).take (xs.length / (errBound sc T + 1)) =
        (xs.drop (j * (xs.length / (errBound sc T + 1)))).take (xs.length / (errBound sc T + 1)) ∧
      o ≤ j * (xs.length / (errBound sc T + 1)) + errBound sc T ∧
      j * (xs.length / (errBound sc T + 1)) ≤ o + errBound sc T := by
  obtain ⟨hx, hy⟩ := hw
  have hE := errs_le_errBound sc hv T xs ys path hs
  have hL := length_diff_le_errs path xs ys 0 hx hy
  generalize errBound sc T = k at *
  refine ⟨by omega, by omega, ?_⟩
  generalize hl : xs.length / (k + 1) = l
  have hlk : (k + 1) * l ≤ xs.length := by
    rw [← hl, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  by_cases hl0 : l = 0
  · subst hl0
    exact ⟨0, by omega, 0, by simp⟩
  have hex : ∃ j, j ≤ k ∧ ∀ c ∈ errCoords path xs ys 0,
      ¬(2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l)) := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ j, j < k + 1 → j ∈ (errCoords path xs ys 0).map (fun c => c / (2 * l)) := by
      intro j hj
      have : ∃ c ∈ errCoords path xs ys 0, 2 * (0 + j * l) < c ∧ c < 2 * (0 + j * l + l) := by
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
  obtain ⟨o, h1, h2, h3, h4⟩ := prefix_clean path xs ys 0 (j * l) l hx hy hjl hc
  exact ⟨j, hj, o, h1, h2, by omega, by omega⟩

end MapSpec

#print axioms MapSpec.exists_clean_seed
