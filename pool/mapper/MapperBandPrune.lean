import MapperBandFast
import MapperFastScore

/-! Pruning the banded pass with spoiled read blocks (default scoring `sc0`).

`DeadRow2 tN tG i`: every cell of row `i` is below `tN` (state none) or `tG`
(gap states).  A dead row stays dead going up (`deadRow2_step`, for
`tN ≤ tG ≤ tN + 8`).  Passing up over a read block `[a, a + L)` that has no
exact copy at any of the positions `p` considered lowers the none threshold by
`4` (`block_step`: inside the block every path pays a mismatch, `−4`, or opens a
gap, `−8`, against the `+4` the gap states may carry). -/

namespace MapSpec

open AlignmentSpec

/-- Every cell of row `i` is below `tN` (none) or `tG` (gap states). -/
def DeadRow2 (xs gs : List Char) (e i : Nat) (tN tG : Int) : Prop :=
  ∀ p, p ≤ e → cv sc0 xs gs e none i p < tN ∧
    cv sc0 xs gs e (some .gapX) i p < tG ∧ cv sc0 xs gs e (some .gapY) i p < tG

theorem diagCost_le (x y : Char) : diagCost sc0 x y ≤ 0 := by
  unfold diagCost sc0; split <;> decide

@[simp] theorem gx_none : gapXCost sc0 none = -8 := by decide
@[simp] theorem gx_x : gapXCost sc0 (some .gapX) = -2 := by decide
@[simp] theorem gx_y : gapXCost sc0 (some .gapY) = -8 := by decide
@[simp] theorem gy_none : gapYCost sc0 none = -8 := by decide
@[simp] theorem gy_x : gapYCost sc0 (some .gapX) = -8 := by decide
@[simp] theorem gy_y : gapYCost sc0 (some .gapY) = -2 := by decide

theorem deadRow2_step (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (i : Nat) (hi : i < xs.length)
    (tN tG : Int) (h1 : tN ≤ tG) (h2 : tG ≤ tN + 8) (hd : DeadRow2 xs gs e (i + 1) tN tG) :
    DeadRow2 xs gs e i tN tG := by
  have key : ∀ m p, e - p = m → p ≤ e → cv sc0 xs gs e none i p < tN ∧
      cv sc0 xs gs e (some .gapX) i p < tG ∧ cv sc0 xs gs e (some .gapY) i p < tG := by
    intro m
    induction m with
    | zero =>
      intro p hm hp
      have hpe : p = e := by omega
      subst hpe
      obtain ⟨-, -, hy⟩ := hd p (Nat.le_refl _)
      rw [cv_end sc0 xs gs p none i hi, cv_end sc0 xs gs p (some .gapX) i hi, cv_end sc0 xs gs p (some .gapY) i hi]; simp; omega
    | succ m ih =>
      intro p hm hp
      obtain ⟨hn1, -, -⟩ := hd (p + 1) (by omega)
      obtain ⟨-, -, hy⟩ := hd p hp
      obtain ⟨-, hx, -⟩ := ih (p + 1) (by omega) (by omega)
      have hD := diagCost_le xs[i] (gs[p]'(by omega))
      rw [cv_main sc0 xs gs e he none i p hi (by omega), cv_main sc0 xs gs e he (some .gapX) i p hi (by omega),
        cv_main sc0 xs gs e he (some .gapY) i p hi (by omega)]; simp; omega
  intro p hp
  exact key (e - p) p rfl hp

theorem deadRow2_down (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (tN tG : Int)
    (h1 : tN ≤ tG) (h2 : tG ≤ tN + 8) :
    ∀ k i, k ≤ i → i ≤ xs.length → DeadRow2 xs gs e i tN tG → DeadRow2 xs gs e (i - k) tN tG
  | 0, i, _, _, h => by simpa using h
  | k + 1, i, hk, hi, h => by
    have := deadRow2_down xs gs e he tN tG h1 h2 k i (by omega) hi h
    rw [show i - (k + 1) = (i - k) - 1 by omega]
    exact deadRow2_step xs gs e he (i - k - 1) (by omega) tN tG h1 h2 (by rwa [show i - k - 1 + 1 = i - k by omega])

/-- Read letters `[r, b)` equal genome letters `[p, p + (b - r))`. -/
def ExactAt (xs gs : List Char) (r b p : Nat) : Prop :=
  (xs.drop r).take (b - r) = (gs.drop p).take (b - r)

/-- **Passing a block.**  Rows `a … a + L` (`L ≥ 2`): from row `a + L` dead at
`(t, t + 4)` to row `a` dead at `(t − 4, t)`, except none cells whose block is an
exact copy. -/
theorem block_step (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (a L : Nat) (hL : 2 ≤ L)
    (hb : a + L ≤ xs.length) (t : Int)
    (hd : DeadRow2 xs gs e (a + L) t (t + 4)) :
    ∀ p, p ≤ e → (cv sc0 xs gs e none a p < t - 4 ∨ (p + L ≤ e ∧ ExactAt xs gs a (a + L) p)) ∧
      cv sc0 xs gs e (some .gapX) a p < t ∧ cv sc0 xs gs e (some .gapY) a p < t := by
  -- rows `a + L - s`, `s = 0 … L`
  have row : ∀ s, s ≤ L → ∀ p, p ≤ e →
      (cv sc0 xs gs e none (a + L - s) p < t - 4 ∨
        (p + s ≤ e ∧ ExactAt xs gs (a + L - s) (a + L) p)) ∧
      cv sc0 xs gs e none (a + L - s) p < t ∧
      cv sc0 xs gs e (some .gapX) (a + L - s) p < t + (if s = 0 then 4 else 0) ∧
      cv sc0 xs gs e (some .gapY) (a + L - s) p < t + (if s = 0 then 4 else if s = 1 then 2 else 0) := by
    intro s
    induction s with
    | zero =>
      intro _ p hp
      obtain ⟨h1, h2, h3⟩ := hd p hp
      refine ⟨Or.inr ⟨by omega, ?_⟩, by simpa using h1, by simpa using h2, by simpa using h3⟩
      unfold ExactAt; simp
    | succ s ih =>
      intro hs
      have ih' := ih (by omega)
      have hr : a + L - (s + 1) < xs.length := by omega
      have hr1 : a + L - (s + 1) + 1 = a + L - s := by omega
      -- the gapX value along the row, from the end `e` back
      have hX : ∀ m p, e - p = m → p ≤ e → cv sc0 xs gs e (some .gapX) (a + L - (s + 1)) p < t := by
        intro m
        induction m with
        | zero =>
          intro p hm hp
          have hpe : p = e := by omega
          subst hpe
          obtain ⟨-, -, -, hy⟩ := ih' p (Nat.le_refl _)
          rw [cv_end sc0 xs gs p _ _ hr, hr1]
          simp only [gy_x]
          split at hy <;> (try split at hy) <;> simp <;> omega
        | succ m ihm =>
          intro p hm hp
          obtain ⟨-, hn1, -, -⟩ := ih' (p + 1) (by omega)
          obtain ⟨-, -, -, hy⟩ := ih' p hp
          have hx := ihm (p + 1) (by omega) (by omega)
          have hD := diagCost_le xs[a + L - (s + 1)] (gs[p]'(by omega))
          rw [cv_main sc0 xs gs e he _ _ p hr (by omega), hr1]
          simp only [gx_x, gy_x]
          split at hy <;> (try split at hy) <;> simp <;> omega
      intro p hp
      have hxp := hX (e - p) p rfl hp
      by_cases hpe : p = e
      · -- the end column: only gapY steps
        subst hpe
        obtain ⟨-, -, -, hy⟩ := ih' p (Nat.le_refl _)
        have e1 := cv_end sc0 xs gs p none _ hr
        have e3 := cv_end sc0 xs gs p (some .gapY) _ hr
        rw [hr1] at e1 e3
        simp only [gy_none, gy_y] at e1 e3
        refine ⟨Or.inl ?_, ?_, by simpa using hxp, ?_⟩
        · split at hy <;> (try split at hy) <;> omega
        · split at hy <;> (try split at hy) <;> omega
        · split at hy <;> (try split at hy) <;> simp <;> omega
      · obtain ⟨hex1, hn1, -, -⟩ := ih' (p + 1) (by omega)
        obtain ⟨-, -, -, hy⟩ := ih' p hp
        have hxp1 := hX (e - (p + 1)) (p + 1) rfl (by omega)
        have m1 := cv_main sc0 xs gs e he none _ p hr (by omega)
        have m3 := cv_main sc0 xs gs e he (some .gapY) _ p hr (by omega)
        rw [hr1] at m1 m3
        simp only [gx_none, gy_none, gx_y, gy_y] at m1 m3
        have hD := diagCost_le xs[a + L - (s + 1)] (gs[p]'(by omega))
        refine ⟨?_, ?_, by simpa using hxp, ?_⟩
        · -- none: a mismatch or a gap costs 4 or more, a match keeps the exact run going
          by_cases hm : xs[a + L - (s + 1)] = gs[p]'(by omega)
          · rcases hex1 with hlt | ⟨hle, hex⟩
            · left
              have : diagCost sc0 xs[a + L - (s + 1)] (gs[p]'(by omega)) = 0 := by
                unfold diagCost; simp [hm, sc0]
              split at hy <;> (try split at hy) <;> omega
            · right
              refine ⟨by omega, ?_⟩
              unfold ExactAt at hex ⊢
              rw [show a + L - (a + L - (s + 1)) = s + 1 by omega]
              rw [show a + L - (a + L - s) = s by omega] at hex
              rw [List.drop_eq_getElem_cons hr, List.drop_eq_getElem_cons (show p < gs.length by omega),
                List.take_succ_cons, List.take_succ_cons, hm, hr1, hex]
          · left
            have : diagCost sc0 xs[a + L - (s + 1)] (gs[p]'(by omega)) = -4 := by
              unfold diagCost; simp [hm, sc0]
            split at hy <;> (try split at hy) <;> omega
        · split at hy <;> (try split at hy) <;> omega
        · split at hy <;> (try split at hy) <;> simp <;> omega
  intro p hp
  obtain ⟨h1, -, h3, h4⟩ := row L (Nat.le_refl _) p hp
  rw [show a + L - L = a by omega] at h1 h3 h4
  refine ⟨h1, ?_, ?_⟩
  · simpa [show L ≠ 0 by omega] using h3
  · simpa [show L ≠ 0 by omega, show L ≠ 1 by omega] using h4

end MapSpec
