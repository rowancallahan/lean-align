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

/-- Spoiled blocks wholly above row `i` (block `j` is rows `[8j, 8j + 8)`). -/
def blocksAbove (sp : Nat → Bool) (i : Nat) : Nat := ((List.range (i / 8)).filter sp).length

/-- The none threshold of row `i`. -/
def tNr (T : Int) (sp : Nat → Bool) (i : Nat) : Int := T + 4 * (blocksAbove sp i : Int)

/-- The gap-state threshold of row `i`. -/
def tGr (T : Int) (sp : Nat → Bool) (i : Nat) : Int :=
  tNr T sp i + (if blocksAbove sp i = 0 then 6 else 4)

theorem blocksAbove_zero (sp : Nat → Bool) : blocksAbove sp 0 = 0 := by simp [blocksAbove]

theorem blocksAbove_succ_same (sp : Nat → Bool) (i : Nat)
    (h : (i + 1) % 8 ≠ 0 ∨ sp ((i + 1) / 8 - 1) = false) :
    blocksAbove sp i = blocksAbove sp (i + 1) := by
  unfold blocksAbove
  by_cases hm : (i + 1) % 8 = 0
  · have hq : (i + 1) / 8 = i / 8 + 1 := by omega
    rw [hq, List.range_succ, List.filter_append]
    have hs : sp (i / 8) = false := by
      rcases h with h | h
      · exact absurd hm h
      · rwa [hq] at h
    simp [hs]
  · rw [show (i + 1) / 8 = i / 8 by omega]

theorem blocksAbove_block (sp : Nat → Bool) (j : Nat) (h : sp j = true) :
    blocksAbove sp (8 * j + 8) = blocksAbove sp (8 * j) + 1 := by
  unfold blocksAbove
  rw [show (8 * j + 8) / 8 = j + 1 by omega, show 8 * j / 8 = j by omega, List.range_succ,
    List.filter_append]
  simp [h]

/-- **Pruned dead row.**  Row `i` dead at the thresholds `tNr`/`tGr` (spoiled blocks
with no exact copy at any in-band position) makes row `0` dead at `T`. -/
theorem prune_down (T : Int) (B : Nat) (hb : BandOK sc0 T B) (xs gs : List Char) (e : Nat)
    (he : e ≤ gs.length) (sp : Nat → Bool)
    (hsp : ∀ j, sp j = true → 8 * j + 8 ≤ xs.length → ∀ p, p ≤ e →
      ((((e - p : Nat) : Int) - ((xs.length - 8 * j : Nat) : Int)).natAbs ≤ B) →
      ¬(p + 8 ≤ e ∧ ExactAt xs gs (8 * j) (8 * j + 8) p)) :
    ∀ i, i ≤ xs.length → DeadRow2 xs gs e i (tNr T sp i) (tGr T sp i) → DeadRow sc0 T xs gs e 0 := by
  have hv : ValidScoring sc0 := by unfold ValidScoring sc0; decide
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi hd
    cases i with
    | zero =>
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hd p hp
      simp only [tGr, tNr, blocksAbove_zero] at h1 h2 h3
      refine ⟨by simpa using h1, ?_, ?_⟩ <;> simp only [sc0] at * <;> simp at * <;> omega
    | succ i =>
      by_cases hblk : (i + 1) % 8 = 0 ∧ sp ((i + 1) / 8 - 1) = true
      · -- a spoiled block ends at row `i + 1`: jump to its start
        obtain ⟨hm, hs⟩ := hblk
        generalize hj : (i + 1) / 8 - 1 = j at hs
        have hij : i + 1 = 8 * j + 8 := by omega
        have hba := blocksAbove_block sp j hs
        rw [← hij] at hba
        have hd' : DeadRow2 xs gs e (8 * j + 8) (tNr T sp (i + 1)) (tNr T sp (i + 1) + 4) := by
          intro p hp
          have := hd p hp
          rw [← hij]
          unfold tGr at this
          rw [if_neg (by omega)] at this
          exact this
        have hst := block_step xs gs e he (8 * j) 8 (by omega) (by omega) _ hd'
        apply ih (8 * j) (by omega) (by omega)
        intro p hp
        obtain ⟨hn, hx, hy⟩ := hst p hp
        have htn : tNr T sp (8 * j) = tNr T sp (i + 1) - 4 := by unfold tNr; rw [hba]; push_cast; omega
        have htg : tNr T sp (i + 1) ≤ tGr T sp (8 * j) := by
          unfold tGr; rw [htn]; split <;> omega
        refine ⟨?_, by omega, by omega⟩
        rw [htn]
        rcases hn with hn | hex
        · exact hn
        · -- an exact copy: outside the band, below `T`
          by_cases hband : ((((e - p : Nat) : Int) - ((xs.length - 8 * j : Nat) : Int)).natAbs ≤ B)
          · exact absurd hex (hsp j hs (by omega) p hp hband)
          · have := cv_off_band sc0 hv T B hb xs gs e he none (8 * j) p (by omega)
            simp only [thr] at this
            have : T ≤ tNr T sp (i + 1) - 4 := by unfold tNr; rw [hba]; push_cast; omega
            omega
      · -- no spoiled block ends here: one row up, same thresholds
        have hsame := blocksAbove_succ_same sp i (by
          by_cases hm : (i + 1) % 8 = 0
          · right; simpa [hm] using hblk
          · left; exact hm)
        apply ih i (by omega) (by omega)
        have ht : tNr T sp i = tNr T sp (i + 1) ∧ tGr T sp i = tGr T sp (i + 1) := by
          unfold tGr tNr; rw [hsame]; exact ⟨rfl, rfl⟩
        rw [ht.1, ht.2]
        exact deadRow2_step xs gs e he i (by omega) _ _ (by unfold tGr; split <;> omega)
          (by unfold tGr; split <;> omega) hd

/-! ## The pruned pass -/

/-- `bandRows2` with the death test at the row thresholds `tNr`/`tGr`. -/
@[specialize] def bandRowsP (T : Int) (B : Nat) (sp : Nat → Bool) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e : Nat) : Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      match bandLoop sc0 (tNr T sp i) (tGr T sp i) rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRowsP T B sp rb gb e i N X Y
        else none
    else none

/-- All windows ending at `e`, pruned pass. -/
@[specialize] def bandEndP (T : Int) (B : Nat) (sp : Nat → Bool) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e : Nat) : Option (Array Int) :=
  bandRowsP T B sp rb gb e rb.size (Array.replicate (2 * B + 3) (T - 1))
    (Array.replicate (2 * B + 3) (T - 1)) (Array.replicate (2 * B + 3) (T - 1))

/-- The values written by `bandLoop` do not depend on its thresholds. -/
theorem bandLoop_vals (sc : Scoring) (T1 To1 T2 To2 : Int) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ m k p (N X Y : Array Int) (a1 a2 : Bool), hi + 1 - k = m →
      (bandLoop sc T1 To1 rb gb e i lastRow hi k p N X Y a1).1 = (bandLoop sc T2 To2 rb gb e i lastRow hi k p N X Y a2).1 ∧
      (bandLoop sc T1 To1 rb gb e i lastRow hi k p N X Y a1).2.1 =
        (bandLoop sc T2 To2 rb gb e i lastRow hi k p N X Y a2).2.1 ∧
      (bandLoop sc T1 To1 rb gb e i lastRow hi k p N X Y a1).2.2.1 =
        (bandLoop sc T2 To2 rb gb e i lastRow hi k p N X Y a2).2.2.1 := by
  intro m
  induction m with
  | zero =>
    intro k p N X Y a1 a2 hm
    unfold bandLoop
    rw [if_neg (by omega), if_neg (by omega)]
    exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro k p N X Y a1 a2 hm
    unfold bandLoop
    rw [if_pos (by omega), if_pos (by omega)]
    exact ih (k + 1) _ _ _ _ _ _ (by omega)

/-- `bandLoop` leaves the slots below `k + 1` alone. -/
theorem bandLoop_frame (sc : Scoring) (T To : Int) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ m k p (N X Y : Array Int) (a : Bool), hi + 1 - k = m → ∀ j, j ≤ k →
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).1[j]! = N[j]! ∧
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).2.1[j]! = X[j]! ∧
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).2.2.1[j]! = Y[j]! := by
  intro m
  induction m with
  | zero =>
    intro k p N X Y a hm j hj
    rw [bandLoop, if_neg (by omega)]
    exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro k p N X Y a hm j hj
    rw [bandLoop, if_pos (by omega)]
    obtain ⟨h1, h2, h3⟩ := ih (k + 1) _ _ _ _ _ (by omega) j (by omega)
    rw [h1, h2, h3, Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_ne _ _ _ _ (by omega),
      Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact ⟨rfl, rfl, rfl⟩

/-- A dead loop: every slot it wrote is below the thresholds. -/
theorem bandLoop_dead (sc : Scoring) (T To : Int) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ m k p (N X Y : Array Int) (a : Bool), hi + 1 - k = m →
      hi + 2 ≤ N.size → hi + 2 ≤ X.size → hi + 2 ≤ Y.size →
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).2.2.2 = false →
      a = false ∧ ∀ j, k ≤ j → j ≤ hi →
        (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).1[j + 1]! < T ∧
        (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).2.1[j + 1]! < To ∧
        (bandLoop sc T To rb gb e i lastRow hi k p N X Y a).2.2.1[j + 1]! < To := by
  intro m
  induction m with
  | zero =>
    intro k p N X Y a hm _ _ _ hd
    rw [bandLoop, if_neg (by omega)] at hd ⊢
    exact ⟨hd, fun j hj hj2 => by omega⟩
  | succ m ih =>
    intro k p N X Y a hm hN hX hY hd
    rw [bandLoop, if_pos (by omega)] at hd ⊢
    generalize hv : cellVals sc rb gb i p lastRow (p == e) N[k + 1]! X[k]! Y[k + 2]! = v at hd ⊢
    have h := ih (k + 1) (p - 1) (N.set! (k + 1) v.1) (X.set! (k + 1) v.2.1) (Y.set! (k + 1) v.2.2) _ (by omega)
      (by simp; omega) (by simp; omega) (by simp; omega) hd
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨ha, h1⟩, h2⟩, h3⟩, hrest⟩ := h
    refine ⟨ha, fun j hj hj2 => ?_⟩
    by_cases hjk : j = k
    · subst hjk
      obtain ⟨f1, f2, f3⟩ := bandLoop_frame sc T To rb gb e i lastRow hi m (j + 1) (p - 1)
        (N.set! (j + 1) v.1) (X.set! (j + 1) v.2.1) (Y.set! (j + 1) v.2.2) _ (by omega) (j + 1) (Nat.le_refl _)
      rw [f1, f2, f3, Array.getElem!_set!_self _ _ _ (by omega), Array.getElem!_set!_self _ _ _ (by omega),
        Array.getElem!_set!_self _ _ _ (by omega)]
      exact ⟨by omega, by omega, by omega⟩
    · exact hrest j (by omega) hj2

theorem Rel.lt_of {t c v u : Int} (h : Rel t c v) (hc : c < u) (htu : t ≤ u) : v < u := by
  by_cases hv : t ≤ v
  · rw [← h.1 hv]; exact hc
  · omega

/-- **The pruned pass.**  Same guarantee as `bandRows2_spec`, given that every
block counted by `sp` has no exact copy in the band. -/
theorem bandRowsP_spec (T : Int) (B : Nat) (hb : BandOK sc0 T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) (sp : Nat → Bool)
    (hsp : ∀ j, sp j = true → 8 * j + 8 ≤ xs.length → ∀ p, p ≤ e →
      ((((e - p : Nat) : Int) - ((xs.length - 8 * j : Nat) : Int)).natAbs ≤ B) →
      ¬(p + 8 ≤ e ∧ ExactAt xs gs (8 * j) (8 * j + 8) p)) :
    ∀ i (N X Y : Array Int), i ≤ xs.length → RowShape T B N X Y →
    (∀ k, k < 2 * B + 1 → i < xs.length → Valid xs.length B e (i + 1) k →
      CellRelP sc0 T B xs gs e (i + 1) k N X Y) →
    match bandRowsP T B sp rb gb e i N X Y with
    | some A => A.size = 2 * B + 3 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k + 1]! (cv sc0 xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc0 T xs gs e 0 := by
  have hv : ValidScoring sc0 := by unfold ValidScoring sc0; decide
  have hn : rb.size = xs.length := hr.1
  have hO : sc0.gapOpen = -6 := rfl
  -- thresholds are at least the plain ones
  have hth : ∀ i, T ≤ tNr T sp i ∧ T - sc0.gapOpen ≤ tGr T sp i := by
    intro i; unfold tGr tNr; rw [hO]; split <;> omega
  intro i
  induction i with
  | zero =>
    intro N X Y hi hshape hold
    rw [bandRowsP]
    by_cases hin : rb.size ≤ e + 0 + B
    · rw [if_pos hin]
      have h := bandLoop_spec sc0 hv T B hb xs gs e he rb gb hr hg 0 hi (min (2 * B) (e + 0 + B - xs.length))
        (fun k hk => by unfold Valid; omega) (by omega) _ (0 + B - xs.length) (e + 0 + B - xs.length - (0 + B - xs.length))
        N X Y false rfl (Nat.le_refl _) (by omega) (fun _ => by unfold pOf; omega) hshape
        (fun k hk _ hvk => by unfold Valid at hvk; omega) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
        (fun _ k hk _ hvk => by unfold Valid at hvk; omega)
      have hval := bandLoop_vals sc0 (tNr T sp 0) (tGr T sp 0) T (T - sc0.gapOpen) rb gb e 0 (0 == rb.size)
        (min (2 * B) (e + 0 + B - rb.size)) _ (0 + B - rb.size) (e + 0 + B - rb.size - (0 + B - rb.size))
        N X Y false false rfl
      have hdd := bandLoop_dead sc0 (tNr T sp 0) (tGr T sp 0) rb gb e 0 (0 == rb.size)
        (min (2 * B) (e + 0 + B - rb.size)) _ (0 + B - rb.size) (e + 0 + B - rb.size - (0 + B - rb.size))
        N X Y false rfl (by have := hshape.1; omega) (by have := hshape.2.1; omega) (by have := hshape.2.2.1; omega)
      rw [hn] at hin hval hdd ⊢
      revert h hval hdd
      generalize bandLoop sc0 (tNr T sp 0) (tGr T sp 0) rb gb e 0 (0 == xs.length) (min (2 * B) (e + 0 + B - xs.length))
        (0 + B - xs.length) (e + 0 + B - xs.length - (0 + B - xs.length)) N X Y false = r
      generalize bandLoop sc0 T (T - sc0.gapOpen) rb gb e 0 (0 == xs.length) (min (2 * B) (e + 0 + B - xs.length))
        (0 + B - xs.length) (e + 0 + B - xs.length - (0 + B - xs.length)) N X Y false = rB
      obtain ⟨N', X', Y', alive⟩ := r
      intro h hval hdd
      obtain ⟨e1, e2, e3⟩ := hval
      simp only at e1 e2 e3
      obtain ⟨hshape', hrel, -⟩ := h
      rw [← e1, ← e2, ← e3] at hshape' hrel
      cases alive with
      | true => exact ⟨hshape'.1, fun k hk hvk => (hrel k hk hvk).1⟩
      | false =>
        obtain ⟨-, hlt⟩ := hdd rfl
        apply prune_down T B hb xs gs e he sp hsp 0 hi
        intro p hp
        by_cases hin2 : xs.length + p ≤ e + 0 + B ∧ e + 0 ≤ xs.length + p + B
        · have hk := hrel (e + 0 + B - xs.length - p) (by omega) ⟨by omega, by omega⟩
          have hl := hlt (e + 0 + B - xs.length - p) (by omega) (by omega)
          simp only at hl
          unfold CellRelP at hk
          rw [show pOf xs.length B e 0 (e + 0 + B - xs.length - p) = p by unfold pOf; omega] at hk
          obtain ⟨r1, r2, r3⟩ := hk
          obtain ⟨l1, l2, l3⟩ := hl
          have t1 := hth 0
          exact ⟨r1.lt_of l1 t1.1, r2.lt_of l2 t1.2, r3.lt_of l3 t1.2⟩
        · have hoff : (B : Int) + 1 ≤ (((e - p : Nat) : Int) - ((xs.length - 0 : Nat) : Int)).natAbs := by omega
          have a := cv_off_band sc0 hv T B hb xs gs e he none 0 p hoff
          have b := cv_off_band sc0 hv T B hb xs gs e he (some .gapX) 0 p hoff
          have c := cv_off_band sc0 hv T B hb xs gs e he (some .gapY) 0 p hoff
          simp only [thr] at a b c
          have t1 := hth 0
          exact ⟨by omega, by omega, by omega⟩
    · rw [if_neg hin]
      exact deadRow_of_band sc0 hv T B hb xs gs e he 0 hi
        (fun k _ hvk => by unfold Valid at hvk; omega)
  | succ i ih =>
    intro N X Y hi hshape hold
    rw [bandRowsP]
    by_cases hin : rb.size ≤ e + (i + 1) + B
    · rw [if_pos hin]
      have h := bandLoop_spec sc0 hv T B hb xs gs e he rb gb hr hg (i + 1) hi
        (min (2 * B) (e + (i + 1) + B - xs.length))
        (fun k hk => by unfold Valid; omega) (by omega) _ (i + 1 + B - xs.length)
        (e + (i + 1) + B - xs.length - (i + 1 + B - xs.length))
        N X Y false rfl (Nat.le_refl _) (by omega) (fun _ => by unfold pOf; omega) hshape
        (fun k hk _ hvk => by unfold Valid at hvk; omega) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
        (fun _ k hk _ hvk => by unfold Valid at hvk; omega)
      have hval := bandLoop_vals sc0 (tNr T sp (i + 1)) (tGr T sp (i + 1)) T (T - sc0.gapOpen) rb gb e (i + 1)
        (i + 1 == rb.size) (min (2 * B) (e + (i + 1) + B - rb.size)) _ (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size)) N X Y false false rfl
      have hdd := bandLoop_dead sc0 (tNr T sp (i + 1)) (tGr T sp (i + 1)) rb gb e (i + 1) (i + 1 == rb.size)
        (min (2 * B) (e + (i + 1) + B - rb.size)) _ (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size))
        N X Y false rfl (by have := hshape.1; omega) (by have := hshape.2.1; omega) (by have := hshape.2.2.1; omega)
      rw [hn] at hin hval hdd ⊢
      revert h hval hdd
      generalize bandLoop sc0 (tNr T sp (i + 1)) (tGr T sp (i + 1)) rb gb e (i + 1) (i + 1 == xs.length)
        (min (2 * B) (e + (i + 1) + B - xs.length)) (i + 1 + B - xs.length)
        (e + (i + 1) + B - xs.length - (i + 1 + B - xs.length)) N X Y false = r
      generalize bandLoop sc0 T (T - sc0.gapOpen) rb gb e (i + 1) (i + 1 == xs.length)
        (min (2 * B) (e + (i + 1) + B - xs.length)) (i + 1 + B - xs.length)
        (e + (i + 1) + B - xs.length - (i + 1 + B - xs.length)) N X Y false = rB
      obtain ⟨N', X', Y', alive⟩ := r
      intro h hval hdd
      obtain ⟨e1, e2, e3⟩ := hval
      simp only at e1 e2 e3
      obtain ⟨hshape', hrel, -⟩ := h
      rw [← e1, ← e2, ← e3] at hshape' hrel
      cases alive with
      | true =>
        exact ih N' X' Y' (by omega) hshape' (fun k hk _ hvk => hrel k hk hvk)
      | false =>
        obtain ⟨-, hlt⟩ := hdd rfl
        apply prune_down T B hb xs gs e he sp hsp (i + 1) hi
        intro p hp
        by_cases hin2 : xs.length + p ≤ e + (i + 1) + B ∧ e + (i + 1) ≤ xs.length + p + B
        · have hk := hrel (e + (i + 1) + B - xs.length - p) (by omega) ⟨by omega, by omega⟩
          have hl := hlt (e + (i + 1) + B - xs.length - p) (by omega) (by omega)
          simp only at hl
          unfold CellRelP at hk
          rw [show pOf xs.length B e (i + 1) (e + (i + 1) + B - xs.length - p) = p by unfold pOf; omega] at hk
          obtain ⟨r1, r2, r3⟩ := hk
          obtain ⟨l1, l2, l3⟩ := hl
          have t1 := hth (i + 1)
          exact ⟨r1.lt_of l1 t1.1, r2.lt_of l2 t1.2, r3.lt_of l3 t1.2⟩
        · have hoff : (B : Int) + 1 ≤ (((e - p : Nat) : Int) - ((xs.length - (i + 1) : Nat) : Int)).natAbs := by
            omega
          have a := cv_off_band sc0 hv T B hb xs gs e he none (i + 1) p hoff
          have b := cv_off_band sc0 hv T B hb xs gs e he (some .gapX) (i + 1) p hoff
          have c := cv_off_band sc0 hv T B hb xs gs e he (some .gapY) (i + 1) p hoff
          simp only [thr] at a b c
          have t1 := hth (i + 1)
          exact ⟨by omega, by omega, by omega⟩
    · rw [if_neg hin]
      exact deadRow_down sc0 hv T xs gs e he (i + 1) hi
        (deadRow_of_band sc0 hv T B hb xs gs e he (i + 1) hi
          (fun k _ hvk => by unfold Valid at hvk; omega))

/-- **The pruned kernel.**  Same guarantee as `bandEnd2_spec`. -/
theorem bandEndP_spec (T : Int) (B : Nat) (hb : BandOK sc0 T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) (sp : Nat → Bool)
    (hsp : ∀ j, sp j = true → 8 * j + 8 ≤ xs.length → ∀ p, p ≤ e →
      ((((e - p : Nat) : Int) - ((xs.length - 8 * j : Nat) : Int)).natAbs ≤ B) →
      ¬(p + 8 ≤ e ∧ ExactAt xs gs (8 * j) (8 * j + 8) p)) :
    match bandEndP T B sp rb gb e with
    | some A => A.size = 2 * B + 3 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k + 1]! (cv sc0 xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc0 T xs gs e 0 := by
  unfold bandEndP
  rw [hr.1]
  refine bandRowsP_spec T B hb xs gs e he rb gb hr hg sp hsp xs.length _ _ _ (Nat.le_refl _)
    ⟨by simp, by simp, by simp, ?_, ?_⟩ (fun k _ h => absurd h (Nat.lt_irrefl _))
  · rw [getElem!_pos _ 0 (by simp)]; simp
  · rw [getElem!_pos _ (2 * B + 2) (by simp)]; simp

/-! ## Thresholds from a count array -/

/-- `bandRowsP` with the spoiled-block counts read from `cnt` (`cnt[i / 8]` blocks above row `i`). -/
@[specialize] def bandRowsC (T : Int) (B : Nat) (cnt : Array Nat) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e : Nat) : Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      let h := cnt[i / 8]!
      let tN := T + 4 * (h : Int)
      match bandLoop sc0 tN (tN + (if h = 0 then 6 else 4)) rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRowsC T B cnt rb gb e i N X Y
        else none
    else none

@[specialize] def bandEndC (T : Int) (B : Nat) (cnt : Array Nat) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt)
    (e : Nat) : Option (Array Int) :=
  bandRowsC T B cnt rb gb e rb.size (Array.replicate (2 * B + 3) (T - 1))
    (Array.replicate (2 * B + 3) (T - 1)) (Array.replicate (2 * B + 3) (T - 1))

theorem bandRowsC_eq (T : Int) (B : Nat) (cnt : Array Nat) (sp : Nat → Bool) {Gt : Type} [GRead Gt]
    (rb : ByteArray) (gb : Gt) (e : Nat) (hcnt : ∀ i, i ≤ rb.size → cnt[i / 8]! = blocksAbove sp i) :
    ∀ i N X Y, i ≤ rb.size → bandRowsC T B cnt rb gb e i N X Y = bandRowsP T B sp rb gb e i N X Y := by
  intro i
  induction i with
  | zero =>
    intro N X Y hi
    rw [bandRowsC, bandRowsP]
    simp only [hcnt 0 hi, tNr, tGr]
    rfl
  | succ i ih =>
    intro N X Y hi
    rw [bandRowsC, bandRowsP]
    simp only [hcnt (i + 1) hi, tNr, tGr, ih _ _ _ (by omega)]
    rfl

theorem bandEndC_eq (T : Int) (B : Nat) (cnt : Array Nat) (sp : Nat → Bool) {Gt : Type} [GRead Gt]
    (rb : ByteArray) (gb : Gt) (e : Nat) (hcnt : ∀ i, i ≤ rb.size → cnt[i / 8]! = blocksAbove sp i) :
    bandEndC T B cnt rb gb e = bandEndP T B sp rb gb e := by
  unfold bandEndC bandEndP
  exact bandRowsC_eq T B cnt sp rb gb e hcnt _ _ _ _ (Nat.le_refl _)

/-- Spoiled-block counts: slot `q` is the number of spoiled blocks among `0 … q − 1`. -/
def prefCnt (A : Array Bool) : Array Nat :=
  (Array.range (A.size + 1)).map fun q => ((List.range q).filter fun j => A[j]?.getD false).length

theorem prefCnt_get (A : Array Bool) (n : Nat) (hA : A.size = n / 8) :
    ∀ i, i ≤ n → (prefCnt A)[i / 8]! = blocksAbove (fun j => A[j]?.getD false) i := by
  intro i hi
  have hq : i / 8 < A.size + 1 := by rw [hA]; have := Nat.div_le_div_right (c := 8) hi; omega
  unfold prefCnt blocksAbove
  rw [getElem!_pos _ _ (by simpa using hq)]
  simp

end MapSpec
