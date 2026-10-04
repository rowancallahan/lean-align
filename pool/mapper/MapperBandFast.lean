import MapperBandProof

/-!
`bandEnd2`: the same pass as `bandEnd` with less work per cell.  Rows are
padded with one sentinel slot on each side (cell `k` lives in slot `k + 1`;
slots `0` and `2B + 2` always hold `T - 1`), and each row loops over exactly
its valid cells, so a cell does no bounds or validity test.
Proved with the same invariant as `bandEnd` (`bandEnd2_spec`).
-/

namespace MapSpec

open AlignmentSpec

/-- Cells `k, k+1, …, hi` of row `i`; `p` is the genome position of cell `k`. -/
def bandLoop (sc : Scoring) (T To : Int) (rb gb : ByteArray) (e i : Nat) (lastRow : Bool) (hi : Nat) :
    Nat → Nat → Array Int → Array Int → Array Int → Bool → Array Int × Array Int × Array Int × Bool
  | k, p, N, X, Y, alive =>
    if k ≤ hi then
      let v := cellVals sc rb gb i p lastRow (p == e) N[k + 1]! X[k]! Y[k + 2]!
      bandLoop sc T To rb gb e i lastRow hi (k + 1) (p - 1) (N.set! (k + 1) v.1)
        (X.set! (k + 1) v.2.1) (Y.set! (k + 1) v.2.2)
        (alive || decide (T ≤ v.1) || decide (To ≤ v.2.1) || decide (To ≤ v.2.2))
    else (N, X, Y, alive)
  termination_by k => hi + 1 - k

/-- Rows `i, i-1, …, 0`; `none` as soon as a row is dead. -/
def bandRows2 (sc : Scoring) (T : Int) (B : Nat) (rb gb : ByteArray) (e : Nat) :
    Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      match bandLoop sc T (T - sc.gapOpen) rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRows2 sc T B rb gb e i N X Y
        else none
    else none

/-- All windows ending at `e`: slot `k + 1` is the capped score of the window
of length `n + k - B`; `none` = every one of them scores below `T`. -/
def bandEnd2 (sc : Scoring) (T : Int) (B : Nat) (rb gb : ByteArray) (e : Nat) : Option (Array Int) :=
  bandRows2 sc T B rb gb e rb.size (Array.replicate (2 * B + 3) (T - 1))
    (Array.replicate (2 * B + 3) (T - 1)) (Array.replicate (2 * B + 3) (T - 1))

/-! ## Proof -/

def CellRelP (sc : Scoring) (T : Int) (B : Nat) (xs gs : List Char) (e i k : Nat)
    (N X Y : Array Int) : Prop :=
  Rel T N[k + 1]! (cv sc xs gs e none i (pOf xs.length B e i k)) ∧
  Rel (T - sc.gapOpen) X[k + 1]! (cv sc xs gs e (some .gapX) i (pOf xs.length B e i k)) ∧
  Rel (T - sc.gapOpen) Y[k + 1]! (cv sc xs gs e (some .gapY) i (pOf xs.length B e i k))

/-- Shape of a row: sizes and the two sentinels. -/
def RowShape (T : Int) (B : Nat) (N X Y : Array Int) : Prop :=
  N.size = 2 * B + 3 ∧ X.size = 2 * B + 3 ∧ Y.size = 2 * B + 3 ∧
  X[0]! = T - 1 ∧ Y[2 * B + 2]! = T - 1

theorem RowShape.set (T : Int) (B : Nat) (N X Y : Array Int) (h : RowShape T B N X Y) (j : Nat)
    (hj1 : 1 ≤ j) (hj2 : j ≤ 2 * B + 1) (a b c : Int) :
    RowShape T B (N.set! j a) (X.set! j b) (Y.set! j c) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simp [h1], by simp [h2], by simp [h3], ?_, ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact h4
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact h5

theorem bandLoop_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) (i : Nat) (hi : i ≤ xs.length) (hiK : Nat)
    (hvalid : ∀ k, k < 2 * B + 1 → (Valid xs.length B e i k ↔ i + B - xs.length ≤ k ∧ k ≤ hiK))
    (hhi : hiK < 2 * B + 1) :
    ∀ m k0 p (N X Y : Array Int) (alive : Bool), hiK + 1 - k0 = m →
    i + B - xs.length ≤ k0 → k0 ≤ hiK + 1 →
    (k0 ≤ hiK → p = pOf xs.length B e i k0) →
    RowShape T B N X Y →
    (∀ k, k < k0 → k < 2 * B + 1 → Valid xs.length B e i k → CellRelP sc T B xs gs e i k N X Y) →
    (∀ k, k0 ≤ k → k < 2 * B + 1 → i < xs.length → Valid xs.length B e (i + 1) k →
      CellRelP sc T B xs gs e (i + 1) k N X Y) →
    (alive = false → ∀ k, k < k0 → k < 2 * B + 1 → Valid xs.length B e i k →
      CellDead sc T xs gs e i (pOf xs.length B e i k)) →
    let r := bandLoop sc T (T - sc.gapOpen) rb gb e i (i == xs.length) hiK k0 p N X Y alive
    RowShape T B r.1 r.2.1 r.2.2.1 ∧
    (∀ k, k < 2 * B + 1 → Valid xs.length B e i k → CellRelP sc T B xs gs e i k r.1 r.2.1 r.2.2.1) ∧
    (r.2.2.2 = false → ∀ k, k < 2 * B + 1 →
      Valid xs.length B e i k → CellDead sc T xs gs e i (pOf xs.length B e i k)) := by
  have hO := hv.2.2.1
  intro m
  induction m with
  | zero =>
    intro k0 p N X Y alive hm hlo hk0 _ hshape hnew _ hdead
    simp only
    rw [bandLoop, if_neg (by omega)]
    refine ⟨hshape, fun k hk hvk => hnew k ?_ hk hvk, fun ha k hk hvk => hdead ha k ?_ hk hvk⟩
    · have := ((hvalid k hk).mp hvk).2; omega
    · have := ((hvalid k hk).mp hvk).2; omega
  | succ m ih =>
    intro k0 p N X Y alive hm hlo hk0 hp hshape hnew hold hdead
    simp only
    rw [bandLoop, if_pos (by omega)]
    have hp' := hp (by omega)
    have hvk' : Valid xs.length B e i k0 := (hvalid k0 (by omega)).mpr ⟨hlo, by omega⟩
    have hvk := hvk'
    unfold Valid at hvk
    have hpp : pOf xs.length B e i k0 = p := hp'.symm
    have hpe : p ≤ e := by unfold pOf at hp'; omega
    obtain ⟨hN, hX, hY, hX0, hYW⟩ := hshape
    have hcell := cellVals_rel sc hv T xs gs e he rb gb hr hg i p hi hpe N[k0 + 1]! X[k0]! Y[k0 + 2]!
      (fun hi1 hp1 => by
        have h := (hold k0 (Nat.le_refl _) (by omega) hi1 ⟨by omega, by unfold pOf at hp'; omega⟩).1
        rwa [show pOf xs.length B e (i + 1) k0 = p + 1 by unfold pOf at hp' ⊢; omega] at h)
      (fun hp1 => by
        by_cases hk : k0 = 0
        · subst hk
          rw [hX0]
          apply Rel.of_below (by omega)
          have := cv_off_band sc hv T B hb xs gs e he (some .gapX) i (p + 1)
            (by unfold pOf at hp'; omega)
          simpa [thr] using this
        · have h := (hnew (k0 - 1) (by omega) (by omega)
            ⟨by omega, by unfold pOf at hp'; omega⟩).2.1
          rw [show k0 - 1 + 1 = k0 by omega,
            show pOf xs.length B e i (k0 - 1) = p + 1 by unfold pOf at hp' ⊢; omega] at h
          exact h)
      (fun hi1 => by
        by_cases hk : k0 + 1 < 2 * B + 1
        · have h := (hold (k0 + 1) (by omega) hk hi1 ⟨by omega, by omega⟩).2.2
          rwa [show pOf xs.length B e (i + 1) (k0 + 1) = p by unfold pOf at hp' ⊢; omega] at h
        · rw [show k0 + 2 = 2 * B + 2 by omega, hYW]
          apply Rel.of_below (by omega)
          have := cv_off_band sc hv T B hb xs gs e he (some .gapY) (i + 1) p
            (by unfold pOf at hp'; omega)
          simpa [thr] using this)
    have hn1 : (i == xs.length) = (i == xs.length) := rfl
    generalize hv3 : cellVals sc rb gb i p (i == xs.length) (p == e) N[k0 + 1]! X[k0]! Y[k0 + 2]! = v
      at hcell
    obtain ⟨c1, c2, c3⟩ := hcell
    apply ih (k0 + 1) (p - 1) _ _ _ _ (by omega) (by omega) (by omega)
      (fun hk => by unfold pOf at hp' ⊢; omega)
      (RowShape.set T B N X Y ⟨hN, hX, hY, hX0, hYW⟩ (k0 + 1) (by omega) (by omega) _ _ _)
    · intro k hk hkW hvk2
      by_cases hkk : k = k0
      · subst hkk
        unfold CellRelP
        rw [Array.getElem!_set!_self _ _ _ (by omega), Array.getElem!_set!_self _ _ _ (by omega),
          Array.getElem!_set!_self _ _ _ (by omega), hpp]
        exact ⟨c1, c2, c3⟩
      · have h := hnew k (by omega) hkW hvk2
        unfold CellRelP at h ⊢
        have hne : k0 + 1 ≠ k + 1 := by omega
        rwa [Array.getElem!_set!_ne _ _ _ _ hne, Array.getElem!_set!_ne _ _ _ _ hne,
          Array.getElem!_set!_ne _ _ _ _ hne]
    · intro k hk hkW hi1 hvk2
      have h := hold k (by omega) hkW hi1 hvk2
      unfold CellRelP at h ⊢
      have hne : k0 + 1 ≠ k + 1 := by omega
      rwa [Array.getElem!_set!_ne _ _ _ _ hne, Array.getElem!_set!_ne _ _ _ _ hne,
        Array.getElem!_set!_ne _ _ _ _ hne]
    · intro ha k hk hkW hvk2
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha
      obtain ⟨⟨⟨ha0, h1⟩, h2⟩, h3⟩ := ha
      by_cases hkk : k = k0
      · subst hkk
        rw [hpp]
        exact ⟨c1.below (by omega), c2.below (by omega), c3.below (by omega)⟩
      · exact hdead ha0 k (by omega) hkW hvk2


theorem bandRows2_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) :
    ∀ i (N X Y : Array Int), i ≤ xs.length → RowShape T B N X Y →
    (∀ k, k < 2 * B + 1 → i < xs.length → Valid xs.length B e (i + 1) k →
      CellRelP sc T B xs gs e (i + 1) k N X Y) →
    match bandRows2 sc T B rb gb e i N X Y with
    | some A => A.size = 2 * B + 3 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k + 1]! (cv sc xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc T xs gs e 0 := by
  have hn : rb.size = xs.length := hr.1
  intro i
  induction i with
  | zero =>
    intro N X Y hi hshape hold
    rw [bandRows2]
    by_cases hin : rb.size ≤ e + 0 + B
    · rw [if_pos hin]
      have h := bandLoop_spec sc hv T B hb xs gs e he rb gb hr hg 0 hi (min (2 * B) (e + 0 + B - xs.length))
        (fun k hk => by unfold Valid; omega) (by omega) _ (0 + B - xs.length) (e + 0 + B - xs.length - (0 + B - xs.length))
        N X Y false rfl (Nat.le_refl _) (by omega) (fun _ => by unfold pOf; omega) hshape
        (fun k hk _ hvk => by unfold Valid at hvk; omega) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
        (fun _ k hk _ hvk => by unfold Valid at hvk; omega)
      rw [hn] at hin ⊢
      revert h
      generalize bandLoop sc T (T - sc.gapOpen) rb gb e 0 (0 == xs.length) (min (2 * B) (e + 0 + B - xs.length))
        (0 + B - xs.length) (e + 0 + B - xs.length - (0 + B - xs.length)) N X Y false = r
      obtain ⟨N', X', Y', alive⟩ := r
      intro h
      obtain ⟨hshape', hrel, hdead⟩ := h
      cases alive with
      | true => exact ⟨hshape'.1, fun k hk hvk => (hrel k hk hvk).1⟩
      | false => exact deadRow_of_band sc hv T B hb xs gs e he 0 hi (hdead rfl)
    · rw [if_neg hin]
      exact deadRow_of_band sc hv T B hb xs gs e he 0 hi
        (fun k _ hvk => by unfold Valid at hvk; omega)
  | succ i ih =>
    intro N X Y hi hshape hold
    rw [bandRows2]
    by_cases hin : rb.size ≤ e + (i + 1) + B
    · rw [if_pos hin]
      have h := bandLoop_spec sc hv T B hb xs gs e he rb gb hr hg (i + 1) hi
        (min (2 * B) (e + (i + 1) + B - xs.length))
        (fun k hk => by unfold Valid; omega) (by omega) _ (i + 1 + B - xs.length)
        (e + (i + 1) + B - xs.length - (i + 1 + B - xs.length))
        N X Y false rfl (Nat.le_refl _) (by omega) (fun _ => by unfold pOf; omega) hshape
        (fun k hk _ hvk => by unfold Valid at hvk; omega) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
        (fun _ k hk _ hvk => by unfold Valid at hvk; omega)
      rw [hn] at hin ⊢
      revert h
      generalize bandLoop sc T (T - sc.gapOpen) rb gb e (i + 1) (i + 1 == xs.length)
        (min (2 * B) (e + (i + 1) + B - xs.length)) (i + 1 + B - xs.length)
        (e + (i + 1) + B - xs.length - (i + 1 + B - xs.length)) N X Y false = r
      obtain ⟨N', X', Y', alive⟩ := r
      intro h
      obtain ⟨hshape', hrel, hdead⟩ := h
      cases alive with
      | true =>
        exact ih N' X' Y' (by omega) hshape' (fun k hk _ hvk => hrel k hk hvk)
      | false =>
        exact deadRow_down sc hv T xs gs e he (i + 1) hi
          (deadRow_of_band sc hv T B hb xs gs e he (i + 1) hi (hdead rfl))
    · rw [if_neg hin]
      exact deadRow_down sc hv T xs gs e he (i + 1) hi
        (deadRow_of_band sc hv T B hb xs gs e he (i + 1) hi
          (fun k _ hvk => by unfold Valid at hvk; omega))

/-- **The fast kernel.**  Same guarantee as `bandEnd_spec`; the score of the
window of length `n + k - B` is in slot `k + 1`. -/
theorem bandEnd2_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) :
    match bandEnd2 sc T B rb gb e with
    | some A => A.size = 2 * B + 3 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k + 1]! (cv sc xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc T xs gs e 0 := by
  unfold bandEnd2
  rw [hr.1]
  refine bandRows2_spec sc hv T B hb xs gs e he rb gb hr hg xs.length _ _ _ (Nat.le_refl _)
    ⟨by simp, by simp, by simp, ?_, ?_⟩ (fun k _ h => absurd h (Nat.lt_irrefl _))
  · rw [getElem!_pos _ 0 (by simp)]; simp
  · rw [getElem!_pos _ (2 * B + 2) (by simp)]; simp

end MapSpec

#print axioms MapSpec.bandEnd2_spec
