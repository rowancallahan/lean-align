import MapperBandKernel

/-!
Proof that `bandEnd` is faithful to the true cell values (`cv`): every
computed window score equals the true one when either is `≥ T`, and `none`
only when every window ending at `e` scores below `T`.
-/

namespace MapSpec

open AlignmentSpec

theorem cellVals_rel (sc : Scoring) (hv : ValidScoring sc) (T : Int) (xs gs : List Char)
    (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs) (hg : Encodes gb gs)
    (i p : Nat) (hi : i ≤ xs.length) (hp : p ≤ e) (dN xX yY : Int)
    (hdN : i < xs.length → p < e → Rel T dN (cv sc xs gs e none (i + 1) (p + 1)))
    (hxX : p < e → Rel (T - sc.gapOpen) xX (cv sc xs gs e (some .gapX) i (p + 1)))
    (hyY : i < xs.length → Rel (T - sc.gapOpen) yY (cv sc xs gs e (some .gapY) (i + 1) p)) :
    Rel T (cellVals sc rb gb i p (i == xs.length) (p == e) dN xX yY).1 (cv sc xs gs e none i p) ∧
    Rel (T - sc.gapOpen) (cellVals sc rb gb i p (i == xs.length) (p == e) dN xX yY).2.1
      (cv sc xs gs e (some .gapX) i p) ∧
    Rel (T - sc.gapOpen) (cellVals sc rb gb i p (i == xs.length) (p == e) dN xX yY).2.2
      (cv sc xs gs e (some .gapY) i p) := by
  obtain ⟨hM, hX, hO, hE⟩ := hv
  by_cases hin : i = xs.length
  · subst hin
    by_cases hpe : p = e
    · subst hpe
      simp only [cellVals, beq_self_eq_true, if_true, cv_last_end, GRead.get_bytes, GRead.size_bytes]
      exact ⟨Rel.refl _ _, Rel.refl _ _, Rel.refl _ _⟩
    · have hpe' : (p == e) = false := by simp [hpe]
      have hlt : p < e := by omega
      simp only [cellVals, beq_self_eq_true, if_true, hpe', Bool.false_eq_true, if_false,
        cv_last sc xs gs e he _ p hlt, gapXCost, GRead.get_bytes, GRead.size_bytes]
      simp only [reduceCtorEq, if_false]
      exact ⟨rel_add (hxX hlt) (by omega), rel_add (hxX hlt) (by omega),
        rel_add (hxX hlt) (by omega)⟩
  · have hin' : (i == xs.length) = false := by simp [hin]
    have hlt : i < xs.length := by omega
    by_cases hpe : p = e
    · subst hpe
      simp only [cellVals, hin', beq_self_eq_true, Bool.false_eq_true, if_false, if_true,
        cv_end sc xs gs p _ i hlt, gapYCost, GRead.get_bytes, GRead.size_bytes]
      simp only [reduceCtorEq, if_false]
      exact ⟨rel_add (hyY hlt) (by omega), rel_add (hyY hlt) (by omega),
        rel_add (hyY hlt) (by omega)⟩
    · have hpe' : (p == e) = false := by simp [hpe]
      have hplt : p < e := by omega
      have hpg : p < gs.length := by omega
      have hbeq := Encodes.beq_iff hr hg i p hlt hpg
      have hD : (if rb.get! i == gb.get! p then sc.matchScore else sc.mismatchScore) =
          diagCost sc xs[i] gs[p] := by
        rw [hbeq, diagCost]; simp
      have hDle : diagCost sc xs[i] gs[p] ≤ 0 := by unfold diagCost; split <;> omega
      simp only [cellVals, hin', hpe', Bool.false_eq_true, if_false, hD,
        cv_main sc xs gs e he _ i p hlt hplt, gapXCost, gapYCost, GRead.get_bytes, GRead.size_bytes]
      simp only [reduceCtorEq, if_false]
      have h1 := hdN hlt hplt
      have h2 := hxX hplt
      have h3 := hyY hlt
      exact ⟨rel_max3 h1 h2 h3 (by omega) (by omega) (by omega),
        rel_max3 h1 h2 h3 (by omega) (by omega) (by omega),
        rel_max3 h1 h2 h3 (by omega) (by omega) (by omega)⟩


/-! ## The row loop -/

def Valid (n B e i k : Nat) : Prop := n + k ≤ e + i + B ∧ i + B ≤ n + k

def pOf (n B e i k : Nat) : Nat := e + i + B - n - k

def CellRel (sc : Scoring) (T : Int) (B : Nat) (xs gs : List Char) (e i k : Nat)
    (N X Y : Array Int) : Prop :=
  Rel T N[k]! (cv sc xs gs e none i (pOf xs.length B e i k)) ∧
  Rel (T - sc.gapOpen) X[k]! (cv sc xs gs e (some .gapX) i (pOf xs.length B e i k)) ∧
  Rel (T - sc.gapOpen) Y[k]! (cv sc xs gs e (some .gapY) i (pOf xs.length B e i k))

def CellDead (sc : Scoring) (T : Int) (xs gs : List Char) (e i p : Nat) : Prop :=
  cv sc xs gs e none i p < T ∧
    cv sc xs gs e (some .gapX) i p < T - sc.gapOpen ∧ cv sc xs gs e (some .gapY) i p < T - sc.gapOpen

theorem bandRow_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) (i : Nat) (hi : i ≤ xs.length) :
    ∀ m k0 (N X Y : Array Int) (alive : Bool), 2 * B + 1 - k0 = m →
    N.size = 2 * B + 1 → X.size = 2 * B + 1 → Y.size = 2 * B + 1 →
    (∀ k, k < k0 → k < 2 * B + 1 → Valid xs.length B e i k → CellRel sc T B xs gs e i k N X Y) →
    (∀ k, k0 ≤ k → k < 2 * B + 1 → i < xs.length → Valid xs.length B e (i + 1) k →
      CellRel sc T B xs gs e (i + 1) k N X Y) →
    (alive = false → ∀ k, k < k0 → k < 2 * B + 1 → Valid xs.length B e i k →
      CellDead sc T xs gs e i (pOf xs.length B e i k)) →
    (bandRow sc T B rb gb e i k0 N X Y alive).1.size = 2 * B + 1 ∧
    (bandRow sc T B rb gb e i k0 N X Y alive).2.1.size = 2 * B + 1 ∧
    (bandRow sc T B rb gb e i k0 N X Y alive).2.2.1.size = 2 * B + 1 ∧
    (∀ k, k < 2 * B + 1 → Valid xs.length B e i k →
      CellRel sc T B xs gs e i k (bandRow sc T B rb gb e i k0 N X Y alive).1
        (bandRow sc T B rb gb e i k0 N X Y alive).2.1 (bandRow sc T B rb gb e i k0 N X Y alive).2.2.1) ∧
    ((bandRow sc T B rb gb e i k0 N X Y alive).2.2.2 = false → ∀ k, k < 2 * B + 1 →
      Valid xs.length B e i k → CellDead sc T xs gs e i (pOf xs.length B e i k)) := by
  have hO := hv.2.2.1
  have hn : rb.size = xs.length := hr.1
  intro m
  induction m with
  | zero =>
    intro k0 N X Y alive hm hN hX hY hold _ hdead
    rw [bandRow, if_neg (by omega)]
    exact ⟨hN, hX, hY, fun k hk hvk => hold k (by omega) hk hvk,
      fun ha k hk hvk => hdead ha k (by omega) hk hvk⟩
  | succ m ih =>
    intro k0 N X Y alive hm hN hX hY hnew hold hdead
    rw [bandRow, if_pos (by omega)]
    by_cases hvk : rb.size + k0 ≤ e + i + B ∧ i + B ≤ rb.size + k0
    · rw [if_pos hvk]
      simp only []
      rw [hn] at hvk ⊢
      have hvk' : Valid xs.length B e i k0 := hvk
      generalize hp : e + i + B - xs.length - k0 = p
      have hpp : pOf xs.length B e i k0 = p := hp
      have hpe : p ≤ e := by omega
      generalize hxX : (if k0 = 0 then T - 1 else X[k0 - 1]!) = xX
      generalize hyY : (if k0 + 1 < 2 * B + 1 then Y[k0 + 1]! else T - 1) = yY
      have hcell := cellVals_rel sc hv T xs gs e he rb gb hr hg i p hi hpe N[k0]! xX yY
        (fun hi1 hp1 => by
          have h := (hold k0 (Nat.le_refl _) (by omega) hi1 ⟨by omega, by omega⟩).1
          rwa [show pOf xs.length B e (i + 1) k0 = p + 1 by unfold pOf; omega] at h)
        (fun hp1 => by
          subst hxX
          split
          · apply Rel.of_below (by omega)
            have := cv_off_band sc hv T B hb xs gs e he (some .gapX) i (p + 1) (by omega)
            simpa [thr] using this
          · have h := (hnew (k0 - 1) (by omega) (by omega) ⟨by omega, by omega⟩).2.1
            rwa [show pOf xs.length B e i (k0 - 1) = p + 1 by unfold pOf; omega] at h)
        (fun hi1 => by
          subst hyY
          split
          · have h := (hold (k0 + 1) (by omega) (by omega) hi1 ⟨by omega, by omega⟩).2.2
            rwa [show pOf xs.length B e (i + 1) (k0 + 1) = p by unfold pOf; omega] at h
          · apply Rel.of_below (by omega)
            have := cv_off_band sc hv T B hb xs gs e he (some .gapY) (i + 1) p (by omega)
            simpa [thr] using this)
      generalize hv3 : cellVals sc rb gb i p (i == xs.length) (p == e) N[k0]! xX yY = v at hcell
      obtain ⟨c1, c2, c3⟩ := hcell
      apply ih (k0 + 1) _ _ _ _ (by omega) (by simp [hN])
        (by simp [hX]) (by simp [hY])
      · intro k hk hkW hvk2
        by_cases hkk : k = k0
        · subst hkk
          unfold CellRel
          rw [Array.getElem!_set!_self _ _ _ (by omega), Array.getElem!_set!_self _ _ _ (by omega),
            Array.getElem!_set!_self _ _ _ (by omega), hpp]
          exact ⟨c1, c2, c3⟩
        · have h := hnew k (by omega) hkW hvk2
          unfold CellRel at h ⊢
          rwa [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkk), Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkk),
            Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkk)]
      · intro k hk hkW hi1 hvk2
        have h := hold k (by omega) hkW hi1 hvk2
        unfold CellRel at h ⊢
        have hkk : k0 ≠ k := by omega
        rwa [Array.getElem!_set!_ne _ _ _ _ hkk, Array.getElem!_set!_ne _ _ _ _ hkk,
          Array.getElem!_set!_ne _ _ _ _ hkk]
      · intro ha k hk hkW hvk2
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha
        obtain ⟨⟨⟨ha0, h1⟩, h2⟩, h3⟩ := ha
        by_cases hkk : k = k0
        · subst hkk
          rw [hpp]
          exact ⟨c1.below (by omega), c2.below (by omega), c3.below (by omega)⟩
        · exact hdead ha0 k (by omega) hkW hvk2
    · rw [if_neg hvk]
      rw [hn] at hvk
      apply ih (k0 + 1) N X Y alive (by omega) hN hX hY
      · intro k hk hkW hvk2
        by_cases hkk : k = k0
        · subst hkk; exact absurd hvk2 hvk
        · exact hnew k (by omega) hkW hvk2
      · intro k hk hkW hi1 hvk2
        exact hold k (by omega) hkW hi1 hvk2
      · intro ha k hk hkW hvk2
        by_cases hkk : k = k0
        · subst hkk; exact absurd hvk2 hvk
        · exact hdead ha k (by omega) hkW hvk2


/-! ## All rows -/

theorem deadRow_of_band (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat)
    (hb : BandOK sc T B) (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (i : Nat) (hi : i ≤ xs.length)
    (h : ∀ k, k < 2 * B + 1 → Valid xs.length B e i k →
      CellDead sc T xs gs e i (pOf xs.length B e i k)) :
    DeadRow sc T xs gs e i := by
  intro p hp
  by_cases hin : xs.length + p ≤ e + i + B ∧ e + i ≤ xs.length + p + B
  · have h1 := h (e + i + B - xs.length - p) (by omega) ⟨by omega, by omega⟩
    rwa [show pOf xs.length B e i (e + i + B - xs.length - p) = p by unfold pOf; omega] at h1
  · have hoff : (B : Int) + 1 ≤ (((e - p : Nat) : Int) - ((xs.length - i : Nat) : Int)).natAbs := by
      omega
    have a := cv_off_band sc hv T B hb xs gs e he none i p hoff
    have b := cv_off_band sc hv T B hb xs gs e he (some .gapX) i p hoff
    have c := cv_off_band sc hv T B hb xs gs e he (some .gapY) i p hoff
    simp only [thr] at a b c
    exact ⟨a, b, c⟩

theorem bandRows_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) :
    ∀ i (N X Y : Array Int), i ≤ xs.length →
    N.size = 2 * B + 1 → X.size = 2 * B + 1 → Y.size = 2 * B + 1 →
    (∀ k, k < 2 * B + 1 → i < xs.length → Valid xs.length B e (i + 1) k →
      CellRel sc T B xs gs e (i + 1) k N X Y) →
    match bandRows sc T B rb gb e i N X Y with
    | some A => A.size = 2 * B + 1 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k]! (cv sc xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc T xs gs e 0 := by
  intro i
  induction i with
  | zero =>
    intro N X Y hi hN hX hY hold
    have h := bandRow_spec sc hv T B hb xs gs e he rb gb hr hg 0 hi _ 0 N X Y false rfl hN hX hY
      (fun k hk => absurd hk (Nat.not_lt_zero _)) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
      (fun _ k hk => absurd hk (Nat.not_lt_zero _))
    rw [bandRows]
    revert h
    generalize bandRow sc T B rb gb e 0 0 N X Y false = r
    obtain ⟨N', X', Y', alive⟩ := r
    intro h
    obtain ⟨hN', -, -, hrel, hdead⟩ := h
    cases alive with
    | true => exact ⟨hN', fun k hk hvk => (hrel k hk hvk).1⟩
    | false => exact deadRow_of_band sc hv T B hb xs gs e he 0 hi (hdead rfl)
  | succ i ih =>
    intro N X Y hi hN hX hY hold
    have h := bandRow_spec sc hv T B hb xs gs e he rb gb hr hg (i + 1) hi _ 0 N X Y false rfl hN hX hY
      (fun k hk => absurd hk (Nat.not_lt_zero _)) (fun k _ hk hi1 hvk => hold k hk hi1 hvk)
      (fun _ k hk => absurd hk (Nat.not_lt_zero _))
    rw [bandRows]
    revert h
    generalize bandRow sc T B rb gb e (i + 1) 0 N X Y false = r
    obtain ⟨N', X', Y', alive⟩ := r
    intro h
    obtain ⟨hN', hX', hY', hrel, hdead⟩ := h
    cases alive with
    | true =>
      exact ih N' X' Y' (by omega) hN' hX' hY' (fun k hk _ hvk => hrel k hk hvk)
    | false =>
      exact deadRow_down sc hv T xs gs e he (i + 1) hi
        (deadRow_of_band sc hv T B hb xs gs e he (i + 1) hi (hdead rfl))

/-- **The kernel.**  With `ValidScoring sc` and a band `B` that no walk scoring
`≥ T` can leave, `bandEnd` either returns one capped score per window ending
at `e` (exact when either it or the true score is `≥ T`), or `none`, and then
every window ending at `e` scores below `T`. -/
theorem bandEnd_spec (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat) (hb : BandOK sc T B)
    (xs gs : List Char) (e : Nat) (he : e ≤ gs.length) (rb gb : ByteArray) (hr : Encodes rb xs)
    (hg : Encodes gb gs) :
    match bandEnd sc T B rb gb e with
    | some A => A.size = 2 * B + 1 ∧ ∀ k, k < 2 * B + 1 → Valid xs.length B e 0 k →
        Rel T A[k]! (cv sc xs gs e none 0 (pOf xs.length B e 0 k))
    | none => DeadRow sc T xs gs e 0 := by
  unfold bandEnd
  rw [hr.1]
  exact bandRows_spec sc hv T B hb xs gs e he rb gb hr hg xs.length _ _ _ (Nat.le_refl _)
    (by simp) (by simp) (by simp) (fun k _ h => absurd h (Nat.lt_irrefl _))

end MapSpec

#print axioms MapSpec.bandEnd_spec
