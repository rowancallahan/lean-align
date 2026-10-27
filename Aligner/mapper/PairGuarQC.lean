import PairGuarQ

/-!
# `pairGQ`, part (c): the early-stop fold, proved

* (c1) `stepP_inv`, `foldP_inv`, `goP_spec`: the fold keeps `InvQ`, and `goP` folds every pair of
  its hits unless the result stops at the bound;
* (c2) `goP2_spec`: phase 0 (bound 0) then phase 1 (bound `U1 ≤ 0`);
* (c3) `ansOk`: then a pair is found iff one exists, and the answer is `bestPairD`.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-! ## (c1) The fold -/

theorem stepP_inv (dc : Nat → Nat) (D : List PairHit) (s : Option PairHit × Bool) (p : PairHit)
    (h : InvQ dc D s) : InvQ dc (D ++ [p]) (stepP dc s p) := by
  obtain ⟨h0, h1⟩ := h
  obtain ⟨sb, st⟩ := s
  cases sb with
  | none =>
    have hD := h0 rfl
    subst hD
    refine ⟨fun h => (by cases h), fun b hb => ?_⟩
    simp only [stepP, Option.some.injEq] at hb
    subst hb
    refine ⟨by simp, fun q hq => by simp at hq; subst hq; exact Int.le_refl _, ?_⟩
    simp [stepP, samePlP]
  | some b =>
    obtain ⟨hbD, hmax, htie⟩ := h1 b rfl
    refine ⟨fun h => ?_, fun c hc => ?_⟩
    · simp only [stepP] at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
    · simp only [stepP] at hc ⊢
      by_cases hlt : pairScoreD dc b < pairScoreD dc p
      · simp only [hlt, if_true, Option.some.injEq] at hc
        subst hc
        refine ⟨by simp, fun q hq => ?_, ?_⟩
        · simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | rfl
          · have := hmax q hq; omega
          · exact Int.le_refl _
        · simp only [hlt, if_true, Bool.false_eq_true, false_iff, not_exists, not_and,
            List.mem_append, List.mem_singleton]
          rintro q (hq | rfl) he
          · have := hmax q hq; omega
          · simp [samePlP]
      · simp only [hlt, if_false] at hc ⊢
        by_cases hti : pairScoreD dc p = pairScoreD dc b ∧ samePlP p b = false
        · simp only [hti, and_self, if_true, Option.some.injEq] at hc ⊢
          subst hc
          refine ⟨by simp [hbD], fun q hq => ?_, ?_⟩
          · simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact hmax q hq
            · omega
          · simp only [true_iff]
            exact ⟨p, by simp, hti.1, hti.2⟩
        · simp only [hti, if_false] at hc ⊢
          cases hc
          refine ⟨by simp [hbD], fun q hq => ?_, ?_⟩
          · simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact hmax q hq
            · omega
          · rw [htie]
            constructor
            · rintro ⟨q, hq, he⟩; exact ⟨q, by simp [hq], he⟩
            · rintro ⟨q, hq, he⟩
              simp only [List.mem_append, List.mem_singleton] at hq
              rcases hq with hq | rfl
              · exact ⟨q, hq, he⟩
              · exact absurd he hti

theorem foldP_inv (dc : Nat → Nat) (l : List PairHit) :
    ∀ (D : List PairHit) (s : Option PairHit × Bool), InvQ dc D s → InvQ dc (D ++ l) (l.foldl (stepP dc) s) := by
  induction l with
  | nil => intro D s h; simpa using h
  | cons p l ih =>
    intro D s h
    have := ih (D ++ [p]) (stepP dc s p) (stepP_inv dc D s p h)
    simpa [List.append_assoc] using this

/-- (c1) `goP`: the pairs folded (`D'`) are pairs of `xs`; every pair of `xs` is folded unless the
result stops at `U`. -/
theorem goP_spec (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U : Int) :
    ∀ (xs : List (Placement × Int)) (D : List PairHit) (s : Option PairHit × Bool), InvQ dc D s →
      ∃ D', InvQ dc (D ++ D') (goP dc f U xs s) ∧ (∀ p ∈ D', ∃ x ∈ xs, p ∈ f x) ∧
        ∀ x ∈ xs, ∀ p ∈ f x, p ∈ D' ∨ stopP dc U (goP dc f U xs s) = true := by
  intro xs
  induction xs with
  | nil => intro D s h; exact ⟨[], by simpa [goP] using h, by simp, by simp⟩
  | cons x xs ih =>
    intro D s h
    by_cases hs : stopP dc U s = true
    · refine ⟨[], by simpa [goP, hs] using h, by simp, fun _ _ _ _ => Or.inr ?_⟩
      simp [goP, hs]
    · have hf := foldP_inv dc (f x) D s h
      obtain ⟨D'', hI, hm, hc⟩ := ih (D ++ f x) _ hf
      have hg : goP dc f U (x :: xs) s = goP dc f U xs ((f x).foldl (stepP dc) s) := by
        simp [goP, hs]
      rw [hg]
      refine ⟨f x ++ D'', by simpa [List.append_assoc] using hI, fun p hp => ?_, fun y hy p hp => ?_⟩
      · rcases List.mem_append.mp hp with hp | hp
        · exact ⟨x, List.mem_cons_self, hp⟩
        · obtain ⟨y, hy, hpy⟩ := hm p hp
          exact ⟨y, List.mem_cons_of_mem _ hy, hpy⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl (List.mem_append_left _ hp)
        · rcases hc y hy p hp with h' | h'
          · exact Or.inl (List.mem_append_right _ h')
          · exact Or.inr h'

/-! ## (c2) The two phases -/

theorem stopP_mono (dc : Nat → Nat) (U U' : Int) (hU : U' ≤ U) (s : Option PairHit × Bool)
    (h : stopP dc U s = true) : stopP dc U' s = true := by
  unfold stopP at h ⊢
  split at h
  · cases h
  · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨h1, by omega⟩

theorem goP_stop (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U : Int) (s : Option PairHit × Bool)
    (h : stopP dc U s = true) : ∀ xs, goP dc f U xs s = s
  | [] => rfl
  | _ :: _ => by simp [goP, h]

/-- (c2) Phase 0 (bound 0) then phase 1 (bound `U1 ≤ 0`): every pair is folded, or lies below a
bound at which the result stops. -/
theorem goP2_spec (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U1 : Int) (hU : U1 ≤ 0)
    (l0 l1 : List (Placement × Int))
    (h0 : ∀ x ∈ l0, ∀ p ∈ f x, pairScoreD dc p ≤ 0) (h1 : ∀ x ∈ l1, ∀ p ∈ f x, pairScoreD dc p ≤ U1) :
    ∃ D, InvQ dc D (goP dc f U1 l1 (goP dc f 0 l0 (none, false))) ∧
      (∀ p ∈ D, ∃ x ∈ l0 ++ l1, p ∈ f x) ∧
      ∀ x ∈ l0 ++ l1, ∀ p ∈ f x, p ∈ D ∨
        ∃ U, pairScoreD dc p ≤ U ∧ stopP dc U (goP dc f U1 l1 (goP dc f 0 l0 (none, false))) = true := by
  have hI0 : InvQ dc [] ((none, false) : Option PairHit × Bool) :=
    ⟨fun _ => rfl, fun b hb => by cases hb⟩
  obtain ⟨D0, hI1, hm0, hc0⟩ := goP_spec dc f 0 l0 [] (none, false) hI0
  obtain ⟨D1, hI2, hm1, hc1⟩ := goP_spec dc f U1 l1 ([] ++ D0) _ hI1
  refine ⟨[] ++ D0 ++ D1, hI2, fun p hp => ?_, fun x hx p hp => ?_⟩
  · simp only [List.nil_append, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, hx, h⟩ := hm0 p hp; exact ⟨x, List.mem_append_left _ hx, h⟩
    · obtain ⟨x, hx, h⟩ := hm1 p hp; exact ⟨x, List.mem_append_right _ hx, h⟩
  · rcases List.mem_append.mp hx with hx | hx
    · rcases hc0 x hx p hp with h | h
      · exact Or.inl (by simp [h])
      · refine Or.inr ⟨0, h0 x hx p hp, ?_⟩
        rw [goP_stop dc f U1 _ (stopP_mono dc 0 U1 hU _ h) l1]
        exact h
    · rcases hc1 x hx p hp with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨U1, h1 x hx p hp, h⟩

/-! ## (c3) The answer -/

theorem find?_eq_some_of_unique {α : Type} (P : α → Bool) (l : List α) (b : α) (hb : b ∈ l)
    (hP : P b = true) (hu : ∀ x ∈ l, P x = true → x = b) : l.find? P = some b := by
  cases h : l.find? P with
  | none => exact absurd hP (by simpa using List.find?_eq_none.mp h b hb)
  | some x =>
    rw [hu x (List.mem_of_find?_eq_some h) (List.find?_some h)]

/-- (c3) The pairs at score `≥ W` are `All`; those folded (`D`) are among them, the others lie below a
bound where the fold stopped.  Then a pair was found iff one exists, and the answer
(`none` on a tie) is `bestPairD`. -/
theorem ansOk (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) (f1 : ScoreFun h1)
    (f2 : ScoreFun h2) (W : Int) (All : List PairHit)
    (hA : ∀ p, p ∈ All ↔ p ∈ properPairs sl lo hi h1 h2 ∧ W ≤ pairScoreD dc p)
    (D : List PairHit) (s : Option PairHit × Bool) (hI : InvQ dc D s) (hD : ∀ p ∈ D, p ∈ All)
    (hrest : ∀ p ∈ All, p ∈ D ∨ ∃ U, pairScoreD dc p ≤ U ∧ stopP dc U s = true) :
    (s.1.isSome = true ↔ ∃ w ∈ properPairs sl lo hi h1 h2, W ≤ pairScoreD dc w) ∧
      (s.1.isSome = true → (if s.2 then none else s.1) = bestPairD dc sl lo hi h1 h2) := by
  obtain ⟨hI0, hI1⟩ := hI
  obtain ⟨sb, st⟩ := s
  simp only at hI0 hI1 ⊢
  cases sb with
  | none =>
    have hD0 := hI0 rfl
    subst hD0
    refine ⟨?_, fun h => by cases h⟩
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro w hw hW
    rcases hrest w ((hA w).2 ⟨hw, hW⟩) with h | ⟨U, -, h⟩
    · cases h
    · simp [stopP] at h
  | some b =>
    obtain ⟨hbD, hmax, htie⟩ := hI1 b rfl
    have hbA := (hA b).1 (hD b hbD)
    refine ⟨?_, fun _ => ?_⟩
    · simp only [Option.isSome_some, true_iff]
      exact ⟨b, hbA.1, hbA.2⟩
    -- every proper pair scores at most `b`, strictly unless at `b`'s placements when no tie
    have hall : ∀ p ∈ properPairs sl lo hi h1 h2, pairScoreD dc p ≤ pairScoreD dc b ∧
        (st = false → (p.1.1 = b.1.1 ∧ p.2.1 = b.2.1) ∨ pairScoreD dc p < pairScoreD dc b) := by
      intro p hp
      by_cases hW : W ≤ pairScoreD dc p
      · rcases hrest p ((hA p).2 ⟨hp, hW⟩) with hpD | ⟨U, hpU, hst⟩
        · refine ⟨hmax p hpD, fun hf => ?_⟩
          by_cases he : pairScoreD dc p = pairScoreD dc b
          · by_cases hs : samePlP p b = false
            · have := htie.2 ⟨p, hpD, he, hs⟩
              rw [hf] at this; cases this
            · left; simpa [samePlP] using hs
          · right; have := hmax p hpD; omega
        · simp only [stopP, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hst
          refine ⟨by omega, fun hf => Or.inr ?_⟩
          subst hf; simp at hst; omega
      · have := hbA.2
        exact ⟨by omega, fun _ => Or.inr (by omega)⟩
    unfold bestPairD
    cases st with
    | true =>
      obtain ⟨q, hqD, hqe, hqs⟩ := htie.1 rfl
      have hqP := ((hA q).1 (hD q hqD)).1
      simp only [if_true]
      symm
      apply List.find?_eq_none.mpr
      intro p hp hpr
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpr
      have hpb := (hall p hp).1
      have e1 := hpr b hbA.1
      have e2 := hpr q hqP
      simp only [samePlP, decide_eq_false_iff_not] at hqs
      rcases e1 with e1 | e1
      · omega
      rcases e2 with e2 | e2
      · omega
      exact hqs ⟨e2.1.trans e1.1.symm, e2.2.trans e1.2.symm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false]
      symm
      apply find?_eq_some_of_unique _ _ b hbA.1
      · simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        intro p' hp'
        rcases (hall p' hp').2 rfl with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro p hp hpr
        simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpr
        rcases hpr b hbA.1 with e | e
        · have := (hall p hp).1; omega
        · have mp := mem_properPairs.mp hp
          have mb := mem_properPairs.mp hbA.1
          have s1 := f1 _ mp.1 _ mb.1 e.1.symm
          have s2 := f2 _ mp.2.1 _ mb.2.1 e.2.symm
          obtain ⟨⟨pa, pas⟩, ⟨pb, pbs⟩⟩ := p
          obtain ⟨⟨ba, bas⟩, ⟨bb, bbs⟩⟩ := b
          simp only at e s1 s2
          rw [e.1, e.2, s1, s2]

end MapSpec.Fast

#print axioms MapSpec.Fast.stepP_inv
#print axioms MapSpec.Fast.foldP_inv
#print axioms MapSpec.Fast.goP_spec
#print axioms MapSpec.Fast.goP2_spec
#print axioms MapSpec.Fast.ansOk
