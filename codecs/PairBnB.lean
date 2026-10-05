import PairSpecU
import FastMapper

/-!
# Branch and bound on the pair score (`pairSpecUT`)

Rowan's rule: once some proper pair `w` with score `W` is known (summed mate scores
minus the distance cost), only hits with score `≥ W` can be in a pair that beats or
ties it, since mate scores are `≤ 0` and the distance cost is `≥ 0`.  So `pairSpecUT`
at caps `T1, T2` equals `pairSpecUT` at the tighter caps `max T1 W, max T2 W`
(`pairSpecUT_bnb`): each mate can be searched again at the smaller penalty cap, where
more seeds stay clean and the filter is more selective.

The list lemma `bestPairD_restrict` needs only that the scores are `≤ 0` and that a
placement determines its score in each hit list.
-/

namespace MapSpec

open AlignmentSpec

theorem mem_properPairs {sl lo hi : Nat} {h1 h2 : List (Placement × Int)} {p : PairHit} :
    p ∈ properPairs sl lo hi h1 h2 ↔ p.1 ∈ h1 ∧ p.2 ∈ h2 ∧ properPairU sl lo hi p.1.1 p.2.1 = true := by
  obtain ⟨a, b⟩ := p
  simp only [properPairs, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨a', ha', b', ⟨hb', hp⟩, he⟩
    cases he
    exact ⟨ha', hb', hp⟩
  · rintro ⟨ha, hb, hp⟩
    exact ⟨a, ha, b, ⟨hb, hp⟩, rfl⟩

theorem properPairs_filter (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (q : Placement × Int → Bool) :
    properPairs sl lo hi (h1.filter q) (h2.filter q) =
      (properPairs sl lo hi h1 h2).filter (fun p => q p.1 && q p.2) := by
  induction h1 with
  | nil => simp [properPairs]
  | cons a t ih =>
    have hc : properPairs sl lo hi (a :: t) h2 =
        (h2.filter fun b => properPairU sl lo hi a.1 b.1).map (fun b => (a, b)) ++
          properPairs sl lo hi t h2 := by simp [properPairs]
    rw [hc, List.filter_append, ← ih]
    by_cases hq : q a = true
    · have hc' : properPairs sl lo hi ((a :: t).filter q) (h2.filter q) =
          ((h2.filter q).filter fun b => properPairU sl lo hi a.1 b.1).map (fun b => (a, b)) ++
            properPairs sl lo hi (t.filter q) (h2.filter q) := by
        simp [properPairs, List.filter_cons, hq]
      rw [hc']
      congr 1
      rw [List.filter_map, List.filter_filter, List.filter_filter]
      congr 1
      · apply List.filter_congr
        intro x _
        simp [Function.comp, hq, Bool.and_comm]
    · have hc' : properPairs sl lo hi ((a :: t).filter q) (h2.filter q) =
          properPairs sl lo hi (t.filter q) (h2.filter q) := by
        simp [properPairs, List.filter_cons, hq]
      rw [hc']
      have : ((h2.filter fun b => properPairU sl lo hi a.1 b.1).map (fun b => (a, b))).filter
          (fun p => q p.1 && q p.2) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨b, _, rfl⟩ := hp
        simp [hq]
      rw [this, List.nil_append]

/-- `find?` over a filtered list, when the dropped elements fail the test and the
kept ones test the same. -/
theorem find?_filter_eq {α : Type} (L : List α) (Q P P' : α → Bool)
    (hdrop : ∀ x ∈ L, Q x = false → P x = false)
    (hkeep : ∀ x ∈ L, Q x = true → P x = P' x) :
    L.find? P = (L.filter Q).find? P' := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    have ih' := ih (fun y hy => hdrop y (List.mem_cons_of_mem _ hy))
      (fun y hy => hkeep y (List.mem_cons_of_mem _ hy))
    cases hQ : Q x
    · have hP := hdrop x List.mem_cons_self hQ
      simp [List.find?_cons, hP, List.filter_cons, hQ, ih']
    · have hP := hkeep x List.mem_cons_self hQ
      cases hPx : P x
      · simp [List.find?_cons, hPx, List.filter_cons, hQ, ← hP, ih']
      · simp [List.find?_cons, hPx, List.filter_cons, hQ, ← hP]

/-- A placement determines its score in the list. -/
def ScoreFun (h : List (Placement × Int)) : Prop :=
  ∀ x ∈ h, ∀ y ∈ h, x.1 = y.1 → x.2 = y.2

/-- Branch and bound, with the bound and the filter named. -/
theorem bestPairD_restrictW (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (hf1 : ScoreFun h1) (hf2 : ScoreFun h2)
    (hn1 : ∀ x ∈ h1, x.2 ≤ 0) (hn2 : ∀ x ∈ h2, x.2 ≤ 0)
    (w : PairHit) (hw : w ∈ properPairs sl lo hi h1 h2)
    (W : Int) (hW : W = pairScoreD dc w)
    (q : Placement × Int → Bool) (hq : q = fun x => decide (W ≤ x.2))
    (ps : List PairHit) (hps : ps = properPairs sl lo hi h1 h2) :
    bestPairD dc sl lo hi h1 h2 = bestPairD dc sl lo hi (h1.filter q) (h2.filter q) := by
  have hfil := properPairs_filter sl lo hi h1 h2 q
  unfold bestPairD
  rw [hfil, ← hps]
  obtain ⟨hw1, hw2, _⟩ := mem_properPairs.mp hw
  rw [← hps] at hw
  -- equal placements give equal pair scores
  have hsame : ∀ p ∈ ps, ∀ p' ∈ ps, p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1 →
      pairScoreD dc p' = pairScoreD dc p := by
    intro p hp p' hp' ⟨e1, e2⟩
    rw [hps] at hp hp'
    obtain ⟨hp1, hp2, _⟩ := mem_properPairs.mp hp
    obtain ⟨hp1', hp2', _⟩ := mem_properPairs.mp hp'
    unfold pairScoreD
    rw [hf1 _ hp1' _ hp1 e1, hf2 _ hp2' _ hp2 e2, e1, e2]
  -- a pair with a mate below `W` scores below `W`
  have hlow : ∀ p ∈ ps, (q p.1 && q p.2) = false → pairScoreD dc p < W := by
    intro p hp hQ
    rw [hps] at hp
    obtain ⟨hp1, hp2, _⟩ := mem_properPairs.mp hp
    have n1 := hn1 _ hp1
    have n2 := hn2 _ hp2
    have hd : (0 : Int) ≤ (dc (fragLen p.1.1 p.2.1) : Int) := Int.natCast_nonneg _
    simp only [hq, Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le] at hQ
    unfold pairScoreD
    omega
  apply find?_filter_eq
  · intro p hp hQ
    have hlt := hlow p hp hQ
    rw [List.all_eq_false]
    refine ⟨w, hw, ?_⟩
    intro hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | he
    · omega
    · have := hsame p hp w hw he
      omega
  · intro p hp hQ
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h p' hp'
      exact h p' (List.mem_filter.mp hp').1
    · intro h p' hp'
      by_cases hQ' : (q p'.1 && q p'.2) = true
      · exact h p' (List.mem_filter.mpr ⟨hp', hQ'⟩)
      · have hlt := hlow p' hp' (by simpa using hQ')
        -- `p` scores at least `W`: the witness is in the filtered list
        have hwQ : (q w.1 && q w.2) = true := by
          have n1 := hn1 _ hw1
          have n2 := hn2 _ hw2
          have hd : (0 : Int) ≤ (dc (fragLen w.1.1 w.2.1) : Int) := Int.natCast_nonneg _
          simp only [hq, Bool.and_eq_true, decide_eq_true_eq, hW]
          unfold pairScoreD
          omega
        have hwp := h w (List.mem_filter.mpr ⟨hw, hwQ⟩)
        have hge : W ≤ pairScoreD dc p := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hwp
          rw [hW]
          rcases hwp with hlt' | he
          · exact Int.le_of_lt hlt'
          · exact Int.le_of_eq (hsame p hp w hw he)
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (Int.lt_of_lt_of_le hlt hge)

/-- **Branch and bound.**  Given a proper pair `w`, `bestPairD` only needs the hits
with score at least `w`'s pair score. -/
theorem bestPairD_restrict (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (hf1 : ScoreFun h1) (hf2 : ScoreFun h2)
    (hn1 : ∀ x ∈ h1, x.2 ≤ 0) (hn2 : ∀ x ∈ h2, x.2 ≤ 0)
    (w : PairHit) (hw : w ∈ properPairs sl lo hi h1 h2) :
    bestPairD dc sl lo hi h1 h2 =
      bestPairD dc sl lo hi (h1.filter fun x => decide (pairScoreD dc w ≤ x.2))
        (h2.filter fun x => decide (pairScoreD dc w ≤ x.2)) :=
  bestPairD_restrictW dc sl lo hi h1 h2 hf1 hf2 hn1 hn2 w hw _ rfl _ rfl _ rfl

/-! ## Hit lists -/

theorem hitsOf_filter (f : Window → Option Int) (T W : Int) (ws : List Window) :
    (hitsOf f T ws).filter (fun x => decide (W ≤ x.2)) = hitsOf f (max T W) ws := by
  induction ws with
  | nil => rfl
  | cons v t ih =>
    simp only [hitsOf, List.filterMap_cons] at ih ⊢
    cases hv : f v with
    | none => simpa using ih
    | some s =>
      by_cases h1 : T ≤ s <;> by_cases h2 : W ≤ s <;>
        simp [h1, h2, List.filter_cons, ih, Int.max_le]

theorem hitsBoth_filter (sc : Scoring) (T W : Int) (g : Genome) (r : List Char) :
    (hitsBoth sc T g r).filter (fun x => decide (W ≤ x.2)) = hitsBoth sc (max T W) g r := by
  unfold hitsBoth
  rw [List.filter_append, List.filter_map, List.filter_map, ← hitsOf_filter, ← hitsOf_filter]
  rfl

theorem mem_hitsOf_score {f : Window → Option Int} {T : Int} {ws : List Window} {x : Window × Int}
    (h : x ∈ hitsOf f T ws) : f x.1 = some x.2 ∧ T ≤ x.2 := by
  unfold hitsOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨v, _, hv⟩ := h
  split at hv
  · next s hs =>
    split at hv
    · cases hv
      exact ⟨hs, by assumption⟩
    · cases hv
  · cases hv

theorem hitsBoth_scoreFun (sc : Scoring) (T : Int) (g : Genome) (r : List Char) :
    ScoreFun (hitsBoth sc T g r) := by
  intro x hx y hy e
  unfold hitsBoth at hx hy
  simp only [List.mem_append, List.mem_map] at hx hy
  rcases hx with ⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩ <;>
    rcases hy with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩ <;>
    simp only [Prod.mk.injEq, reduceCtorEq, and_false, and_true] at e
  · have a := (mem_hitsOf_score hx').1
    have b := (mem_hitsOf_score hy').1
    rw [e, b] at a
    exact (Option.some.inj a).symm
  · have a := (mem_hitsOf_score hx').1
    have b := (mem_hitsOf_score hy').1
    rw [e, b] at a
    exact (Option.some.inj a).symm

theorem hitsBoth_nonpos (T : Int) (g : Genome) (r : List Char) :
    ∀ x ∈ hitsBoth sc0 T g r, x.2 ≤ 0 := by
  intro x hx
  unfold hitsBoth at hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩
  · exact Fast.windowScore_nonpos _ _ _ _ (mem_hitsOf_score hx').1
  · exact Fast.windowScore_nonpos _ _ _ _ (mem_hitsOf_score hx').1

/-- **Branch and bound for `pairSpecUT`.**  Given any proper pair `w` of hits (at the
caps `T1, T2`) with pair score `W`, the answer is the same at the tighter caps
`max T1 W, max T2 W`; in penalties: cap `min(P, S)` for a best-so-far pair sum `S`. -/
theorem pairSpecUT_bnb (dc : Nat → Nat) (sl lo hi : Nat) (T1 T2 : Int) (g : Genome)
    (m1 m2 : List Char) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 T1 g m1) (hitsBoth sc0 T2 g m2)) :
    pairSpecUT sc0 dc sl lo hi T1 T2 g m1 m2 =
      pairSpecUT sc0 dc sl lo hi (max T1 (pairScoreD dc w)) (max T2 (pairScoreD dc w)) g m1 m2 := by
  unfold pairSpecUT
  rw [bestPairD_restrict dc sl lo hi _ _ (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)
    (hitsBoth_nonpos _ _ _) (hitsBoth_nonpos _ _ _) w hw, hitsBoth_filter, hitsBoth_filter]

/-- A hit at a tighter cap is a hit at a looser one. -/
theorem hitsBoth_mono {sc : Scoring} {T T' : Int} {g : Genome} {r : List Char}
    (hT : T ≤ T') {x : Placement × Int} (hx : x ∈ hitsBoth sc T' g r) : x ∈ hitsBoth sc T g r := by
  have e := hitsBoth_filter sc T T' g r
  rw [Int.max_eq_right hT] at e
  rw [← e] at hx
  exact (List.mem_filter.mp hx).1

end MapSpec
