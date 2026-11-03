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

/-- A placement determines its score in the list. -/
def ScoreFun (h : List (Placement × Int)) : Prop :=
  ∀ x ∈ h, ∀ y ∈ h, x.1 = y.1 → x.2 = y.2

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

/-- A hit at a tighter cap is a hit at a looser one. -/
theorem hitsBoth_mono {sc : Scoring} {T T' : Int} {g : Genome} {r : List Char}
    (hT : T ≤ T') {x : Placement × Int} (hx : x ∈ hitsBoth sc T' g r) : x ∈ hitsBoth sc T g r := by
  have e := hitsBoth_filter sc T T' g r
  rw [Int.max_eq_right hT] at e
  rw [← e] at hx
  exact (List.mem_filter.mp hx).1

end MapSpec

