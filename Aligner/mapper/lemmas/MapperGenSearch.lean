import MapperFastAlgo

/-!
Near-linear helpers for the general mapper's stages.

* `dedupAdj`: drop adjacent repeats (after a sort, all repeats); same members.
* `lbound`, `anyNear`: binary search in an increasing array of packed anchors
  for one whose diagonal `e / 16` lies in `[lo, hi]` (`anyNear_spec`).
-/

namespace MapSpec.Fast

/-- Drop adjacent repeats. -/
def dedupAdj : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then dedupAdj (b :: t) else a :: dedupAdj (b :: t)

theorem mem_dedupAdj : ∀ (l : List Nat) (x : Nat), x ∈ dedupAdj l ↔ x ∈ l
  | [], x => by simp [dedupAdj]
  | [a], x => by simp [dedupAdj]
  | a :: b :: t, x => by
    unfold dedupAdj
    have ih := mem_dedupAdj (b :: t) x
    split
    · next hab => subst hab; rw [ih]; simp
    · rw [List.mem_cons, ih]; simp

/-- First index in `[a, b)` whose anchor's diagonal is `≥ lo` (`b` if none),
for an increasing array. -/
def lbound (arr : Array Nat) (lo : Nat) (a b : Nat) : Nat :=
  if a < b then
    let mid := (a + b) / 2
    if arr[mid]! / 16 < lo then lbound arr lo (mid + 1) b else lbound arr lo a mid
  else a
termination_by b - a

/-- Is there an anchor with diagonal in `[lo, hi]`? -/
def anyNear (arr : Array Nat) (lo hi : Nat) : Bool :=
  let i := lbound arr lo 0 arr.size
  decide (i < arr.size) && decide (arr[i]! / 16 ≤ hi)

section
variable (arr : Array Nat) (hs : arr.toList.Pairwise (· < ·))
include hs

theorem mono_get (i j : Nat) (hij : i ≤ j) (hj : j < arr.size) : arr[i]! / 16 ≤ arr[j]! / 16 := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · have := List.pairwise_iff_getElem.1 hs i j (by simp; omega) (by simp; omega) h
    simp only [Array.getElem_toList] at this
    rw [getElem!_pos arr i (by omega), getElem!_pos arr j hj]
    exact Nat.div_le_div_right (by omega)
  · exact Nat.le_refl _

theorem lbound_spec (lo : Nat) :
    ∀ d a b, b - a = d → a ≤ b → b ≤ arr.size → (∀ k, k < a → arr[k]! / 16 < lo) → (∀ k, b ≤ k → k < arr.size → lo ≤ arr[k]! / 16) →
      (∀ k, k < lbound arr lo a b → arr[k]! / 16 < lo) ∧
      (∀ k, lbound arr lo a b ≤ k → k < arr.size → lo ≤ arr[k]! / 16) ∧ lbound arr lo a b ≤ arr.size := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro a b hd hab0 hb h1 h2
    unfold lbound
    split
    · next hab =>
      dsimp only
      split
      · next hm =>
        exact ih (b - ((a + b) / 2 + 1)) (by omega) _ _ rfl (by omega) hb (fun k hk => by
          by_cases hka : k < a
          · exact h1 k hka
          · have := mono_get arr hs k ((a + b) / 2) (by omega) (by omega); omega) h2
      · next hm =>
        exact ih ((a + b) / 2 - a) (by omega) _ _ rfl (by omega) (by omega) h1 (fun k hk hk2 => by
          by_cases hkb : b ≤ k
          · exact h2 k hkb hk2
          · have := mono_get arr hs ((a + b) / 2) k hk hk2; omega)
    · next hab =>
      refine ⟨h1, fun k hk hk2 => h2 k (by omega) hk2, by omega⟩

/-- **Binary search.** -/
theorem anyNear_spec (lo hi : Nat) :
    anyNear arr lo hi = true ↔ ∃ e ∈ arr.toList, lo ≤ e / 16 ∧ e / 16 ≤ hi := by
  obtain ⟨h1, h2, h3⟩ := lbound_spec arr hs lo _ 0 arr.size rfl (Nat.zero_le _) (Nat.le_refl _)
    (fun k hk => by omega) (fun k hk hk2 => by omega)
  unfold anyNear
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  generalize lbound arr lo 0 arr.size = i at *
  constructor
  · rintro ⟨hi1, hi2⟩
    refine ⟨arr[i], Array.getElem_mem_toList hi1, ?_, ?_⟩
    · have := h2 i (Nat.le_refl _) hi1; rwa [getElem!_pos arr i hi1] at this
    · rwa [getElem!_pos arr i hi1] at hi2
  · rintro ⟨e, he, hl, hh⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    simp only [Array.length_toList] at hk
    simp only [Array.getElem_toList] at hl hh
    have hk' : lo ≤ arr[k]! / 16 := by rw [getElem!_pos arr k hk]; exact hl
    have hik : i ≤ k := by
      apply Classical.byContradiction; intro h; have := h1 k (by omega); omega
    refine ⟨by omega, ?_⟩
    have := mono_get arr hs i k hik hk
    rw [getElem!_pos arr k hk] at this; omega

end

end MapSpec.Fast

#print axioms MapSpec.Fast.anyNear_spec
