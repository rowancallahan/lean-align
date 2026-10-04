import SeedMapper

/-!
# Codec `bandScore`: capped banded score-only window scorer

Part 1: a scorer only has to be right about windows scoring at least `T`
(`ScoreFaithful`); `mapWith` with such a scorer is `mapSpec`.
-/

namespace MapSpec

open AlignmentSpec

/-- The scorer agrees with the specification on every score `≥ T`, and on
nothing else. -/
def ScoreFaithful (sc : Scoring) (T : Int) (read : List Char) (g : Genome)
    (score : Window → Option Int) : Prop :=
  ∀ w s, (score w = some s ∧ T ≤ s) ↔ (windowScore sc read g w = some s ∧ T ≤ s)

/-- `hitsOf` only looks at scores `≥ T`. -/
theorem hitsOf_congr_faithful (sc : Scoring) (T : Int) (read : List Char) (g : Genome)
    (score : Window → Option Int) (hf : ScoreFaithful sc T read g score) (ws : List Window) :
    hitsOf score T ws = hitsOf (windowScore sc read g) T ws := by
  unfold hitsOf
  induction ws with
  | nil => rfl
  | cons w ws ih =>
  rw [List.filterMap_cons, List.filterMap_cons, ih]
  congr 1
  have h := hf w
  cases h1 : score w with
  | none =>
    cases h2 : windowScore sc read g w with
    | none => rfl
    | some s =>
      by_cases hT : T ≤ s
      · have := (h s).mpr ⟨h2, hT⟩; rw [h1] at this; cases this.1
      · simp [hT]
  | some s =>
    by_cases hT : T ≤ s
    · have := (h s).mp ⟨h1, hT⟩
      rw [this.1]
    · simp only [hT, if_false]
      cases h2 : windowScore sc read g w with
      | none => rfl
      | some s' =>
        by_cases hT' : T ≤ s'
        · have := (h s').mpr ⟨h2, hT'⟩; rw [h1] at this
          simp at this; omega
        · simp [hT']

/-- **Faithful scorer.**  With a complete lookup and a scorer faithful at
threshold `T`, the mapper returns the specification's answer. -/
theorem mapWith_eq_mapSpec_of_faithful (lookup : List Char → List (Nat × Nat))
    (score : Window → Option Int) (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) (hl : LookupComplete g l0 lookup)
    (hf : ScoreFaithful sc T read g score) :
    mapWith lookup score l0 T (errBound sc T) g read = mapSpec sc T g read := by
  have h : mapWith lookup score l0 T (errBound sc T) g read =
      mapWith lookup (windowScore sc read g) l0 T (errBound sc T) g read := by
    unfold mapWith
    rw [hitsOf_congr_faithful sc T read g score hf]
  rw [h]
  exact mapWith_eq_mapSpec lookup _ l0 sc hv T g read hl (fun _ => rfl)

end MapSpec

#print axioms MapSpec.mapWith_eq_mapSpec_of_faithful
