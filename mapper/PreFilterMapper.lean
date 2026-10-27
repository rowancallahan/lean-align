import MapSpec                    -- the mapping specification (spec/, draft)
import SeedMapper                 -- mapWith, candidates, mem_candidates

/-!
# Pre-filter by a location-decided predicate

Users often keep only reads whose mapped window passes a filter decided by
location alone (`keep : Window → Bool`: a region, a chromosome, and for pairs
proper-pair orientation and distance).  The window the specification reports
is always among the seed candidates, so when no candidate passes `keep` the
filtered answer is `none`, and the read can be skipped before any alignment.

    (∀ w s, windowScore w = some s → T ≤ s → w ∈ C) → (∀ w ∈ C, keep w = false) →
      (mapSpec sc T g read).filter (keep ·.1) = none                       (filter_none_of_cover)
    mapPreFiltered keep C (fun _ => mapWith …) = (mapSpec sc T g read).filter (keep ·.1)
                                                                            (mapPreFiltered_eq)
    the same with C = the seed candidates of `mapWith`                     (mapWithPreFiltered_eq)

## Paired-end (statement only, not proved: no paired-end spec yet)

With a paired spec `mapPairSpec sc T g (r1, r2) : Option ((Window × Int) × (Window × Int))`
and `proper : Window → Window → Bool` (orientation, distance), and candidate
lists `C1`, `C2` covering every window scoring ≥ T for `r1`, `r2`:

    (∀ w1 ∈ C1, ∀ w2 ∈ C2, proper w1 w2 = false) →
      (mapPairSpec sc T g (r1, r2)).filter (fun p => proper p.1.1 p.2.1) = none

Proof plan: the reported pair has each window among the hits of its read
(the analogue of `mem_of_selectUnique` per read), hence in `C1 × C2`.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Skip the read when no candidate passes `keep`; otherwise run `mapper` and filter. -/
def mapPreFiltered (keep : Window → Bool) (C : List Window) (mapper : Unit → Option (Window × Int)) :
    Option (Window × Int) :=
  if C.any keep then (mapper ()).filter (fun a => keep a.1) else none

/-! ## Proof -/

theorem mem_of_selectUnique (l : List (Window × Int)) (a : Window × Int) (h : selectUnique l = some a) :
    a ∈ l :=
  List.mem_of_find?_eq_some h

/-- **The reported window is a candidate.**  If `C` covers every window
scoring at least `T`, the window `mapSpec` reports is in `C`. -/
theorem mapSpec_mem_cover (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (hC : ∀ w s, windowScore sc read g w = some s → T ≤ s → w ∈ C) (w : Window) (s : Int)
    (h : mapSpec sc T g read = some (w, s)) : w ∈ C := by
  have hm := mem_of_selectUnique _ _ h
  rw [mem_hitsOf] at hm
  exact hC w s hm.2.1 hm.2.2

/-- **Pre-filter.**  If no covering candidate passes `keep`, the filtered
answer is `none`. -/
theorem filter_none_of_cover (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (hC : ∀ w s, windowScore sc read g w = some s → T ≤ s → w ∈ C)
    (keep : Window → Bool) (hk : ∀ w ∈ C, keep w = false) :
    (mapSpec sc T g read).filter (fun a => keep a.1) = none := by
  cases h : mapSpec sc T g read with
  | none => rfl
  | some a =>
    obtain ⟨w, s⟩ := a
    have := hk w (mapSpec_mem_cover sc T g read C hC w s h)
    simp [Option.filter, this]

/-- Skipping such reads gives the same filtered output. -/
theorem mapPreFiltered_eq (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (hC : ∀ w s, windowScore sc read g w = some s → T ≤ s → w ∈ C)
    (keep : Window → Bool) (mapper : Unit → Option (Window × Int))
    (hm : mapper () = mapSpec sc T g read) :
    mapPreFiltered keep C mapper = (mapSpec sc T g read).filter (fun a => keep a.1) := by
  unfold mapPreFiltered
  split
  · rw [hm]
  · rename_i hany
    symm
    apply filter_none_of_cover sc T g read C hC keep
    intro w hw
    cases hkw : keep w with
    | false => rfl
    | true => exact absurd (List.any_eq_true.mpr ⟨w, hw, hkw⟩) hany

/-- **With the seed mapper.**  Candidates are `mapWith`'s seed candidates. -/
theorem mapWithPreFiltered_eq (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w)
    (keep : Window → Bool) :
    mapPreFiltered keep (candidates lookup l0 g read (errBound sc T))
        (fun _ => mapWith lookup score l0 T (errBound sc T) g read) =
      (mapSpec sc T g read).filter (fun a => keep a.1) :=
  mapPreFiltered_eq sc T g read _
    (fun w s hws hT => mem_candidates lookup l0 sc hv T g hl read w s hws hT) keep _
    (mapWith_eq_mapSpec lookup score l0 sc hv T g read hl hs)

end MapSpec

#print axioms MapSpec.filter_none_of_cover
#print axioms MapSpec.mapPreFiltered_eq
#print axioms MapSpec.mapWithPreFiltered_eq
