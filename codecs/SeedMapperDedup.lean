import SeedMapper                 -- the seed-and-index mapper and its theorems
import Std.Data.HashSet

/-!
# Codec `mapWithDedup`: score each candidate window once

`mapWith` hands every candidate window to the scorer.  The candidate list
names the same window many times (several seeds and shifts produce it) and
names windows that do not fit in their chromosome.  `mapWithDedup` first drops
the windows that do not fit, looking only at chromosome lengths, then removes
repeated windows with a hash set, and only then scores, filters and selects
exactly as `mapWith` does.

The algorithm, then the theorems, then the proof.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

instance : Hashable Window where
  hash w := mixHash (hash w.chr) (mixHash (hash w.start) (hash w.len))

/-- Chromosome lengths, computed once per genome. -/
def chrLens (g : Genome) : Array Nat :=
  (g.map fun c => c.seq.length).toArray

/-- Does the window fit in its chromosome?  Looks only at the lengths. -/
def fitsLens (lens : Array Nat) (w : Window) : Bool :=
  match lens[w.chr]? with
  | some n => decide (w.start + w.len ≤ n)
  | none => false

/-- One step of duplicate removal: keep `w` unless it was seen before. -/
def dedupStep (acc : Std.HashSet Window × Array Window) (w : Window) :
    Std.HashSet Window × Array Window :=
  if acc.1.contains w then acc else (acc.1.insert w, acc.2.push w)

/-- The windows of `ws`, each once, in order of first appearance. -/
def dedupWindows (ws : List Window) : List Window :=
  (ws.foldl dedupStep (∅, #[])).2.toList

/-- The candidate windows that fit, each once. -/
def dedupCandidates (lens : Array Nat) (ws : List Window) : List Window :=
  dedupWindows (ws.filter (fitsLens lens))

/-- `mapWith` with the chromosome lengths supplied: drop the candidates that do
not fit, remove repeats, then score, filter and select. -/
def mapWithLens (lens : Array Nat) (lookup : List Char → List (Nat × Nat))
    (score : Window → Option Int) (l0 : Nat) (T : Int) (k : Nat) (g : Genome) (read : List Char) :
    Option (Window × Int) :=
  selectUnique (hitsOf score T (dedupCandidates lens (candidates lookup l0 g read k)))

/-- Drop the candidates that do not fit, remove repeats, then score, filter and
select. -/
def mapWithDedup (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (T : Int) (k : Nat) (g : Genome) (read : List Char) : Option (Window × Int) :=
  mapWithLens (chrLens g) lookup score l0 T k g read

/-- Map one read through an index, with the chromosome lengths supplied. -/
def mapWithIndexDedup (sc : Scoring) (T : Int) (idx : Index) (lens : Array Nat) (read : List Char) :
    Option (Window × Int) :=
  mapWithLens lens idx.lookup (kernelScore sc read idx.genome) idx.l0 T (errBound sc T) idx.genome read

/-- Build the index and the chromosome lengths once, then map every read. -/
def mapReadsDedup (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  let lens := chrLens g
  reads.map (mapWithIndexDedup sc T idx lens)

/-! ## The theorems

    (∀ w, windowSeq g w = none → score w = none) →
      mapWithDedup lookup score l0 T k g read = mapWith lookup score l0 T k g read
                                                                     (mapWithDedup_eq_mapWith)
    (dedupWindows ws).Nodup,   w ∈ dedupWindows ws ↔ w ∈ ws          (nodup_dedupWindows, mem_dedupWindows)
    idx = buildIndex l0 g → lens = chrLens g →
      mapWithIndexDedup sc T idx lens read = mapSpec sc T g read     (mapWithIndexDedup_eq_mapSpec)
    mapReadsDedup l0 sc T g reads = reads.map (mapSpec sc T g)       (mapReadsDedup_eq_mapSpec)

The last two for every scoring with `ValidScoring sc`. -/

/-! ## Proof -/

/-- The length test is the specification's notion of fitting. -/
theorem fitsLens_chrLens (g : Genome) (w : Window) :
    fitsLens (chrLens g) w = (windowSeq g w).isSome := by
  unfold fitsLens chrLens windowSeq
  rw [List.getElem?_toArray, List.getElem?_map]
  cases g[w.chr]? with
  | none => rfl
  | some c =>
    simp only [Option.map_some]
    by_cases h : w.start + w.len ≤ c.seq.length <;> simp [h]

/-- Invariant of duplicate removal: the set and the array hold the same
windows, and the array holds each once. -/
private def DedupInv (acc : Std.HashSet Window × Array Window) : Prop :=
  (∀ w, w ∈ acc.1 ↔ w ∈ acc.2.toList) ∧ acc.2.toList.Nodup

private theorem dedupStep_inv (acc : Std.HashSet Window × Array Window) (w : Window)
    (h : DedupInv acc) : DedupInv (dedupStep acc w) := by
  unfold dedupStep
  by_cases hc : acc.1.contains w = true
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]
    have hnot : w ∉ acc.2.toList := fun hm => hc (Std.HashSet.mem_iff_contains.mp ((h.1 w).mpr hm))
    refine ⟨fun x => ?_, ?_⟩
    · simp only [Std.HashSet.mem_insert, Array.toList_push, List.mem_append, List.mem_singleton,
        beq_iff_eq, h.1 x]
      constructor
      · rintro (rfl | hx)
        · exact Or.inr rfl
        · exact Or.inl hx
      · rintro (hx | rfl)
        · exact Or.inr hx
        · exact Or.inl rfl
    · simp only [Array.toList_push]
      rw [List.nodup_append]
      refine ⟨h.2, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      exact hnot ha

private theorem dedupStep_mem (acc : Std.HashSet Window × Array Window) (w x : Window)
    (h : DedupInv acc) : x ∈ (dedupStep acc w).2.toList ↔ x ∈ acc.2.toList ∨ x = w := by
  unfold dedupStep
  by_cases hc : acc.1.contains w = true
  · rw [if_pos hc]
    have hw : w ∈ acc.2.toList := (h.1 w).mp (Std.HashSet.mem_iff_contains.mpr hc)
    constructor
    · exact Or.inl
    · rintro (hx | rfl)
      · exact hx
      · exact hw
  · rw [if_neg hc]
    simp [Array.toList_push]

private theorem foldl_dedupStep (ws : List Window) :
    ∀ acc : Std.HashSet Window × Array Window, DedupInv acc →
      DedupInv (ws.foldl dedupStep acc) ∧
      ∀ x, x ∈ (ws.foldl dedupStep acc).2.toList ↔ x ∈ acc.2.toList ∨ x ∈ ws := by
  induction ws with
  | nil => intro acc h; exact ⟨h, fun x => by simp⟩
  | cons w ws ih =>
    intro acc h
    rw [List.foldl_cons]
    obtain ⟨hinv, hmem⟩ := ih (dedupStep acc w) (dedupStep_inv acc w h)
    refine ⟨hinv, fun x => ?_⟩
    rw [hmem x, dedupStep_mem acc w x h, List.mem_cons, or_assoc]

private theorem dedupInv_empty : DedupInv ((∅ : Std.HashSet Window), (#[] : Array Window)) :=
  ⟨fun w => by simp, by simp⟩

/-- Duplicate removal keeps exactly the windows that were there. -/
theorem mem_dedupWindows (ws : List Window) (w : Window) : w ∈ dedupWindows ws ↔ w ∈ ws := by
  unfold dedupWindows
  rw [(foldl_dedupStep ws _ dedupInv_empty).2 w]
  simp

/-- After duplicate removal every window appears once, so it is scored once. -/
theorem nodup_dedupWindows (ws : List Window) : (dedupWindows ws).Nodup :=
  (foldl_dedupStep ws _ dedupInv_empty).1.2

/-- The windows left to score: the candidates that fit. -/
theorem mem_dedupCandidates (lens : Array Nat) (ws : List Window) (w : Window) :
    w ∈ dedupCandidates lens ws ↔ w ∈ ws ∧ fitsLens lens w = true := by
  unfold dedupCandidates
  rw [mem_dedupWindows, List.mem_filter]

/-- **Same answer as `mapWith`**, for any lookup and any scorer that returns
`none` on windows that do not fit. -/
theorem mapWithDedup_eq_mapWith (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (T : Int) (k : Nat) (g : Genome) (read : List Char)
    (hfit : ∀ w, windowSeq g w = none → score w = none) :
    mapWithDedup lookup score l0 T k g read = mapWith lookup score l0 T k g read := by
  unfold mapWithDedup mapWithLens mapWith
  apply selectUnique_congr
  · rintro ⟨w, s⟩
    rw [mem_hitsOf, mem_hitsOf, mem_dedupCandidates, fitsLens_chrLens]
    constructor
    · rintro ⟨⟨hw, -⟩, hs, hT⟩
      exact ⟨hw, hs, hT⟩
    · rintro ⟨hw, hs, hT⟩
      refine ⟨⟨hw, ?_⟩, hs, hT⟩
      cases hseq : windowSeq g w with
      | none => rw [hfit w hseq] at hs; cases hs
      | some _ => rfl
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

/-- The specification's score is `none` on windows that do not fit. -/
theorem windowScore_none_of_not_fit (sc : Scoring) (read : List Char) (g : Genome) (w : Window)
    (h : windowSeq g w = none) : windowScore sc read g w = none := by
  unfold windowScore; rw [h]

/-- The codec's score is `none` on windows that do not fit. -/
theorem kernelScore_none_of_not_fit (sc : Scoring) (read : List Char) (g : Genome) (w : Window)
    (h : windowSeq g w = none) : kernelScore sc read g w = none := by
  unfold kernelScore; rw [h]

/-- With a complete lookup and a correct scorer, `mapWithDedup` returns the
specification's answer. -/
theorem mapWithDedup_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w) :
    mapWithDedup lookup score l0 T (errBound sc T) g read = mapSpec sc T g read := by
  rw [mapWithDedup_eq_mapWith lookup score l0 T (errBound sc T) g read
    (fun w h => by rw [hs w]; exact windowScore_none_of_not_fit sc read g w h)]
  exact mapWith_eq_mapSpec lookup score l0 sc hv T g read hl hs

/-- **Index and read.**  Mapping through the index and lengths made from the
genome gives what `mapWithIndex` gives. -/
theorem mapWithIndexDedup_eq_mapWithIndex (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome)
    (idx : Index) (hidx : idx = buildIndex l0 g) (lens : Array Nat) (hlens : lens = chrLens g)
    (read : List Char) :
    mapWithIndexDedup sc T idx lens read = mapWithIndex sc T idx read := by
  subst hidx hlens
  exact mapWithDedup_eq_mapWith _ _ _ T _ g read (kernelScore_none_of_not_fit sc read g)

/-- So it is the specification's answer. -/
theorem mapWithIndexDedup_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (idx : Index) (hidx : idx = buildIndex l0 g) (lens : Array Nat)
    (hlens : lens = chrLens g) (read : List Char) :
    mapWithIndexDedup sc T idx lens read = mapSpec sc T g read := by
  rw [mapWithIndexDedup_eq_mapWithIndex l0 sc T g idx hidx lens hlens]
  exact mapWithIndex_eq_mapSpec l0 sc hv T g idx hidx read

/-- **One index, many reads.**  Every read gets the specification's answer. -/
theorem mapReadsDedup_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReadsDedup l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsDedup
  apply List.map_congr_left
  intro read _
  exact mapWithIndexDedup_eq_mapSpec l0 sc hv T g _ rfl _ rfl read

end MapSpec

#print axioms MapSpec.mem_dedupWindows
#print axioms MapSpec.nodup_dedupWindows
#print axioms MapSpec.mapWithDedup_eq_mapWith
#print axioms MapSpec.mapWithDedup_eq_mapSpec
#print axioms MapSpec.mapWithIndexDedup_eq_mapWithIndex
#print axioms MapSpec.mapWithIndexDedup_eq_mapSpec
#print axioms MapSpec.mapReadsDedup_eq_mapSpec
