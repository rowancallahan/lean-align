import SeedMapper                 -- `mapWith` and its general theorem

/-!
# Codec `mapReadsArray`: the seed-and-index mapper over arrays and a hashed index

The same algorithm as `indexMapper` (`mapWith`), with a faster lookup and a
faster scorer:

* each chromosome is stored once as an `Array Char`; a window's letters are
  taken with `Array.extract`;
* the index is keyed by a `UInt64` polynomial hash of the `l0`-letter word and
  is filled in one pass over each chromosome, reading the letters of each word
  straight from the array.

Two different words may share a hash.  Then a lookup reports places where the
word does not occur; they only add windows to score.  The theorem needs just
`LookupComplete`: every place a word does occur is reported.

The algorithm, then the theorems against `mapSpec`, then the proof.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- One step of the polynomial hash. -/
@[inline] def hashStep (h : UInt64) (c : Char) : UInt64 :=
  h * 0x9E3779B97F4A7C15 + c.val.toUInt64

/-- Hash of a word given as a list (used for the read's seeds). -/
def hashWord (word : List Char) : UInt64 :=
  word.foldl hashStep 0

/-- Hash of the `n` letters of `a` starting at `p`, continuing from `h`. -/
def hashFrom (a : Array Char) : Nat → Nat → UInt64 → UInt64
  | _, 0, h => h
  | p, n + 1, h => hashFrom a (p + 1) n (hashStep h (a.getD p 'A'))

abbrev PlaceTable := Std.HashMap UInt64 (List (Nat × Nat))

@[inline] def addPlace (m : PlaceTable) (h : UInt64) (place : Nat × Nat) : PlaceTable :=
  m.insert h (place :: m.getD h [])

/-- Add every `l0`-letter word of chromosome number `c`. -/
def addChromosome (l0 c : Nat) (a : Array Char) (m : PlaceTable) : PlaceTable :=
  (List.range (a.size + 1 - l0)).foldl (fun m p => addPlace m (hashFrom a p l0 0) (c, p)) m

/-- Hash of every `l0`-letter word of the genome ↦ the places (chromosome, start)
with that hash. -/
structure ArrayIndex where
  genome : Genome
  l0 : Nat
  chromosomes : Array (Array Char)
  table : PlaceTable

def buildArrayIndex (l0 : Nat) (g : Genome) : ArrayIndex :=
  let chromosomes := (g.map fun chromosome => chromosome.seq.toArray).toArray
  { genome := g, l0 := l0, chromosomes := chromosomes,
    table := (List.range chromosomes.size).foldl
      (fun m c => addChromosome l0 c (chromosomes.getD c #[]) m) ∅ }

def ArrayIndex.lookup (idx : ArrayIndex) (word : List Char) : List (Nat × Nat) :=
  idx.table.getD (hashWord word) []

/-- Score of the read against a window, computed by the proved codec on a
slice of the chromosome's array. -/
def arrayScore (sc : Scoring) (chromosomes : Array (Array Char)) (read : Array Char) (w : Window) :
    Option Int :=
  match chromosomes[w.chr]? with
  | some a =>
    if w.start + w.len ≤ a.size then
      match wfaAlignU3 sc read (a.extract w.start (w.start + w.len)) with
      | some result => some result.2
      | none => none
    else none
  | none => none

/-- Map one read through an array index. -/
def mapWithArrayIndex (sc : Scoring) (T : Int) (idx : ArrayIndex) (read : List Char) :
    Option (Window × Int) :=
  mapWith idx.lookup (arrayScore sc idx.chromosomes read.toArray) idx.l0 T (errBound sc T)
    idx.genome read

/-- Build the arrays and the index once, then map every read through them. -/
def mapReadsArray (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildArrayIndex l0 g
  reads.map (mapWithArrayIndex sc T idx)

/-! ## The theorems

    LookupComplete genome l0 (buildArrayIndex l0 genome).lookup             (buildArrayIndex_complete)
    arrayScore sc (buildArrayIndex l0 genome).chromosomes read.toArray w
      = windowScore sc read genome w                                        (arrayScore_eq)
    mapWithArrayIndex sc T (buildArrayIndex l0 genome) read
      = mapSpec sc T genome read                                            (mapWithArrayIndex_eq_mapSpec)
    mapReadsArray l0 sc T genome reads = reads.map (mapSpec sc T genome)    (mapReadsArray_eq_mapSpec)

for every genome, read, threshold `T` and word length `l0`; the last two for
every scoring with `ValidScoring sc`.  They are at the end of this file;
everything before them is their proof. -/

/-! ## Proof -/

/-- Hashing from the array is hashing the word. -/
theorem hashFrom_eq (a : Array Char) : ∀ (n p : Nat) (h : UInt64), p + n ≤ a.size →
    hashFrom a p n h = ((a.toList.drop p).take n).foldl hashStep h := by
  intro n
  induction n with
  | zero => intro p h _; simp [hashFrom]
  | succ n ih =>
    intro p h hp
    have hlt : p < a.toList.length := by simp; omega
    rw [hashFrom, ih (p + 1) _ (by omega), List.drop_eq_getElem_cons hlt, List.take_succ_cons,
      List.foldl_cons]
    have : a.getD p 'A' = a.toList[p] := by
      simp [Array.getD, show p < a.size by omega]
    rw [this]

theorem mem_addPlace_self (m : PlaceTable) (h : UInt64) (place : Nat × Nat) :
    place ∈ (addPlace m h place).getD h [] := by
  simp [addPlace, Std.HashMap.getD_insert]

theorem mem_addPlace_of_mem (m : PlaceTable) (h h' : UInt64) (place place' : Nat × Nat)
    (hm : place' ∈ m.getD h' []) : place' ∈ (addPlace m h place).getD h' [] := by
  unfold addPlace
  rw [Std.HashMap.getD_insert]
  by_cases hk : (h == h') = true
  · rw [if_pos hk]
    have : h = h' := by simpa using hk
    subst this
    exact List.mem_cons_of_mem _ hm
  · rw [if_neg hk]
    exact hm

/-- A fold of `addPlace` over positions holds each position's place, and keeps
what the table held. -/
theorem mem_foldl_addPlace (key : Nat → UInt64) (c : Nat) (h : UInt64) (place : Nat × Nat) :
    ∀ (ps : List Nat) (m : PlaceTable),
      ((∃ p ∈ ps, key p = h ∧ (c, p) = place) ∨ place ∈ m.getD h []) →
      place ∈ (ps.foldl (fun m p => addPlace m (key p) (c, p)) m).getD h [] := by
  intro ps
  induction ps with
  | nil =>
    intro m hm
    rcases hm with ⟨p, hp, -⟩ | hm
    · cases hp
    · exact hm
  | cons q qs ih =>
    intro m hm
    rw [List.foldl_cons]
    apply ih
    rcases hm with ⟨p, hp, hk, hpl⟩ | hm
    · rcases List.mem_cons.1 hp with hp | hp
      · right
        subst hp; subst hk; subst hpl
        exact mem_addPlace_self _ _ _
      · exact Or.inl ⟨p, hp, hk, hpl⟩
    · exact Or.inr (mem_addPlace_of_mem _ _ _ _ _ hm)

theorem mem_addChromosome_of_mem (l0 c : Nat) (a : Array Char) (m : PlaceTable) (h : UInt64)
    (place : Nat × Nat) (hm : place ∈ m.getD h []) :
    place ∈ (addChromosome l0 c a m).getD h [] :=
  mem_foldl_addPlace _ c h place _ m (Or.inr hm)

theorem mem_addChromosome (l0 c : Nat) (a : Array Char) (m : PlaceTable) (p : Nat)
    (hp : p + l0 ≤ a.size) :
    (c, p) ∈ (addChromosome l0 c a m).getD (hashWord ((a.toList.drop p).take l0)) [] :=
  mem_foldl_addPlace _ c _ (c, p) _ m
    (Or.inl ⟨p, List.mem_range.2 (by omega), hashFrom_eq a l0 p 0 hp, rfl⟩)

/-- A fold of `addChromosome` over chromosome numbers holds every word of each. -/
theorem mem_foldl_addChromosome (l0 : Nat) (chrom : Nat → Array Char) (c p : Nat)
    (hp : p + l0 ≤ (chrom c).size) :
    ∀ (cs : List Nat) (m : PlaceTable),
      (c ∈ cs ∨ (c, p) ∈ m.getD (hashWord (((chrom c).toList.drop p).take l0)) []) →
      (c, p) ∈ (cs.foldl (fun m c => addChromosome l0 c (chrom c) m) m).getD
        (hashWord (((chrom c).toList.drop p).take l0)) [] := by
  intro cs
  induction cs with
  | nil =>
    intro m hm
    rcases hm with hm | hm
    · cases hm
    · exact hm
  | cons d ds ih =>
    intro m hm
    rw [List.foldl_cons]
    apply ih
    rcases hm with hm | hm
    · rcases List.mem_cons.1 hm with hm | hm
      · subst hm
        exact Or.inr (mem_addChromosome l0 c (chrom c) m p hp)
      · exact Or.inl hm
    · exact Or.inr (mem_addChromosome_of_mem _ _ _ _ _ _ hm)

/-- The chromosome arrays are the genome's sequences. -/
theorem buildArrayIndex_chromosomes (l0 : Nat) (g : Genome) (c : Nat) :
    (buildArrayIndex l0 g).chromosomes[c]? = (g[c]?).map fun chromosome => chromosome.seq.toArray := by
  simp [buildArrayIndex]

/-- The hashed index reports every place a word occurs. -/
theorem buildArrayIndex_complete (l0 : Nat) (g : Genome) :
    LookupComplete g l0 (buildArrayIndex l0 g).lookup := by
  intro c chromosome p hc hp
  have hlt : c < g.length := by
    rcases List.getElem?_eq_some_iff.mp hc with ⟨h, -⟩; exact h
  have hget : ((g.map fun chromosome => chromosome.seq.toArray).toArray).getD c #[] =
      chromosome.seq.toArray := by
    have h := buildArrayIndex_chromosomes l0 g c
    rw [hc] at h
    simp only [buildArrayIndex, Option.map_some] at h
    simp [Array.getD_eq_getD_getElem?, h]
  have h := mem_foldl_addChromosome l0
    (fun c => ((g.map fun chromosome => chromosome.seq.toArray).toArray).getD c #[]) c p
    (by simp only [hget]; simpa using hp)
    (List.range (g.map fun chromosome => chromosome.seq.toArray).toArray.size) ∅
    (Or.inl (List.mem_range.2 (by simpa using hlt)))
  simp only [hget] at h
  simpa [ArrayIndex.lookup, buildArrayIndex] using h

/-- A slice of the array is the window of the list. -/
theorem toList_extract_window (seq : List Char) (start len : Nat) :
    (seq.toArray.extract start (start + len)).toList = (seq.drop start).take len := by
  simp [List.extract_eq_drop_take]

/-- The array scorer returns the specification's window score. -/
theorem arrayScore_eq (l0 : Nat) (sc : Scoring) (g : Genome) (read : List Char) (w : Window) :
    arrayScore sc (buildArrayIndex l0 g).chromosomes read.toArray w = windowScore sc read g w := by
  unfold arrayScore windowScore windowSeq
  rw [buildArrayIndex_chromosomes]
  cases g[w.chr]? with
  | none => rfl
  | some chromosome =>
    simp only [Option.map_some, List.size_toArray]
    by_cases hfit : w.start + w.len ≤ chromosome.seq.length
    · rw [if_pos hfit, if_pos hfit]
      have h := wfaAlignU3_score sc read.toArray (chromosome.seq.toArray.extract w.start (w.start + w.len))
      rw [toList_extract_window] at h
      exact h
    · rw [if_neg hfit, if_neg hfit]

/-- **Index and read.**  Mapping through the array index gives exactly the
specification's answer. -/
theorem mapWithArrayIndex_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) :
    mapWithArrayIndex sc T (buildArrayIndex l0 g) read = mapSpec sc T g read :=
  mapWith_eq_mapSpec _ _ l0 sc hv T g read (buildArrayIndex_complete l0 g)
    (arrayScore_eq l0 sc g read)

/-- **One index, many reads.**  Every read gets the specification's answer. -/
theorem mapReadsArray_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReadsArray l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsArray
  apply List.map_congr_left
  intro read _
  exact mapWithArrayIndex_eq_mapSpec l0 sc hv T g read

end MapSpec

#print axioms MapSpec.buildArrayIndex_complete
#print axioms MapSpec.arrayScore_eq
#print axioms MapSpec.mapWithArrayIndex_eq_mapSpec
#print axioms MapSpec.mapReadsArray_eq_mapSpec
