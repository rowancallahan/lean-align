import SeedMapperDedup            -- the mapper (with and without duplicate removal)

/-!
# Codec `mapReadsPar`: map the reads in parallel

The reads are cut into chunks; each chunk is mapped in its own `Task`; the
results are concatenated in order.  For a pure function this is `List.map`.

The algorithm, then the theorems, then the proof.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Cut `l` into pieces of `n` items (the last may be shorter).  `fuel` bounds
the number of cuts; `l.length` is always enough. -/
def chunksAux {α : Type} (n : Nat) : Nat → List α → List (List α)
  | 0, l => [l]
  | fuel + 1, l =>
    match l.drop n with
    | [] => [l]
    | rest => l.take n :: chunksAux n fuel rest

/-- Cut `l` into pieces of `chunk` items (at least one item each). -/
def chunksOf {α : Type} (chunk : Nat) (l : List α) : List (List α) :=
  chunksAux (max chunk 1) l.length l

/-- Map every chunk in its own task, then concatenate the results in order. -/
def mapReadsPar {α β : Type} (chunk : Nat) (f : α → β) (reads : List α) : List β :=
  let tasks := (chunksOf chunk reads).map fun c => Task.spawn fun _ => c.map f
  tasks.flatMap Task.get

/-- Build the index once, then map the reads in parallel. -/
def mapReadsIndexPar (chunk l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  mapReadsPar chunk (mapWithIndex sc T idx) reads

/-- Build the index and chromosome lengths once, then map the reads in
parallel, scoring each candidate window once. -/
def mapReadsDedupPar (chunk l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  let lens := chrLens g
  mapReadsPar chunk (mapWithIndexDedup sc T idx lens) reads

/-! ## The theorems

    mapReadsPar chunk f reads = reads.map f                                (mapReadsPar_eq_map)
    mapReadsIndexPar chunk l0 sc T g reads = reads.map (mapSpec sc T g)    (mapReadsIndexPar_eq_mapSpec)
    mapReadsDedupPar chunk l0 sc T g reads = reads.map (mapSpec sc T g)    (mapReadsDedupPar_eq_mapSpec)

The first for every function and chunk size; the others for every scoring
with `ValidScoring sc`. -/

/-! ## Proof -/

/-- The pieces, put back together, are the list. -/
theorem flatten_chunksAux {α : Type} (n fuel : Nat) (l : List α) : (chunksAux n fuel l).flatten = l := by
  induction fuel generalizing l with
  | zero => simp [chunksAux]
  | succ fuel ih =>
    unfold chunksAux
    split
    · simp
    · next rest _ =>
      rw [List.flatten_cons, ih rest]
      exact List.take_append_drop n l

theorem flatten_chunksOf {α : Type} (chunk : Nat) (l : List α) : (chunksOf chunk l).flatten = l :=
  flatten_chunksAux _ _ l

/-- **Parallel map is map.** -/
theorem mapReadsPar_eq_map {α β : Type} (chunk : Nat) (f : α → β) (reads : List α) :
    mapReadsPar chunk f reads = reads.map f := by
  unfold mapReadsPar
  simp only [List.flatMap_map]
  have hget : ∀ c : List α, (Task.spawn fun _ => c.map f).get = c.map f := fun _ => rfl
  simp only [hget]
  rw [List.flatMap_def, ← List.map_flatten, flatten_chunksOf]

/-- **Parallel mapping through the index** gives every read the
specification's answer. -/
theorem mapReadsIndexPar_eq_mapSpec (chunk l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReadsIndexPar chunk l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsIndexPar
  rw [mapReadsPar_eq_map]
  exact mapReads_eq_mapSpec l0 sc hv T g reads

/-- **Parallel mapping, each window scored once,** gives every read the
specification's answer. -/
theorem mapReadsDedupPar_eq_mapSpec (chunk l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReadsDedupPar chunk l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsDedupPar
  rw [mapReadsPar_eq_map]
  exact mapReadsDedup_eq_mapSpec l0 sc hv T g reads

end MapSpec

#print axioms MapSpec.mapReadsPar_eq_map
#print axioms MapSpec.mapReadsIndexPar_eq_mapSpec
#print axioms MapSpec.mapReadsDedupPar_eq_mapSpec
