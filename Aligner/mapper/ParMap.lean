import SeedMapper                  -- the mapper and its theorems against `mapSpec`

/-!
# Codec `parMap`: map an array in parallel

The array is cut into `n` batches of `⌈size / n⌉` items; each batch is mapped
in its own dedicated `Task`; the results are concatenated in order.  In Lean's
logic `Task.spawn` and `Task.get` are pure (`(Task.spawn fn).get = fn ()`), so
`parMap` is `Array.map`.

The algorithm, then the theorems, then the proof.
-/

namespace ParMap

/-! ## The algorithm -/

/-- Number of items in each batch: `⌈size / n⌉` (with `n` at least 1). -/
def batchSize (n size : Nat) : Nat := (size + max n 1 - 1) / max n 1

/-- Batch `t`: items `t * b ..< (t + 1) * b`. -/
def batch {α : Type} (b : Nat) (xs : Array α) (t : Nat) : Array α :=
  xs.extract (t * b) ((t + 1) * b)

/-- Append the results of the tasks in order. -/
def joinTasks {β : Type} (tasks : List (Task (Array β))) : Array β :=
  tasks.foldl (fun acc t => acc ++ t.get) #[]

/-- Map `f` over `xs` with `n` tasks (one per batch).  All tasks are spawned
before the first `get`. -/
def parMap {α β : Type} (n : Nat) (f : α → β) (xs : Array α) : Array β :=
  let b := batchSize n xs.size
  let tasks := (List.range (max n 1)).map fun t =>
    Task.spawn (prio := .dedicated) fun _ => (batch b xs t).map f
  joinTasks tasks

end ParMap

namespace MapSpec

open AlignmentSpec ParMap

/-- Build the index once, then map an array of reads with `n` tasks. -/
def mapReadsParArray (n l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : Array (List Char)) :
    Array (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  parMap n (mapWithIndex sc T idx) reads

/-! ## The theorems

    parMap n f xs = xs.map f                                                 (parMap_eq_map)
    (∀ r, f r = mapSpec sc T g r) → parMap n f reads = reads.map (mapSpec sc T g)
                                                                             (parMap_eq_mapSpec)
    mapReadsParArray n l0 sc T g reads = reads.map (mapSpec sc T g)          (mapReadsParArray_eq_mapSpec)

The first for every `n` (0 and `n > xs.size` included) and every function;
the second for every per-read function equal to `mapSpec`; the third for
every scoring with `ValidScoring sc`. -/

end MapSpec

/-! ## Proof -/

namespace ParMap

theorem joinTasks_range_spawn {α β : Type} (f : α → β) (xs : Array α) (b k : Nat) :
    joinTasks ((List.range k).map fun t =>
        Task.spawn (prio := .dedicated) fun _ => (batch b xs t).map f) =
      (xs.extract 0 (k * b)).map f := by
  unfold joinTasks
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    have hget : ∀ c : Array β, (Task.spawn (prio := .dedicated) fun _ => c).get = c := fun _ => rfl
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hget, batch]
    rw [← Array.map_append, Array.extract_append_extract]
    congr 2 <;> simp [Nat.succ_mul]

theorem size_le_batches (n s : Nat) : s ≤ max n 1 * batchSize n s := by
  unfold batchSize
  have h1 : 0 < max n 1 := by omega
  have h2 := Nat.div_add_mod (s + max n 1 - 1) (max n 1)
  have h3 := Nat.mod_lt (s + max n 1 - 1) h1
  generalize max n 1 * ((s + max n 1 - 1) / max n 1) = q at h2 ⊢
  omega

/-- **Parallel map is map.** -/
theorem parMap_eq_map {α β : Type} (n : Nat) (f : α → β) (xs : Array α) :
    parMap n f xs = xs.map f := by
  unfold parMap
  simp only
  rw [joinTasks_range_spawn, Array.extract_eq_self_of_le (size_le_batches n xs.size)]

end ParMap

namespace MapSpec

open AlignmentSpec ParMap

/-- **Any per-read function equal to `mapSpec`, run in parallel,** gives every
read the specification's answer. -/
theorem parMap_eq_mapSpec (n : Nat) (sc : Scoring) (T : Int) (g : Genome)
    (f : List Char → Option (Window × Int)) (hf : ∀ read, f read = mapSpec sc T g read)
    (reads : Array (List Char)) :
    parMap n f reads = reads.map (mapSpec sc T g) := by
  rw [parMap_eq_map]
  exact Array.map_congr_left (fun r _ => hf r)

/-- **One index, reads mapped in parallel.**  Every read gets the
specification's answer. -/
theorem mapReadsParArray_eq_mapSpec (n l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : Array (List Char)) :
    mapReadsParArray n l0 sc T g reads = reads.map (mapSpec sc T g) :=
  parMap_eq_mapSpec n sc T g _ (mapWithIndex_eq_mapSpec l0 sc hv T g _ rfl) reads

end MapSpec

#print axioms ParMap.parMap_eq_map
#print axioms MapSpec.parMap_eq_mapSpec
#print axioms MapSpec.mapReadsParArray_eq_mapSpec
