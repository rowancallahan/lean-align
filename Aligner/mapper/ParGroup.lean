import ParStream                   -- parMap, streamTasks, formatAll, bytesOf
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Codec `ParGroup`: sort, de-duplicate, bin, map in parallel, restore order, stream

Three ways to reorganise the per-read work, each proved equal to mapping the
reads in input order:

* `sortMap` — tag each read with its index, sort by any comparison (e.g. the
  first bases), map the sorted reads in parallel bins, sort back by index.
* `dedupMap` — map only the distinct reads (in any order, here sorted), in
  parallel bins, keep the answers in a hash table, look every read up.
  A read missing from the table is mapped directly, so the theorem does not
  depend on the table being complete.
* `pipelineTasks` — cut the input into chunks; each chunk is grouped and
  mapped (`dedupMap`) and formatted in its own task, at most `w` chunks at a
  time; a writer takes the chunk texts in order.

The algorithm, then the theorems, then the proof.
-/

namespace ParMap

/-! ## The algorithm -/

/-- Map `f` over `xs` in bins of `b` items, one task per bin, on `prio`. -/
def parMapBins {α β : Type} (prio : Task.Priority) (b : Nat) (f : α → β) (xs : Array α) : Array β :=
  let bs := max b 1
  joinTasks ((List.range (numBatches bs xs.size)).map fun t =>
    Task.spawn (prio := prio) fun _ => (batch bs xs t).map f)

/-- Restore input order: sort by the recorded index, drop it. -/
def unsort {β : Type} (ys : List (β × Nat)) : List β :=
  (ys.mergeSort fun a b => decide (a.2 ≤ b.2)).map Prod.fst

/-- Sort by `le` (indices recorded), map in parallel bins, restore order. -/
def sortMap {α β : Type} (prio : Task.Priority) (bin : Nat) (le : α → α → Bool) (f : α → β)
    (xs : Array α) : Array β :=
  let sorted := (xs.toList.zipIdx.mergeSort fun a b => le a.1 b.1).toArray
  (unsort (parMapBins prio bin (fun q => (f q.1, q.2)) sorted).toList).toArray

/-- The distinct items of `xs`, in first-seen order. -/
def distinct {α : Type} [BEq α] [Hashable α] (xs : Array α) : Array α :=
  (xs.foldl (fun (acc : Std.HashSet α × Array α) x =>
    if acc.1.contains x then acc else (acc.1.insert x, acc.2.push x)) ({}, #[])).2

/-- A table from (item, answer) pairs. -/
def buildTable {α β : Type} [BEq α] [Hashable α] (ps : Array (α × β)) : Std.HashMap α β :=
  ps.foldl (fun m p => m.insert p.1 p.2) {}

/-- The answer for `x`: from the table, else computed. -/
def lookupOr {α β : Type} [BEq α] [Hashable α] (f : α → β) (tbl : Std.HashMap α β) (x : α) : β :=
  match tbl[x]? with
  | some v => v
  | none => f x

/-- Map the distinct items (sorted by `le`) in parallel bins, then look every
item up. -/
def dedupMap {α β : Type} [BEq α] [Hashable α] (prio : Task.Priority) (bin : Nat) (le : α → α → Bool)
    (f : α → β) (xs : Array α) : Array β :=
  let keys := ((distinct xs).toList.mergeSort le).toArray
  let tbl := buildTable (parMapBins prio bin (fun k => (k, f k)) keys)
  xs.map (lookupOr f tbl)

/-- The task of chunk `t` (text `h` of the chunk): after the task of chunk
`t - k` if there is one, else at once. -/
def nextTaskH {α : Type} (k b : Nat) (h : Array α → String) (xs : Array α)
    (acc : Array (Task String)) (t : Nat) : Task String :=
  if k ≤ t then
    match acc[t - k]? with
    | some p => p.map (prio := .dedicated) fun _ => h (batch b xs t)
    | none => Task.spawn (prio := .dedicated) fun _ => h (batch b xs t)
  else Task.spawn (prio := .dedicated) fun _ => h (batch b xs t)

/-- One task per chunk of `b` items, at most `w` at once, in input order. -/
def streamTasksH {α : Type} (w b : Nat) (h : Array α → String) (xs : Array α) : Array (Task String) :=
  (List.range (numBatches b xs.size)).foldl
    (fun acc t => acc.push (nextTaskH (max w 1) (max b 1) h xs acc t)) #[]

/-- The whole pipeline: chunks of `chunk` reads, `w` chunks at once; inside a
chunk, distinct reads sorted by `le`, mapped in bins of `bin` reads on the
task pool, looked up, formatted. -/
def pipelineTasks {α β : Type} [BEq α] [Hashable α] (w chunk bin : Nat) (le : α → α → Bool)
    (f : α → β) (fmt : β → String) (xs : Array α) : Array (Task String) :=
  streamTasksH w chunk (fun c => formatAll fmt (dedupMap .default bin le f c)) xs

end ParMap

/-! ## The theorems

    parMapBins prio b f xs = xs.map f                                 (parMapBins_eq_map)
    p ~ xs.zipIdx → unsort (p.map fun q => (f q.1, q.2)) = xs.map f   (unsort_map_perm)
    sortMap prio bin le f xs = xs.map f                               (sortMap_eq_map)
    dedupMap prio bin le f xs = xs.map f                              (dedupMap_eq_map)
    bytesOf ((pipelineTasks w chunk bin le f fmt xs).toList.map Task.get)
      = (formatAll fmt (xs.map f)).toUTF8                             (pipelineTasks_bytes)

For every priority, bin / chunk size and worker count (0 included), every
comparison `le` (no ordering laws needed) and every `f`; `dedupMap` needs
lawful `BEq` and `Hashable`.  With `f` equal to `mapSpec`, the `MapSpec`
corollaries (`sortMap_eq_mapSpec`, `dedupMap_eq_mapSpec`,
`pipelineTasks_bytes_mapSpec`) give the specification's answers / bytes. -/

/-! ## Proof -/

namespace ParMap

theorem joinTasks_range_bins {α β : Type} (prio : Task.Priority) (f : α → β) (xs : Array α) (b k : Nat) :
    joinTasks ((List.range k).map fun t => Task.spawn (prio := prio) fun _ => (batch b xs t).map f) =
      (xs.extract 0 (k * b)).map f := by
  unfold joinTasks
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    have hget : ∀ c : Array β, (Task.spawn (prio := prio) fun _ => c).get = c := fun _ => rfl
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hget, batch]
    rw [← Array.map_append, Array.extract_append_extract]
    congr 2 <;> simp [Nat.succ_mul]

theorem numBatches_max (b s : Nat) : numBatches (max b 1) s = numBatches b s := by
  simp [numBatches, Nat.max_def]; split <;> simp_all

/-- **Parallel map in bins is map.** -/
theorem parMapBins_eq_map {α β : Type} (prio : Task.Priority) (b : Nat) (f : α → β) (xs : Array α) :
    parMapBins prio b f xs = xs.map f := by
  unfold parMapBins
  simp only
  rw [joinTasks_range_bins, numBatches_max,
    Array.extract_eq_self_of_le (Nat.mul_comm _ _ ▸ size_le_batches b xs.size)]

/-- Two lists with the same items, both strictly ordered by an asymmetric
relation, are equal. -/
theorem eq_of_perm_of_pairwise {γ : Type} {R : γ → γ → Prop} (asymm : ∀ a b, R a b → ¬ R b a) :
    ∀ {l₁ l₂ : List γ}, l₁.Perm l₂ → l₁.Pairwise R → l₂.Pairwise R → l₁ = l₂
  | [], l₂, hp, _, _ => (List.Perm.nil_eq hp).symm.symm
  | a :: t, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t, b :: s, hp, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    by_cases hab : a = b
    · subst hab
      rw [eq_of_perm_of_pairwise asymm (hp.cons_inv) h₁.2 h₂.2]
    · have ha : a ∈ s := by
        have := hp.mem_iff.mp (List.mem_cons_self ..)
        rcases List.mem_cons.mp this with h | h
        · exact absurd h hab
        · exact h
      have hb : b ∈ t := by
        have := hp.mem_iff.mpr (List.mem_cons_self ..)
        rcases List.mem_cons.mp this with h | h
        · exact absurd h.symm hab
        · exact h
      exact absurd (h₂.1 a ha) (asymm _ _ (h₁.1 b hb))

/-- **Un-sorting restores input order**, whatever permutation was mapped. -/
theorem unsort_map_perm {α β : Type} (f : α → β) (xs : List α) (p : List (α × Nat))
    (hp : p.Perm xs.zipIdx) : unsort (p.map fun q => (f q.1, q.2)) = xs.map f := by
  let L := xs.zipIdx.map fun q => (f q.1, q.2)
  let le : β × Nat → β × Nat → Bool := fun a b => decide (a.2 ≤ b.2)
  have hsnd : L.map Prod.snd = List.range' 0 xs.length := by
    simp only [L, List.map_map]
    exact List.zipIdx_map_snd 0 xs
  have hfst : L.map Prod.fst = xs.map f := by
    simp only [L, List.map_map]
    conv => rhs; rw [← List.zipIdx_map_fst 0 xs, List.map_map]
    rfl
  have hS : (List.mergeSort (p.map fun q => (f q.1, q.2)) le).Perm L :=
    (List.mergeSort_perm _ _).trans (hp.map _)
  have hle := List.pairwise_mergeSort (le := le)
    (fun a b c h1 h2 => by simp [le] at *; omega) (fun a b => by simp [le]; omega)
    (p.map fun q => (f q.1, q.2))
  have hnd : ((List.mergeSort (p.map fun q => (f q.1, q.2)) le).map Prod.snd).Nodup := by
    have := (hS.map Prod.snd).nodup_iff.mpr (hsnd ▸ List.nodup_range')
    exact this
  rw [List.Nodup, List.pairwise_map] at hnd
  have hlt : (List.mergeSort (p.map fun q => (f q.1, q.2)) le).Pairwise (fun a b => a.2 < b.2) :=
    (hle.and hnd).imp fun ⟨h1, h2⟩ => by simp [le] at h1; omega
  have hL : L.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := xs.length)
    rw [← hsnd, List.pairwise_map] at this
    exact this
  unfold unsort
  rw [eq_of_perm_of_pairwise (fun a b h1 h2 => by omega) hS hlt hL, hfst]

/-- **Sort, map in parallel, un-sort is map.** -/
theorem sortMap_eq_map {α β : Type} (prio : Task.Priority) (bin : Nat) (le : α → α → Bool) (f : α → β)
    (xs : Array α) : sortMap prio bin le f xs = xs.map f := by
  unfold sortMap
  simp only
  rw [parMapBins_eq_map, Array.toList_map, List.toList_toArray,
    unsort_map_perm f xs.toList _ (List.mergeSort_perm _ _)]
  cases xs; simp

theorem buildTable_sound {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (f : α → β) (ps : Array (α × β)) (hps : ∀ p ∈ ps, p.2 = f p.1) :
    ∀ a v, (buildTable ps)[a]? = some v → v = f a := by
  unfold buildTable
  rw [← Array.foldl_toList]
  have hl : ∀ p ∈ ps.toList, p.2 = f p.1 := fun p hp => hps p (Array.mem_toList_iff.mp hp)
  suffices ∀ (l : List (α × β)) (m : Std.HashMap α β), (∀ p ∈ l, p.2 = f p.1) →
      (∀ a v, m[a]? = some v → v = f a) →
      ∀ a v, (l.foldl (fun m p => m.insert p.1 p.2) m)[a]? = some v → v = f a from
    this _ _ hl (fun a v h => by simp at h)
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons p l ih =>
    intro m hpl hm
    apply ih _ (fun q hq => hpl q (List.mem_cons_of_mem _ hq))
    intro a v h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next hk =>
      have := LawfulBEq.eq_of_beq hk
      subst this
      simp at h; subst h
      exact hpl p (List.mem_cons_self ..)
    · exact hm a v h

theorem lookupOr_eq {α β : Type} [BEq α] [Hashable α] (f : α → β) (tbl : Std.HashMap α β)
    (htbl : ∀ a v, tbl[a]? = some v → v = f a) (x : α) : lookupOr f tbl x = f x := by
  unfold lookupOr
  split
  · next v h => exact htbl x v h
  · rfl

/-- **Map the distinct items, look every item up: map.** -/
theorem dedupMap_eq_map {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (prio : Task.Priority) (bin : Nat) (le : α → α → Bool) (f : α → β) (xs : Array α) :
    dedupMap prio bin le f xs = xs.map f := by
  unfold dedupMap
  simp only
  apply Array.map_congr_left
  intro x _
  apply lookupOr_eq
  apply buildTable_sound
  intro p hp
  rw [parMapBins_eq_map] at hp
  obtain ⟨k, _, rfl⟩ := Array.mem_map.mp hp
  rfl

theorem nextTaskH_get {α : Type} (k b : Nat) (h : Array α → String) (xs : Array α)
    (acc : Array (Task String)) (t : Nat) :
    (nextTaskH k b h xs acc t).get = h (batch b xs t) := by
  unfold nextTaskH
  split
  · split <;> rfl
  · rfl

theorem streamTasksH_gets {α : Type} (k b : Nat) (h : Array α → String) (xs : Array α) (n : Nat) :
    ((List.range n).foldl (fun acc t => acc.push (nextTaskH k b h xs acc t)) #[]).toList.map Task.get =
      (List.range n).map (fun t => h (batch b xs t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_push,
      List.map_append, ih, List.map_append]
    simp [nextTaskH_get]

/-- **Streamed chunks**: if each chunk's text is the text of the chunk mapped
by `f`, the texts in order are the text of the whole input mapped by `f`. -/
theorem streamTasksH_text {α β : Type} (w b : Nat) (h : Array α → String) (f : α → β)
    (fmt : β → String) (hh : ∀ c, h c = formatAll fmt (c.map f)) (xs : Array α) :
    String.join ((streamTasksH w b h xs).toList.map Task.get) = formatAll fmt (xs.map f) := by
  unfold streamTasksH
  rw [streamTasksH_gets]
  have : (List.range (numBatches b xs.size)).map (fun t => h (batch (max b 1) xs t)) =
      (List.range (numBatches (max b 1) xs.size)).map (chunkText (max b 1) f fmt xs) := by
    rw [numBatches_max]
    exact List.map_congr_left fun t _ => hh _
  have h2 := size_le_numBatches (max b 1) xs.size
  rw [Nat.max_eq_left (Nat.le_max_right b 1)] at h2
  rw [this, join_chunkText, Array.extract_eq_self_of_le h2]

/-- **The whole pipeline's bytes** are the bytes of the text of the input
mapped by `f`, in input order. -/
theorem pipelineTasks_bytes {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (w chunk bin : Nat) (le : α → α → Bool) (f : α → β) (fmt : β → String) (xs : Array α) :
    bytesOf ((pipelineTasks w chunk bin le f fmt xs).toList.map Task.get) =
      (formatAll fmt (xs.map f)).toUTF8 := by
  rw [bytesOf_eq]
  unfold pipelineTasks
  rw [streamTasksH_text w chunk _ f fmt (fun c => by rw [dedupMap_eq_map])]

end ParMap

namespace MapSpec

open AlignmentSpec ParMap

theorem sortMap_eq_mapSpec (prio : Task.Priority) (bin : Nat) (le : List Char → List Char → Bool)
    (sc : Scoring) (T : Int) (g : Genome) (f : List Char → Option (Window × Int))
    (hf : ∀ read, f read = mapSpec sc T g read) (reads : Array (List Char)) :
    sortMap prio bin le f reads = reads.map (mapSpec sc T g) := by
  rw [sortMap_eq_map]; exact Array.map_congr_left fun r _ => hf r

theorem dedupMap_eq_mapSpec (prio : Task.Priority) (bin : Nat) (le : List Char → List Char → Bool)
    (sc : Scoring) (T : Int) (g : Genome) (f : List Char → Option (Window × Int))
    (hf : ∀ read, f read = mapSpec sc T g read) (reads : Array (List Char)) :
    dedupMap prio bin le f reads = reads.map (mapSpec sc T g) := by
  rw [dedupMap_eq_map]; exact Array.map_congr_left fun r _ => hf r

/-- **Pipeline (chunk → distinct, sorted, binned, parallel map → restore order →
bytes)** of any per-read function equal to `mapSpec`: the bytes of the text of
the specification's answers. -/
theorem pipelineTasks_bytes_mapSpec (w chunk bin : Nat) (le : List Char → List Char → Bool)
    (sc : Scoring) (T : Int) (g : Genome) (f : List Char → Option (Window × Int))
    (hf : ∀ read, f read = mapSpec sc T g read) (fmt : Option (Window × Int) → String)
    (reads : Array (List Char)) :
    bytesOf ((pipelineTasks w chunk bin le f fmt reads).toList.map Task.get) =
      (formatAll fmt (reads.map (mapSpec sc T g))).toUTF8 := by
  rw [pipelineTasks_bytes]
  congr 2; exact Array.map_congr_left fun r _ => hf r

end MapSpec

#print axioms ParMap.parMapBins_eq_map
#print axioms ParMap.unsort_map_perm
#print axioms ParMap.sortMap_eq_map
#print axioms ParMap.dedupMap_eq_map
#print axioms ParMap.pipelineTasks_bytes
#print axioms MapSpec.sortMap_eq_mapSpec
#print axioms MapSpec.dedupMap_eq_mapSpec
#print axioms MapSpec.pipelineTasks_bytes_mapSpec
