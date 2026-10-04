import ParMap                      -- parMap, batches, mapReadsParArray

/-!
# Codec `streamTasks`: map in batches, write while mapping

The input is cut into batches of `b` items.  Batch `t` is mapped and
formatted to text in its own dedicated task; with `k` workers, batch `t`
starts when batch `t - k` is done, so at most `k` batches compute at once.
A writer (IO, outside this file) takes the tasks in input order, waits for
each and writes its text; later batches keep computing meanwhile.

The theorem: the texts of the tasks, in order, concatenated, are the text of
the whole mapped input.  So whatever the writer writes is
`formatAll fmt (xs.map f)`, and for a mapper proved equal to `mapSpec` it is
the specification's output.

The algorithm, then the theorems, then the proof.
-/

namespace ParMap

/-! ## The algorithm -/

/-- The text of some results: each formatted, concatenated in order. -/
def formatAll {β : Type} (fmt : β → String) (ys : Array β) : String :=
  String.join (ys.toList.map fmt)

/-- The text of batch `t`, mapped. -/
def chunkText {α β : Type} (b : Nat) (f : α → β) (fmt : β → String) (xs : Array α) (t : Nat) : String :=
  formatAll fmt ((batch b xs t).map f)

/-- Number of batches of `b` items (`b` at least 1): `⌈size / b⌉`. -/
def numBatches (b size : Nat) : Nat := (size + max b 1 - 1) / max b 1

/-- The task of batch `t`: after the task of batch `t - k` if there is one,
else at once. -/
def nextTask {α β : Type} (k b : Nat) (f : α → β) (fmt : β → String) (xs : Array α)
    (acc : Array (Task String)) (t : Nat) : Task String :=
  if k ≤ t then
    match acc[t - k]? with
    | some p => p.map (prio := .dedicated) fun _ => chunkText b f fmt xs t
    | none => Task.spawn (prio := .dedicated) fun _ => chunkText b f fmt xs t
  else Task.spawn (prio := .dedicated) fun _ => chunkText b f fmt xs t

/-- One task per batch of `b` items, at most `workers` computing at once,
in input order. -/
def streamTasks {α β : Type} (workers b : Nat) (f : α → β) (fmt : β → String) (xs : Array α) :
    Array (Task String) :=
  (List.range (numBatches b xs.size)).foldl
    (fun acc t => acc.push (nextTask (max workers 1) (max b 1) f fmt xs acc t)) #[]

end ParMap

/-! ## The theorems

    String.join ((streamTasks w b f fmt xs).toList.map Task.get) = formatAll fmt (xs.map f)
                                                                   (streamTasks_text)
    (∀ r, f r = mapSpec sc T g r) →
    String.join ((streamTasks w b f fmt reads).toList.map Task.get)
      = formatAll fmt (reads.map (mapSpec sc T g))                 (streamTasks_text_mapSpec)

For every number of workers, batch size (0 included), function and format. -/

/-! ## Proof -/

namespace ParMap

theorem formatAll_append {β : Type} (fmt : β → String) (a c : Array β) :
    formatAll fmt (a ++ c) = formatAll fmt a ++ formatAll fmt c := by
  simp [formatAll, String.join_append]

theorem nextTask_get {α β : Type} (k b : Nat) (f : α → β) (fmt : β → String) (xs : Array α)
    (acc : Array (Task String)) (t : Nat) :
    (nextTask k b f fmt xs acc t).get = chunkText b f fmt xs t := by
  unfold nextTask
  split
  · split <;> rfl
  · rfl

theorem streamTasks_gets {α β : Type} (k b : Nat) (f : α → β) (fmt : β → String) (xs : Array α) (n : Nat) :
    ((List.range n).foldl (fun acc t => acc.push (nextTask k b f fmt xs acc t)) #[]).toList.map Task.get =
      (List.range n).map (chunkText b f fmt xs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_push,
      List.map_append, ih, List.map_append]
    simp [nextTask_get]

theorem join_chunkText {α β : Type} (b : Nat) (f : α → β) (fmt : β → String) (xs : Array α) (n : Nat) :
    String.join ((List.range n).map (chunkText b f fmt xs)) = formatAll fmt ((xs.extract 0 (n * b)).map f) := by
  induction n with
  | zero => simp [formatAll]
  | succ n ih =>
    rw [List.range_succ, List.map_append, String.join_append, ih]
    simp only [List.map_cons, List.map_nil, String.join_cons, String.join_nil, String.append_empty,
      chunkText, batch]
    rw [← formatAll_append, ← Array.map_append, Array.extract_append_extract]
    congr 3 <;> simp [Nat.succ_mul]

theorem size_le_numBatches (b s : Nat) : s ≤ numBatches b s * max b 1 := by
  rw [Nat.mul_comm]
  exact size_le_batches b s

/-- **What the writer writes is the text of the whole mapped input.** -/
theorem streamTasks_text {α β : Type} (w b : Nat) (f : α → β) (fmt : β → String) (xs : Array α) :
    String.join ((streamTasks w b f fmt xs).toList.map Task.get) = formatAll fmt (xs.map f) := by
  unfold streamTasks
  rw [streamTasks_gets, join_chunkText]
  have h : numBatches b xs.size = numBatches (max b 1) xs.size := by
    simp [numBatches, Nat.max_def]; split <;> simp_all
  rw [Array.extract_eq_self_of_le (h ▸ size_le_numBatches b xs.size)]

end ParMap

namespace MapSpec

open AlignmentSpec ParMap

/-- **Streamed output of any per-read function equal to `mapSpec`** is the
text of the specification's answers. -/
theorem streamTasks_text_mapSpec (w b : Nat) (sc : Scoring) (T : Int) (g : Genome)
    (f : List Char → Option (Window × Int)) (hf : ∀ read, f read = mapSpec sc T g read)
    (fmt : Option (Window × Int) → String) (reads : Array (List Char)) :
    String.join ((streamTasks w b f fmt reads).toList.map Task.get) =
      formatAll fmt (reads.map (mapSpec sc T g)) := by
  rw [streamTasks_text]
  exact congrArg _ (Array.map_congr_left (fun r _ => hf r))

end MapSpec

#print axioms ParMap.streamTasks_text
#print axioms MapSpec.streamTasks_text_mapSpec
