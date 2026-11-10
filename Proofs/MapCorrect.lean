import Proofs.MapRun
/-! # `process_correct` (Spec/MapFiles.lean), proved from `job_eq` (one job of the stream = `mapReads` of its two slices).
The statement is the Spec's, with `job_eq` as a hypothesis; `Spec.Total.process_correct` in Proofs/MapFiles.lean is this theorem
once that file can import the proof modules (they import it for `mapReads`: move the definitions below `mapStep` into their own module). -/
namespace Spec.MapCopy
open Spec Spec.FQ.MapStream

-- what we use of the Spec's loop `process` (an equation lemma of its structural recursion on `fuel`, `rfl` there)
def ProcSucc (proc : Nat → MapState → StateM Files (Option Unit)) : Prop :=
  ∀ (f : Nat) (st : MapState), proc (f + 1) st = (do
    let chunks ← nextChunksList
    match mapStep st chunks, chunks with
    | none, _ =>
      pure none
    | some (state', lines), none =>
      writeList lines
      pure (some ())
    | some (state', lines), some _ =>
      writeList lines
      proc f state')

-- the Spec's `process` on a list of chunks: start, one `mapStep` per pair of chunks, end (as `Spec.Total.MapProcess.process_fold`, for the Spec's loop)
theorem process_fold' (proc : Nat → MapState → StateM Files (Option Unit)) (hs : ProcSucc proc) : ∀ (blocks : List (ByteArray × ByteArray)) (fuel : Nat), blocks.length < fuel →
    ∀ (st : MapState) (out : List UInt8),
    let r := (proc fuel st).run (blocks, out)
    r.1.map (fun () => r.2.2) = Spec.Total.MapProcess.fold mapStep st out blocks
  | [], fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    rw [hs]
    simp only [nextChunksList, writeList, Spec.Total.MapProcess.fold]
    cases hst : mapStep st none with
    | none => simp [hst, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure]
    | some p =>
      obtain ⟨st', piece⟩ := p
      simp [hst, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, MonadStateOf.modifyGet, bytes]
  | bp :: rest, fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    rw [hs]
    simp only [nextChunksList, writeList, Spec.Total.MapProcess.fold]
    cases hst : mapStep st (some bp) with
    | none => simp [hst, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure, List.foldlM]
    | some p =>
      obtain ⟨st', piece⟩ := p
      have ih := process_fold' proc hs rest f (by simp at h; omega) st' (out ++ bytes piece)
      simp only [Spec.Total.MapProcess.fold] at ih
      simp [hst, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, List.foldlM, bytes]
      try simp only [nextChunksList] at ih
      exact ih

theorem process_correct' (proc : Nat → MapState → StateM Files (Option Unit)) (hs : ProcSucc proc) (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job_eq : ∀ s1 s2, (MapFast.job settings index chrs s1 s2).map bytes =
      mapReads settings index chrs (bytes s1) (bytes s2))
    (chunks : List (ByteArray × ByteArray)) (fuel : Nat) (enough : chunks.length < fuel) :
    let state := mapInit settings index chrs
    let (result, (_, written)) := (proc fuel state).run (chunks, [])
    let fastq1 := chunks.flatMap fun (chunk1, _) => bytes chunk1
    let fastq2 := chunks.flatMap fun (_, chunk2) => bytes chunk2
    (match result with
     | some () => some written
     | none    => none)
      = mapReads settings index chrs fastq1 fastq2 := by
  intro state
  have hp := process_fold' proc hs chunks fuel enough state []
  have hf := fold_correct settings index chrs (MapFast.job settings index chrs) job_eq chunks state [] [] []
    (finv_init _ _)
  have hall := hp.trans hf
  generalize hrun : StateT.run (proc fuel state) (chunks, []) = r at hall ⊢
  obtain ⟨res, rest, written⟩ := r
  cases res with
  | none => simpa [bytes, bl] using hall
  | some u => simpa [bytes, bl] using hall

end Spec.MapCopy
#print axioms Spec.MapCopy.process_correct'
