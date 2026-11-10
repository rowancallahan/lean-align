import Proofs.MapRun
/-! # `process_correct` (Spec/MapFiles.lean), proved from `job_eq` (one job of the stream = `mapReads` of its two slices).
The statement is the Spec's, with `job_eq` as a hypothesis; `Spec.Total.process_correct` in Proofs/MapFiles.lean is this theorem
once that file can import the proof modules (they import it for `mapReads`: move the definitions below `mapStep` into their own module). -/
namespace Spec.Total
open Spec Spec.FQ.MapStream

-- the Spec's `process` on a list of chunks: start, one `mapStep` per pair of chunks, end (as `MapProcess.process_fold`, for the Spec's loop)
theorem process_fold' : ∀ (blocks : List (ByteArray × ByteArray)) (fuel : Nat), blocks.length < fuel →
    ∀ (st : MapState) (out : List UInt8),
    let r := (process nextChunksList writeList fuel st).run (blocks, out)
    r.1.map (fun () => r.2.2) = MapProcess.fold mapStep st out blocks
  | [], fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    simp only [process, nextChunksList, writeList, MapProcess.fold]
    cases hs : mapStep st none with
    | none => simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure]
    | some p =>
      obtain ⟨st', piece⟩ := p
      simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, MonadStateOf.modifyGet, bytes]
  | bp :: rest, fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    simp only [process, nextChunksList, writeList, MapProcess.fold]
    cases hs : mapStep st (some bp) with
    | none => simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure, List.foldlM]
    | some p =>
      obtain ⟨st', piece⟩ := p
      have ih := process_fold' rest f (by simp at h; omega) st' (out ++ bytes piece)
      simp only [MapProcess.fold] at ih
      simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, List.foldlM, bytes]
      simp only [nextChunksList] at ih
      exact ih

theorem process_correct' (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job_eq : ∀ s1 s2, (MapFast.job settings index chrs s1 s2).map bytes =
      mapReads settings index chrs (bytes s1) (bytes s2))
    (chunks : List (ByteArray × ByteArray)) (fuel : Nat) (enough : chunks.length < fuel) :
    let state := mapInit settings index chrs
    let (result, (_, written)) := (process nextChunksList writeList fuel state).run (chunks, [])
    let fastq1 := chunks.flatMap fun (chunk1, _) => bytes chunk1
    let fastq2 := chunks.flatMap fun (_, chunk2) => bytes chunk2
    (match result with
     | some () => some written
     | none    => none)
      = mapReads settings index chrs fastq1 fastq2 := by
  intro state
  have hp := process_fold' chunks fuel enough state []
  have hf := fold_correct settings index chrs (MapFast.job settings index chrs) job_eq chunks state [] [] []
    (finv_init _ _)
  have hall := hp.trans hf
  generalize hrun : StateT.run (process nextChunksList writeList fuel state) (chunks, []) = r at hall ⊢
  obtain ⟨res, rest, written⟩ := r
  cases res with
  | none => simpa [bytes, bl] using hall
  | some u => simpa [bytes, bl] using hall

end Spec.Total
#print axioms Spec.Total.process_correct'
