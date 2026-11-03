import Proofs.Sam
import IoFast

/-! Benchmark only (prints to stdout). Per FASTQ chunk, the same steps as `Main.lean`'s `map` loop, run one after the other and timed:
the serial `readChunk` (parse + trim), the proved `alignPairs` (all cores), and `samChunk` (format).

    lake exe io_bench MODE INDEX READS_1.fq READS_2.fq CHUNK_PAIRS      MODE = old | fast | compare

`old` = Spec.readChunk / Spec.samChunk; `fast` = IoFast.readChunkFast / IoFast.samChunkFast (prototype, unproved);
`compare` runs both on the same chunks and checks that the letters, qualities and the SAM bytes are identical.

Run with `taskset -c 0-3` for 4 cores. Prints one line per chunk and the totals; nothing is written to disk.
Whether reading is the bottleneck of the pipelined shim: compare `read` with `align` (the shim reads chunk n+1 while it aligns chunk n). -/

def Spec.chunkPairsB (chunk : Array (Spec.FastqRecord × Spec.FastqRecord)) :
    List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (record1, record2) =>
    (if record1.letters.isEmpty then none else some record1.letters,
     if record2.letters.isEmpty then none else some record2.letters)

def chunkPairsF (chunk : Array (IoFast.FRec × IoFast.FRec)) : List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (a, b) => (if a.letters.isEmpty then none else some a.letters, if b.letters.isEmpty then none else some b.letters)

def force (results : List Spec.PairResult) : Nat :=
  results.foldl (fun acc r => acc + match r with | .aligned a => (if a.found.isSome then 2 else 1) | _ => 1) 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, indexPath, r1, r2, chunkPairs] =>
    let insertSettings : Spec.InsertSettings := { range := (100, 1000) }
    let index ← IO.FS.readBinFile indexPath
    let chromosomes ← Spec.readChromosomeList (indexPath ++ ".chromosomes")
    let n := chunkPairs.toNat!
    let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
    let reads2 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
    let f1 ← IoFast.Reader.ofHandle (← IO.FS.Handle.mk r1 .read)
    let f2 ← IoFast.Reader.ofHandle (← IO.FS.Handle.mk r2 .read)
    let mut tRead := 0; let mut tAlign := 0; let mut tSam := 0; let mut cnt := 0; let mut bytes := 0; let mut same := true
    repeat
      let t0 ← IO.monoMsNow
      let old ← if mode == "fast" then pure #[] else Spec.readChunk reads1 reads2 n
      let t1 ← IO.monoMsNow
      let fast ← if mode == "old" then pure #[] else IoFast.readChunkFast f1 f2 n 16
      let t1b ← IO.monoMsNow
      if old.isEmpty && fast.isEmpty then break
      let pairs := if mode == "fast" then chunkPairsF fast else Spec.chunkPairsB old
      let results := Spec.alignPairs insertSettings index pairs
      let nres := force results
      let t2 ← IO.monoMsNow
      let text := if mode == "fast" then (IoFast.samChunkFast chromosomes fast results 16) else Spec.samChunk chromosomes old results 16
      let size := text.size
      let t3 ← IO.monoMsNow
      let mut note := ""
      if mode == "compare" then
        if chunkPairsF fast != Spec.chunkPairsB old then same := false; note := " LETTERS DIFFER"
        let text2 := IoFast.samChunkFast chromosomes fast results 16
        if text2 != text then same := false; note := note ++ " SAM DIFFERS"
      let rd := if mode == "fast" then t1b - t1 else t1 - t0
      IO.println s!"chunk {cnt}: {max old.size fast.size} pairs ({nres}) read {rd} ms{if mode == "compare" then s!" (fast {t1b - t1} ms)" else ""}, align {t2 - t1b} ms, sam {t3 - t2} ms ({size} bytes){note}"
      tRead := tRead + rd; tAlign := tAlign + (t2 - t1b); tSam := tSam + (t3 - t2); cnt := cnt + 1; bytes := bytes + size
    IO.println s!"TOTAL {mode} {cnt} chunks: read {tRead} ms, align {tAlign} ms, sam {tSam} ms, sam bytes {bytes}{if mode == "compare" then (if same then " IDENTICAL" else " DIFFERENT") else ""}"
    return 0
  | _ => IO.eprintln "usage: io_bench old|fast|compare INDEX R1.fq R2.fq CHUNK_PAIRS"; return 1
