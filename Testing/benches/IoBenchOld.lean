import Proofs.Sam

/-! Benchmark only. Per FASTQ chunk, the steps of `Main.lean`'s `map` loop (festive d0d2a79) run one after the other and timed:
`readChunk` (serial parse), `trimChunk` (16 tasks), `alignPairs` (all cores; every result is forced), `samChunk` (16 tasks).
    lake exe io_bench_old INDEX R1.fq R2.fq CHUNK_PAIRS        (run with taskset -c 0-3 for 4 cores)
Check that the SAM is mostly mapped (the index must be built by the same commit): the line `mapped` below. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [indexPath, r1, r2, chunkPairs] =>
    let insertSettings : Spec.InsertSettings := { range := (100, 1000) }
    let index ← IO.FS.readBinFile indexPath
    let chromosomes ← Spec.readChromosomeList (indexPath ++ ".chromosomes")
    let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
    let reads2 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
    let mut tRead := 0; let mut tTrim := 0; let mut tAlign := 0; let mut tSam := 0; let mut cnt := 0; let mut mapped := 0; let mut pairs := 0
    repeat
      let t0 ← IO.monoMsNow
      let raw ← Spec.readChunk reads1 reads2 chunkPairs.toNat!
      let t1 ← IO.monoMsNow
      if raw.isEmpty then break
      let chunk := Spec.trimChunk raw 16
      let nt := chunk.size
      let t2 ← IO.monoMsNow
      let results := Spec.alignPairs insertSettings index (Spec.chunkPairs chunk)
      let m := results.foldl (fun acc r => acc + match r with | .aligned a => (if a.found.isSome then 1 else 0) | _ => 0) 0
      let t3 ← IO.monoMsNow
      let text := Spec.samChunk chromosomes chunk results 16
      let size := text.size
      let t4 ← IO.monoMsNow
      IO.println s!"chunk {cnt}: {nt} pairs, mapped {m}, read {t1 - t0} ms, trim {t2 - t1} ms, align {t3 - t2} ms, sam {t4 - t3} ms ({size} bytes)"
      tRead := tRead + (t1 - t0); tTrim := tTrim + (t2 - t1); tAlign := tAlign + (t3 - t2); tSam := tSam + (t4 - t3)
      cnt := cnt + 1; mapped := mapped + m; pairs := pairs + nt
    IO.println s!"TOTAL {cnt} chunks: {pairs} pairs, mapped {mapped}, read {tRead} ms, trim {tTrim} ms, align {tAlign} ms, sam {tSam} ms"
    return 0
  | _ => IO.eprintln "usage: io_bench_old INDEX R1.fq R2.fq CHUNK_PAIRS"; return 1
