-- PROPOSED (needs Rowan): Main with one read-ahead thread per FASTQ file; runs `process` of `process_correct`.
import Proofs.MapFiles
import Std.Sync.Channel

open Spec

def chunkSize : USize := 8 * 1024 * 1024

def fail (tmpPath why : String) : IO UInt32 := do
  IO.FS.removeFile tmpPath
  IO.eprintln s!"lean-align: {why}"
  return 1

def fuel : Nat := 2 ^ 64

-- up to `chunkSize` bytes: a pipe returns at most ~64 KB per read, so reads are repeated until the
-- chunk is full or the file has ended (empty only at the end of the file)
def readFull (fastq : IO.FS.Handle) : IO ByteArray := do
  let mut chunk ← fastq.read chunkSize
  repeat
    match decide (chunkSize.toNat ≤ chunk.size), chunk.isEmpty with
    | true, _ | _, true => break
    | false, false =>
      let more ← fastq.read (chunkSize - chunk.size.toUSize)
      match more.isEmpty with
      | true  => break
      | false => chunk := chunk ++ more
  return chunk

-- each FASTQ file is read on its own thread, a few chunks ahead, so both files (and the
-- decompressors feeding them through pipes) keep going while the chunks are mapped.
-- A read error stops the program at once (exit 1).
def readAhead (fastq : IO.FS.Handle) : IO (Std.CloseableChannel.Sync ByteArray) := do
  let chunks ← Std.CloseableChannel.Sync.new (some 4)
  let _ ← IO.asTask (prio := .dedicated) do
    try
      repeat
        let chunk ← readFull fastq
        match chunk.isEmpty with
        | true  => break
        | false => chunks.send chunk
      chunks.close
    catch e =>
      IO.eprintln s!"lean-align: reading a FASTQ file: {e}"
      IO.Process.exit 1
  return chunks

-- the next chunk of each FASTQ file, in order; none when both files have ended
def nextChunks (chunks1 chunks2 : Std.CloseableChannel.Sync ByteArray) :
    IO (Option (ByteArray × ByteArray)) := do
  let chunk1 := (← chunks1.recv).getD ByteArray.empty
  let chunk2 := (← chunks2.recv).getD ByteArray.empty
  match chunk1.isEmpty && chunk2.isEmpty with
  | true  => return none
  | false => return some (chunk1, chunk2)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["map", indexPath, reads1Path, reads2Path, outPath, minFragment, maxFragment] =>
    let settings : InsertSettings := { range := (minFragment.toNat!, maxFragment.toNat!) }
    -- TRUSTED: the index file is `buildIndex` of the genome,
    -- and INDEX.chromosomes lists its chromosomes
    let index ← IO.FS.readBinFile indexPath
    let chrs ← readChromosomeList (indexPath ++ ".chromosomes")
    let fastq1 ← IO.FS.Handle.mk reads1Path .read
    let fastq2 ← IO.FS.Handle.mk reads2Path .read
    -- written to OUT.tmp, renamed to OUT only when everything succeeded
    let tmpPath := outPath ++ ".tmp"
    let out ← IO.FS.Handle.mk tmpPath .write
    -- the header, then `process` exactly as in `process_correct`,
    -- with the FASTQ files as `nextChunks` and the output file as `out.write`
    out.write ⟨(SamSpec.header chrs).toArray⟩
    let state := Total.mapInit settings index chrs
    let chunks1 ← readAhead fastq1
    let chunks2 ← readAhead fastq2
    match ← Total.process (nextChunks chunks1 chunks2) out.write fuel state with
    | some () =>
      out.flush
      IO.FS.rename tmpPath outPath
      return 0
    | none =>
      fail tmpPath "the FASTQ files are not valid, matching FASTQ"
  | ["build", genomePath, indexPath] =>
    let genome ← readFasta (← IO.FS.Handle.mk genomePath .read)
    IO.FS.writeBinFile indexPath (buildIndex genome)
    IO.FS.writeFile (indexPath ++ ".chromosomes") (chromosomeListText genome)
    return 0
  | _ =>
    IO.eprintln "usage: lean-align build GENOME.fa INDEX"
    IO.eprintln "       lean-align map INDEX READS_1.fq READS_2.fq OUT.sam MIN_FRAGMENT MAX_FRAGMENT"
    return 1
