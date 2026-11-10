-- LOCKED (Rowan, 2026-11-10): the streaming main; it runs `process` of `process_correct`.
import Proofs.MapFiles

open Spec

def chunkSize : USize := 8 * 1024 * 1024

def fail (tmpPath why : String) : IO UInt32 := do
  IO.FS.removeFile tmpPath
  IO.eprintln s!"lean-align: {why}"
  return 1

def fuel : Nat := 2 ^ 64

-- the next chunk of each FASTQ file; none when both files have ended
def nextChunks (fastq1 fastq2 : IO.FS.Handle) : IO (Option (ByteArray × ByteArray)) := do
  let chunk1 ← fastq1.read chunkSize
  let chunk2 ← fastq2.read chunkSize
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
    match ← Total.process (nextChunks fastq1 fastq2) out.write fuel state with
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
