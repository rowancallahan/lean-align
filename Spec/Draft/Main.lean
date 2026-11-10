-- DRAFT (Rowan to re-lock): the streaming main; it runs `process` of `process_correct`.
import Spec.Draft.MapFiles

open Spec

def blockSize : USize := 8 * 1024 * 1024

def fail (tmpPath why : String) : IO UInt32 := do
  IO.FS.removeFile tmpPath
  IO.eprintln s!"lean-align: {why}"
  return 1

def fuel : Nat := 2 ^ 64

-- the next pair of blocks, one from each file; none when both files have ended
def nextBlocks (file1 file2 : IO.FS.Handle) : IO (Option (ByteArray × ByteArray)) := do
  let block1 ← file1.read blockSize
  let block2 ← file2.read blockSize
  match block1.isEmpty && block2.isEmpty with
  | true  => return none
  | false => return some (block1, block2)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["map", indexPath, reads1Path, reads2Path, outPath, minFragment, maxFragment] =>
    let settings : InsertSettings := { range := (minFragment.toNat!, maxFragment.toNat!) }
    -- TRUSTED: the index file is `buildIndex` of the genome, and INDEX.chromosomes lists its chromosomes
    let index ← IO.FS.readBinFile indexPath
    let chrs ← readChromosomeList (indexPath ++ ".chromosomes")
    let file1 ← IO.FS.Handle.mk reads1Path .read
    let file2 ← IO.FS.Handle.mk reads2Path .read
    -- written to OUT.tmp, renamed to OUT only when everything succeeded
    let tmpPath := outPath ++ ".tmp"
    let out ← IO.FS.Handle.mk tmpPath .write
    -- `process` of `process_correct`, with the files as `next` and the output file as `emit`
    match ← Total.process (nextBlocks file1 file2) out.write fuel (Total.mapInit settings index chrs) with
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
    IO.eprintln "usage: lean-align build GENOME.fa INDEX\n       lean-align map INDEX READS_1.fq READS_2.fq OUT.sam MIN_FRAGMENT MAX_FRAGMENT"
    return 1
