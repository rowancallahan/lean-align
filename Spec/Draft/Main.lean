import Spec.Draft.MapFiles

open Spec

def blockSize : USize := 8 * 1024 * 1024

def fail (tmpPath why : String) : IO UInt32 := do
  IO.FS.removeFile tmpPath
  IO.eprintln s!"lean-align: {why}"
  return 1

-- `mapFilesFast_correct`, run on the files: start, one step per pair of blocks, end
def mapFilesIO (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (file1 file2 out : IO.FS.Handle) : IO (Option Unit) := do
  -- start
  let (start, header) := Total.mapStart settings index chrs
  out.write header
  -- one step per pair of blocks, in order
  let mut state := start
  repeat
    let block1 ← file1.read blockSize
    let block2 ← file2.read blockSize
    match block1.isEmpty && block2.isEmpty with
    | true  => break
    | false =>
      match Total.mapStep state block1 block2 with
      | some (next, piece) =>
        out.write piece
        state := next
      | none =>
        return none
  -- end
  match Total.mapEnd state with
  | some last =>
    out.write last
    return some ()
  | none =>
    return none

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
    match ← mapFilesIO settings index chrs file1 file2 out with
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
