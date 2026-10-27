-- The lean-align executable: Spec/Shim.lean line for line, importing Proofs (the proved buildIndex / alignPairs) instead of Spec.
import Proofs.Sam

/-! # The execution shim. `build` reads the FASTA and saves the index; `map` reads only the index,
then reads pairs in chunks, calls `alignPairs` once per chunk, and writes SAM.
Everything here except the boxed `alignPairs` call is unproved plumbing (reading, writing).
Stand-ins for now: no trimming (every mate is `some`). -/

-- a chunk of read pairs, as `alignPairs` takes them
def Spec.chunkPairs (chunk : Array (Spec.FastqRecord × Spec.FastqRecord)) :
    List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (record1, record2) => (some record1.letters, some record2.letters)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["build", genomePath, indexPath] =>
    let byteGenome := Spec.parseFasta (← IO.FS.readFile genomePath)
    IO.FS.writeBinFile indexPath (Spec.buildIndex byteGenome)
    IO.FS.writeFile (indexPath ++ ".chromosomes") (Spec.chromosomeListText byteGenome)
    return 0
  | ["map", indexPath, reads1Path, reads2Path, outPath, minFragment, maxFragment] =>
    let insertSettings : Spec.InsertSettings := { range := (minFragment.toNat!, maxFragment.toNat!) }
    -- TRUSTED: the index file is `buildIndex byteGenome` for the genome (the theorem's `hIndex`),
    -- and INDEX.chromosomes lists that genome's names and lengths
    let index ← IO.FS.readBinFile indexPath
    let chromosomes ← Spec.readChromosomeList (indexPath ++ ".chromosomes")
    let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk reads1Path .read)
    let reads2 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk reads2Path .read)
    let out ← IO.FS.Handle.mk outPath .write
    for line in Spec.samHeader chromosomes do
      out.putStrLn line
    -- pipelined: the next chunk is read, and the previous one written, while this one is aligned
    let mut next ← IO.asTask (Spec.readChunk reads1 reads2 100000)
    let mut writing : Task (Except IO.Error Unit) := .pure (.ok ())
    repeat
      let chunk ← IO.ofExcept next.get
      if chunk.isEmpty then
        break
      next ← IO.asTask (Spec.readChunk reads1 reads2 100000)
      -- ╔══════════════════════════════════════════════════════════════════════════════════╗
      -- ║ THE PROVED PART. `alignPairs_correct` (Aligner.lean) covers this call: one result ║
      -- ║ per pair, in the same order, and every result's claims hold for the genome the    ║
      -- ║ index was built from. Everything around it only reads inputs and writes output.   ║
      -- ╚══════════════════════════════════════════════════════════════════════════════════╝
      let results := Spec.alignPairs insertSettings index (Spec.chunkPairs chunk)
      -- ══════════════════════════════════════════════════════════════════════════════════
      -- results come back in the same order as the pairs; `samChunk` lines each pair up with its result
      let text := Spec.samChunk chromosomes chunk results 16
      let previous := writing
      writing ← IO.asTask (do IO.ofExcept previous.get; out.write text)
    IO.ofExcept writing.get
    return 0
  | _ =>
    IO.eprintln "usage: shim build GENOME.fa INDEX\n       shim map INDEX READS_1.fq READS_2.fq OUT.sam MIN_FRAGMENT MAX_FRAGMENT"
    return 1
