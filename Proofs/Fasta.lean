import Proofs.Aligner
import Proofs.Fastq

/-! # The genome FASTA and the saved chromosome list. Unproved (trusted) plumbing for the shim;
the FASTA parser gets a proof later. -/

namespace Spec

-- a line without its trailing spaces and tabs (FastqReader.line already drops "\n" and "\r")
def trimLineEnd (line : ByteArray) : ByteArray := Id.run do
  let mut stop := line.size
  while 0 < stop && (line[stop - 1]! == 32 || line[stop - 1]! == 9) do
    stop := stop - 1
  return if stop == line.size then line else line.extract 0 stop

-- FASTA: a line starting with '>' names a chromosome; the lines after it are its letters.
-- Streamed from the file a block at a time, so memory stays near the genome's own size.
def readFasta (handle : IO.FS.Handle) : IO GenomeFile := do
  let reader ← FastqReader.ofHandle handle
  let mut chromosomes : GenomeFile := #[]
  let mut name := ""
  let mut sequence := ByteArray.empty
  let mut started := false
  repeat
    let some line ← reader.line | break
    let line := trimLineEnd line
    if 0 < line.size && line[0]! == 62 then
      if started then
        chromosomes := chromosomes.push (name, sequence)
      name := String.fromUTF8! (line.extract 1 line.size)
      sequence := ByteArray.empty
      started := true
    else if started then
      sequence := sequence ++ line
  if started then
    chromosomes := chromosomes.push (name, sequence)
  return chromosomes

-- chromosome names and lengths, in genome order (saved next to the index at build time)
abbrev ChromosomeList := Array (String × Nat)

-- one "name<TAB>length" line per chromosome
def chromosomeListText (byteGenome : GenomeFile) : String :=
  String.join (byteGenome.toList.map fun (name, sequence) => s!"{name}\t{sequence.size}\n")

def readChromosomeList (path : String) : IO ChromosomeList := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  return lines.toArray.map fun line =>
    match line.splitOn "\t" with
    | [name, length] => (name, length.toNat!)
    | _ => (line, 0)

end Spec
