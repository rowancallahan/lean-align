import Spec.Aligner

/-! # The genome FASTA and the saved chromosome list. Unproved (trusted) plumbing for the shim;
the FASTA parser gets a proof later. -/

namespace Spec

-- FASTA: a line starting with '>' names a chromosome; the lines after it are its letters.
-- Read as bytes, one line at a time (no Strings except the names), so memory stays near the genome's size.
def parseFasta (bytes : ByteArray) : GenomeFile := Id.run do
  let mut chromosomes : GenomeFile := #[]
  let mut i := 0
  while i < bytes.size do
    let mut j := i
    while j < bytes.size && bytes[j]! != 10 do
      j := j + 1
    -- the line is [i, stop): no "\n", no trailing "\r", spaces or tabs
    let mut stop := j
    while i < stop && (bytes[stop - 1]! == 13 || bytes[stop - 1]! == 32 || bytes[stop - 1]! == 9) do
      stop := stop - 1
    if i < stop && bytes[i]! == 62 then
      chromosomes := chromosomes.push (String.fromUTF8! (bytes.extract (i + 1) stop), ByteArray.empty)
    else if !chromosomes.isEmpty then
      chromosomes := chromosomes.modify (chromosomes.size - 1) fun (name, sequence) =>
        (name, sequence ++ bytes.extract i stop)
    i := j + 1
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
