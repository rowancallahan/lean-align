import Spec.Aligner

/-! # The genome FASTA and the saved chromosome list. Unproved (trusted) plumbing for the shim;
the FASTA parser gets a proof later. -/

namespace Spec

-- FASTA: a line starting with '>' names a chromosome; the lines after it are its letters
def parseFasta (text : String) : GenomeFile :=
  (text.splitOn "\n").foldl (init := #[]) fun chromosomes line =>
    if line.startsWith ">" then
      chromosomes.push ((line.drop 1).toString, ByteArray.empty)
    else if chromosomes.isEmpty then
      chromosomes
    else
      chromosomes.modify (chromosomes.size - 1) fun (name, sequence) =>
        (name, sequence ++ line.trimAscii.toString.toUTF8)

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
