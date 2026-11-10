-- LOCKED (Rowan, 2026-11-10): the end-to-end spec and its streaming form.
import Spec.Draft.Trim
import Spec.Draft.Sam

namespace Spec.Total
open Spec

-- the mates of every pair have the same QNAME (and it is a valid SAM QNAME);
-- then every read is cut at the adapter and trimmed
def prepPairs (reads1 reads2 : List FQ.Read) : Option (List (FQ.Read × FQ.Read)) :=
  let names1 := reads1.map (SamSpec.qname ∘ FQ.Read.name)
  let names2 := reads2.map (SamSpec.qname ∘ FQ.Read.name)
  match decide (names1 = names2 ∧ names1.all SamSpec.qnameOk) with
  | true  => some (List.zip (reads1.map (Trim.trim ∘ Trim.cut)) (reads2.map (Trim.trim ∘ Trim.cut)))
  | false => none

-- what `alignPairs` takes for a pair: the letters of each mate, or none if trimmed away
def mateLetters (pair : FQ.Read × FQ.Read) : Option ByteArray × Option ByteArray :=
  let letters (r : FQ.Read) : Option ByteArray :=
    match r.sequence with
    | [] => none
    | s  => some ⟨s.toArray⟩
  (letters pair.1, letters pair.2)

-- the SAM file for two FASTQ files, or none if they are not valid, matching FASTQ
def mapFiles (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (file1 file2 : List UInt8) : Option (List UInt8) :=
  match FQ.parse file1, FQ.parse file2 with
  | some reads1, some reads2 =>
    (prepPairs reads1 reads2).map fun pairs =>
      SamSpec.samFile chrs pairs (alignPairs settings index (pairs.map mateLetters))
  | _, _ =>
    none

-- the fast, streaming version: holes, filled below the Spec
def MapState : Type := sorry
def mapStart (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) : MapState × ByteArray := sorry
def mapStep (state : MapState) (block1 block2 : ByteArray) : Option (MapState × ByteArray) := sorry
def mapEnd (state : MapState) : Option ByteArray := sorry

-- however the two files are cut into blocks: start, one step per pair of blocks (in order),
-- then end; the pieces written, joined, are exactly `mapFiles` of the whole files
theorem mapFilesFast_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) :
    let file1 := blocks.flatMap fun (block1, _) => block1.data.toList
    let file2 := blocks.flatMap fun (_, block2) => block2.data.toList
    let (start, header) := mapStart settings index chrs
    let step (sofar : MapState × List UInt8) (blockPair : ByteArray × ByteArray) :=
      (mapStep sofar.1 blockPair.1 blockPair.2).map fun (next, piece) => (next, sofar.2 ++ piece.data.toList)
    let finish (sofar : MapState × List UInt8) :=
      (mapEnd sofar.1).map fun last => sofar.2 ++ last.data.toList
    (blocks.foldlM step (start, header.data.toList)).bind finish
      = mapFiles settings index chrs file1 file2 := by
  sorry

end Spec.Total
