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

-- run it over the two files' blocks, in order
def mapFilesFast (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) : Option (List UInt8) :=
  let (state, header) := mapStart settings index chrs
  (go state blocks).map (header.data.toList ++ ·)
where
  go (state : MapState) : List (ByteArray × ByteArray) → Option (List UInt8)
    | [] => (mapEnd state).map (·.data.toList)
    | (block1, block2) :: rest =>
      match mapStep state block1 block2 with
      | some (next, piece) => (go next rest).map (piece.data.toList ++ ·)
      | none               => none

-- however the two files are cut into blocks, the fast version gives exactly `mapFiles`
theorem mapFilesFast_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) :
    mapFilesFast settings index chrs blocks =
      mapFiles settings index chrs (blocks.flatMap (·.1.data.toList)) (blocks.flatMap (·.2.data.toList)) := by
  sorry

end Spec.Total
