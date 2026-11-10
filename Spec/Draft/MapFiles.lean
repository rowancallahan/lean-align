import Spec.Draft.Trim
import Spec.Draft.Sam

namespace Spec.Total
open Spec

-- the SAM file for two FASTQ files, or none if either file is not valid FASTQ
def mapFiles (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (file1 file2 : List UInt8) : Option (List UInt8) :=
  match FQ.parse file1, FQ.parse file2 with
  | some reads1, some reads2 =>
    let pairs := List.zip (reads1.map (Trim.trim ∘ Trim.cut)) (reads2.map (Trim.trim ∘ Trim.cut))
    some (SamSpec.samFile chrs pairs (alignPairs settings index (pairs.map mateLetters)))
  | _, _ =>
    none
where
  -- what `alignPairs` takes for a pair: the letters of each mate, or none if trimmed away
  mateLetters (pair : FQ.Read × FQ.Read) : Option ByteArray × Option ByteArray :=
    let letters (r : FQ.Read) : Option ByteArray :=
      match r.sequence with
      | [] => none
      | s  => some ⟨s.toArray⟩
    (letters pair.1, letters pair.2)

-- streaming (holes, filled below the Spec): `stream_eq` says it gives exactly `mapFiles`

def MapState : Type := sorry
def mapStart (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) : MapState × ByteArray := sorry
def mapStep (st : MapState) (block1 block2 : ByteArray) : Option (MapState × ByteArray) := sorry
def mapEnd (st : MapState) : Option ByteArray := sorry

def runFrom : MapState → List (ByteArray × ByteArray) → Option (List UInt8)
  | st, [] => (mapEnd st).map (·.data.toList)
  | st, (b1, b2) :: rest =>
    match mapStep st b1 b2 with
    | some (st', piece) => (runFrom st' rest).map (piece.data.toList ++ ·)
    | none => none

def runStream (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) : Option (List UInt8) :=
  let (st, header) := mapStart settings index chrs
  (runFrom st blocks).map (header.data.toList ++ ·)

theorem stream_eq (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) :
    runStream settings index chrs blocks =
      mapFiles settings index chrs (blocks.flatMap (·.1.data.toList)) (blocks.flatMap (·.2.data.toList)) := by
  sorry

end Spec.Total
