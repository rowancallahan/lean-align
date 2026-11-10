import Spec.Draft.Trim
import Spec.Draft.Sam

namespace Spec.Total
open Spec

def pairUp : List FQ.Read → List FQ.Read → Option (List (FQ.Read × FQ.Read))
  | [], [] => some []
  | a :: as, b :: bs =>
    let q := SamSpec.qname a.name
    match q == SamSpec.qname b.name && SamSpec.qnameOk q with
    | true  => (pairUp as bs).map ((a, b) :: ·)
    | false => none
  | _, _ => none

def toAligner (r : FQ.Read) : Option ByteArray :=
  match r.sequence with
  | [] => none
  | s  => some ⟨s.toArray⟩

def mapFiles (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (file1 file2 : List UInt8) : Option (List UInt8) := do
  let pairs ← pairUp (← FQ.parse file1) (← FQ.parse file2)
  let trimmed := pairs.map fun (a, b) => (Trim.trim a, Trim.trim b)
  let results := alignPairs settings index (trimmed.map fun (a, b) => (toAligner a, toAligner b))
  pure (SamSpec.samFile chrs trimmed results)

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
