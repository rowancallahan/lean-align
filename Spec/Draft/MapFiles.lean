import Spec.Draft.Trim
import Spec.Draft.Sam

namespace Spec.Total
open Spec

def pairUp (r1 r2 : List FQ.Read) : Option (List (FQ.Read × FQ.Read)) :=
  if r1.length = r2.length ∧ (r1.zip r2).all fun (a, b) =>
      SamSpec.qname a.name = SamSpec.qname b.name ∧ SamSpec.qnameOk (SamSpec.qname a.name)
  then some (r1.zip r2) else none

def toAligner (r : FQ.Read) : Option ByteArray := if r.sequence = [] then none else some ⟨r.sequence.toArray⟩

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

def runStream (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) :
    List (ByteArray × ByteArray) → Option (List UInt8)
  | blocks =>
    let (st, out) := mapStart settings index chrs
    let rec go (st : MapState) (out : List UInt8) : List (ByteArray × ByteArray) → Option (List UInt8)
      | [] => (mapEnd st).map fun last => out ++ last.data.toList
      | (b1, b2) :: rest => (mapStep st b1 b2).bind fun (st', piece) => go st' (out ++ piece.data.toList) rest
    go st out.data.toList blocks

theorem stream_eq (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) :
    runStream settings index chrs blocks =
      mapFiles settings index chrs (blocks.flatMap (·.1.data.toList)) (blocks.flatMap (·.2.data.toList)) := by
  sorry

end Spec.Total
