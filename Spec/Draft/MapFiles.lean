-- DRAFT (Rowan to re-lock): the end-to-end spec and its streaming form.
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
def mapInit (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) : MapState := sorry
-- given the next pair of blocks (none: both files have ended), the next state and the bytes to write
def mapStep (state : MapState) (blocks : Option (ByteArray × ByteArray)) : Option (MapState × ByteArray) := sorry

-- one loop for the proof and for Main: `next` gives the next pair of blocks, `emit` writes a piece
def process [Monad m] (next : m (Option (ByteArray × ByteArray))) (emit : ByteArray → m Unit) :
    (fuel : Nat) → MapState → m (Option Unit)
  | 0, _ => pure none
  | fuel + 1, state => do
    let blocks ← next
    match mapStep state blocks, blocks with
    | none, _ =>
      pure none
    | some (state', piece), none =>
      emit piece
      pure (some ())
    | some (state', piece), some _ =>
      emit piece
      process next emit fuel state'

-- run on a list of blocks (next takes the first, emit appends), `process` writes exactly `mapFiles`
theorem process_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (blocks : List (ByteArray × ByteArray)) (fuel : Nat) (enough : blocks.length < fuel) :
    let file1 := blocks.flatMap fun (block1, _) => block1.data.toList
    let file2 := blocks.flatMap fun (_, block2) => block2.data.toList
    let next : StateM (List (ByteArray × ByteArray) × List UInt8) (Option (ByteArray × ByteArray)) :=
      modifyGet fun (rest, out) =>
        match rest with
        | []         => (none, ([], out))
        | b :: later => (some b, (later, out))
    let emit (piece : ByteArray) : StateM (List (ByteArray × ByteArray) × List UInt8) Unit :=
      modify fun (rest, out) => (rest, out ++ piece.data.toList)
    let (result, (_, written)) := (process next emit fuel (mapInit settings index chrs)).run (blocks, [])
    result.map (fun () => written) = mapFiles settings index chrs file1 file2 := by
  sorry

end Spec.Total
