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

-- the SAM lines for two FASTQ files (no header), or none if they are not valid, matching FASTQ
def mapReads (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (fastq1 fastq2 : List UInt8) : Option (List UInt8) :=
  match FQ.parse fastq1, FQ.parse fastq2 with
  | some reads1, some reads2 =>
    (prepPairs reads1 reads2).map fun pairs =>
      SamSpec.body chrs pairs (alignPairs settings index (pairs.map mateLetters))
  | _, _ =>
    none

-- the SAM file: the header, then the lines
def mapFiles (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (fastq1 fastq2 : List UInt8) : Option (List UInt8) :=
  (mapReads settings index chrs fastq1 fastq2).map (SamSpec.header chrs ++ ·)

-- the fast, streaming version: holes, filled below the Spec
def MapState : Type := sorry
def mapInit (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) : MapState := sorry
-- given the next chunk of each FASTQ file (none: both files have ended), the next state and SAM lines
def mapStep (state : MapState) (chunks : Option (ByteArray × ByteArray)) : Option (MapState × ByteArray) := sorry

-- one loop for the proof and for Main: `next` gives the next chunks, `emit` writes SAM lines
def process [Monad m] (next : m (Option (ByteArray × ByteArray))) (emit : ByteArray → m Unit) :
    (fuel : Nat) → MapState → m (Option Unit)
  | 0, _ => pure none
  | fuel + 1, state => do
    let chunks ← next
    match mapStep state chunks, chunks with
    | none, _ =>
      pure none
    | some (state', lines), none =>
      emit lines
      pure (some ())
    | some (state', lines), some _ =>
      emit lines
      process next emit fuel state'

def bytes (b : ByteArray) : List UInt8 := b.data.toList

-- `process` on the two FASTQ files given as a list of chunk pairs: `next` takes the next pair,
-- `emit` appends to the output; what it writes is exactly `mapReads`
theorem process_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (chunks : List (ByteArray × ByteArray)) (fuel : Nat) (enough : chunks.length < fuel) :
    let fastq1 := chunks.flatMap fun (chunk1, _) => bytes chunk1
    let fastq2 := chunks.flatMap fun (_, chunk2) => bytes chunk2
    -- the state: the chunks not read yet, and the output written so far
    let next : StateM (List (ByteArray × ByteArray) × List UInt8) (Option (ByteArray × ByteArray)) :=
      modifyGet fun (rest, out) =>
        match rest with
        | []         => (none, ([], out))
        | c :: later => (some c, (later, out))
    let emit (lines : ByteArray) : StateM (List (ByteArray × ByteArray) × List UInt8) Unit :=
      modify fun (rest, out) => (rest, out ++ bytes lines)
    let (result, (_, written)) := (process next emit fuel (mapInit settings index chrs)).run (chunks, [])
    result.map (fun () => written) = mapReads settings index chrs fastq1 fastq2 := by
  sorry

end Spec.Total
