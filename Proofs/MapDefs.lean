import Proofs.Trim
import Proofs.Sam
import Proofs.MapFast

/-! # Exact copies of the definitions of Proofs/MapFiles.lean (= Spec/MapFiles.lean with the holes filled), up to `process_correct`.
The proof modules (MapJobs ... MapCorrect) import these instead of Proofs.MapFiles, which imports the proof (it closes
`process_correct` with `MapCorrect.process_correct'`). `Testing/notes/byte_specs/check_copies.sh` diffs them against Proofs/MapFiles.lean. -/

namespace Spec.MapCopy
open Spec

-- the mates of every pair have the same QNAME (and it is a valid SAM QNAME);
-- then every read is cut at the adapter and trimmed
def prepPairs (reads1 reads2 : List FQ.Read) : Option (List (FQ.Read × FQ.Read)) :=
  let names1 := reads1.map (SamSpec.qname ∘ FQ.Read.name)
  let names2 := reads2.map (SamSpec.qname ∘ FQ.Read.name)
  match decide (names1 = names2 ∧ names1.all SamSpec.qnameOk) with
  | true  =>
    some (List.zip (reads1.map (Trim.trim ∘ Trim.cut)) (reads2.map (Trim.trim ∘ Trim.cut)))
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
  match mapReads settings index chrs fastq1 fastq2 with
  | some lines => some (SamSpec.header chrs ++ lines)
  | none       => none

-- the fast, streaming version: holes, filled below the Spec
def MapState : Type := MapFast.State
def mapInit (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) :
    MapState := MapFast.init (MapFast.job settings index chrs)
-- given the next chunk of each FASTQ file (none: both have ended): the next state, and SAM lines
def mapStep (state : MapState) (chunks : Option (ByteArray × ByteArray)) :
    Option (MapState × ByteArray) := MapFast.step state chunks

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

-- for the proof, the files are a list: the chunk pairs not read yet, and the output written so far
abbrev Files := List (ByteArray × ByteArray) × List UInt8

-- Main's `nextChunks`, on the list: take the next pair of chunks
def nextChunksList : StateM Files (Option (ByteArray × ByteArray)) :=
  modifyGet fun (rest, written) =>
    match rest with
    | []                => (none, ([], written))
    | chunks :: later   => (some chunks, (later, written))

-- Main's `out.write`, on the list: append the lines
def writeList (lines : ByteArray) : StateM Files Unit :=
  modify fun (rest, written) => (rest, written ++ bytes lines)


end Spec.MapCopy
