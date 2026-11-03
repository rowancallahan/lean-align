import Proofs.Fastq
/-! DRAFT for Rowan (not built by lake, not part of Spec/). A whole-file FASTQ spec over bytes:
what the records of a file ARE, independent of how they are read. Every reader (block reader,
parallel slice parser) is then proved to return exactly `parseFastq bytes`. -/
namespace Spec.Draft

-- the file's lines: split at '\n', drop a '\r' before it, no empty last line after a final '\n'
def lines (bytes : ByteArray) : List ByteArray :=
  let ls := (bytes.toList.splitOn 10).map fun l =>
    ByteArray.mk (if l.getLast? = some 13 then l.dropLast else l).toArray
  if ls.getLast?.map (·.size) = some 0 then ls.dropLast else ls

-- four lines per record, each record checked by the existing `parseRecord`
def parseLines : List ByteArray → Except String (List FastqRecord)
  | [] => .ok []
  | header :: letters :: plus :: quality :: rest => do
      let record ← parseRecord header letters plus quality
      let records ← parseLines rest
      pure (record :: records)
  | _ => .error "file ends inside a record"

def parseFastq (bytes : ByteArray) : Except String (List FastqRecord) := parseLines (lines bytes)

-- THE lemma for parallel parsing: cut after a record (a whole number of lines, ending in '\n'),
-- parse both parts (on different tasks), join = parse the whole
theorem parseFastq_append (a b : ByteArray) (hEnd : a.size = 0 ∨ a[a.size - 1]! = 10)
    (hRec : (lines a).length % 4 = 0) :
    parseFastq (a ++ b) = (parseFastq a).bind fun ra => (parseFastq b).map (ra ++ ·) := by
  sorry

-- pairing: the two files have the same number of records and mate names agree, record by record
def pairUp (r1 r2 : List FastqRecord) : Except String (List (FastqRecord × FastqRecord)) :=
  if r1.length != r2.length then .error "FASTQ files out of step: different numbers of reads"
  else (r1.zip r2).mapM fun (x, y) =>
    if mateName x.name == mateName y.name then .ok (x, y) else .error s!"mate names {x.name} / {y.name}"

-- what the shim's reading must produce (trusted today, provable later): the pairs of the two files, in order
def pairsOfFiles (f1 f2 : ByteArray) : Except String (List (FastqRecord × FastqRecord)) := do
  pairUp (← parseFastq f1) (← parseFastq f2)

end Spec.Draft
