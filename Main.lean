-- The lean-align executable: Spec/Shim.lean line for line, importing Proofs (the proved buildIndex / alignPairs) instead of Spec.
import Proofs.Sam
import Std.Sync.Channel

/-! # The execution shim. `build` reads the FASTA and saves the index; `map` reads only the index, then maps the
read pairs in jobs and writes SAM. Everything here except the boxed `alignPairs` call is unproved plumbing.

`map` is a pipeline that keeps every core busy:
* two readers (one per mate file) cut their input into slices of `jobPairs` records: every `4 · jobPairs`-th
  newline, with no parsing (a valid FASTQ record is exactly four lines, `FQ.toBytes`);
* a dispatcher pairs slice k of each file into job k;
* `workers` workers each parse their job's two slices with `parseFastqB` (= `FQ.parse`, `parseFastqB_eq`), pair the
  mates (same number of reads, same QNAME), trim them (`trimChunk` = `trimReadB` on every mate = `trimRead`), align
  them (`alignPairs`, proved) and format the SAM bytes (`samChunk`);
* the writer (the main thread) writes the jobs in order; the first job (in order) that failed stops the run with its
  error, after every job before it is written.

TRUSTED (not proved): that cutting at every `4 · jobPairs`-th newline and parsing the slices gives the reads of the
whole file in order (each record of a valid file has exactly four newlines), the channels and tasks, and the writes. -/

namespace Pipe
open Spec

-- the pairs per job, the workers, and the jobs queued per worker
def jobPairs : Nat := 16000
def workers : Nat := 4
def depth : Nat := 2
def blockSize : Nat := 8 * 1024 * 1024

-- up to 8 MB; short (pipe) reads are topped up, 1 MB at a time, until the block is full or the input ends
def readBig (h : IO.FS.Handle) : IO ByteArray := do
  let mut block ← h.read blockSize.toUSize
  if block.isEmpty then return block
  repeat
    if blockSize ≤ block.size then break
    let more ← h.read (min (1024 * 1024) (blockSize - block.size)).toUSize
    if more.isEmpty then break
    block := block ++ more
  return block

-- one past the `n`-th newline at or after `i`, and how many newlines were found (fewer than `n`: up to the end)
def cutAfter (b : ByteArray) (i n : Nat) : Nat × Nat := Id.run do
  let mut p := i
  let mut f := 0
  for _ in [0:n] do
    let j := findNewline b p
    if j < b.size then
      p := j + 1
      f := f + 1
    else
      p := b.size
      break
  return (p, f)

def die (what : String) (e : IO.Error) : IO Unit := do
  IO.eprintln s!"lean-align: {what}: {e}"
  IO.Process.exit 1

-- slices of exactly `k` records (the last one may be shorter, or end without a newline), in file order
def reader (h : IO.FS.Handle) (k : Nat) (ch : Std.CloseableChannel.Sync ByteArray) : IO Unit := do
  let need := 4 * k
  let mut carry := ByteArray.empty
  let mut scan := 0
  let mut lines := 0
  let mut eof := false
  repeat
    let (p, f) := cutAfter carry scan (need - lines)
    if lines + f = need then
      ch.send (carry.extract 0 p)
      carry := carry.extract p carry.size
      scan := 0
      lines := 0
    else
      scan := carry.size
      lines := lines + f
      if eof then
        if 0 < carry.size then ch.send carry
        break
      let blk ← readBig h
      if blk.isEmpty then eof := true else carry := carry ++ blk
  ch.close

-- a read name for messages (the parser checked it is ASCII)
def nameText (name : ByteArray) : String := (String.fromUTF8? name).getD "?"

-- the two mate files' reads of a job as pairs: the same number of reads, each pair with the same QNAME (`qnameB`,
-- = `qnameOf`), and every QNAME a valid SAM QNAME (`qnameOkB`)
def pairUp (r1 r2 : Array ReadB) : Except String (Array (ReadB × ReadB)) := do
  let mut chunk := #[]
  for (read1, read2) in r1.zip r2 do
    let q1 := qnameB read1.name
    let q2 := qnameB read2.name
    if q1 != q2 then
      throw s!"FASTQ files out of step: mate names {nameText read1.name} / {nameText read2.name}"
    for (read, q) in [(read1, q1), (read2, q2)] do
      unless qnameOkB q do
        throw s!"FASTQ: read name '{nameText read.name}' is not a SAM QNAME"
    chunk := chunk.push (read1, read2)
  if r1.size != r2.size then
    throw "FASTQ files out of step: one file has more reads than the other"
  return chunk

def worker (insertSettings : InsertSettings) (index : ByteArray) (chromosomes : ChromosomeList)
    (jobs : Std.CloseableChannel.Sync (Nat × ByteArray × ByteArray))
    (out : Std.CloseableChannel.Sync (Nat × Except String ByteArray)) : IO Unit := do
  repeat
    let some (seq, slice1, slice2) ← jobs.recv | break
    match (do pairUp (← parseFastqB slice1) (← parseFastqB slice2)) with
    | .error why => out.send (seq, .error why)
    | .ok raw =>
      let chunk := trimChunk raw 1
      -- ╔══════════════════════════════════════════════════════════════════════════════════╗
      -- ║ THE PROVED PART. `alignPairs_correct` (Aligner.lean) covers this call: one result ║
      -- ║ per pair, in the same order, and every result's claims hold for the genome the    ║
      -- ║ index was built from. Everything around it only reads inputs and writes output.   ║
      -- ║                                                                                  ║
      -- ║ IN:  `chunk`, the pairs of this job, parsed by the proved parser (`parseFastqB`   ║
      -- ║      = `FQ.parse`) and trimmed by the proved trimmer (`trimChunk_eq`).            ║
      -- ║ OUT: `results`, one `PairResult` per pair, in the same order as `chunk`.          ║
      -- ║ TRUSTED around it (not proved yet): that the slices are the file's records in     ║
      -- ║ order, that the jobs are written in order, and that `samChunk` and the writes put ║
      -- ║ each pair's lines into the file correctly.                                        ║
      -- ╚══════════════════════════════════════════════════════════════════════════════════╝
      let results := alignPairs insertSettings index (chunkPairs chunk)
      -- ═══════════════════════════════ END OF THE PROVED PART ═══════════════════════════
      out.send (seq, .ok (samChunk chromosomes chunk results))

def run (insertSettings : InsertSettings) (index : ByteArray) (chromosomes : ChromosomeList) (h1 h2 : IO.FS.Handle)
    (outH : IO.FS.Handle) : IO Unit := do
  let ch1 ← Std.CloseableChannel.Sync.new (some 3)
  let ch2 ← Std.CloseableChannel.Sync.new (some 3)
  let jobs ← Std.CloseableChannel.Sync.new (some (depth * workers))
  let res ← Std.CloseableChannel.Sync.new (some (4 * workers))
  let _ ← IO.asTask (prio := .dedicated) (try reader h1 jobPairs ch1 catch e => die "reading the first FASTQ file" e)
  let _ ← IO.asTask (prio := .dedicated) (try reader h2 jobPairs ch2 catch e => die "reading the second FASTQ file" e)
  let dispatcher ← IO.asTask (prio := .dedicated) (do
      let mut seq := 0
      repeat
        let a ← ch1.recv
        let b ← ch2.recv
        match a, b with
        | some x, some y =>
          jobs.send (seq, x, y)
          seq := seq + 1
        | none, none => break
        | _, _ =>
          res.send (seq, .error "FASTQ files out of step: one file has more reads than the other")
          break
      jobs.close)
  let ws ← (List.range workers).mapM fun _ =>
    IO.asTask (prio := .dedicated) (try worker insertSettings index chromosomes jobs res catch e => die "worker" e)
  let _ ← IO.asTask (prio := .dedicated) (do
    let _ ← IO.wait dispatcher
    for w in ws do let _ ← IO.wait w
    res.close)
  let mut pending : Std.HashMap Nat (Except String ByteArray) := {}
  let mut nextSeq := 0
  repeat
    let some (s, text) ← res.recv | break
    pending := pending.insert s text
    repeat
      match (pending[nextSeq]? : Option (Except String ByteArray)) with
      | some (.ok t) =>
        outH.write t
        pending := pending.erase nextSeq
        nextSeq := nextSeq + 1
      | some (.error why) =>
        outH.flush
        die "map" (IO.userError why)
      | none => break
  unless pending.isEmpty do die "map" (IO.userError "pipeline: results missing")

end Pipe

def main (args : List String) : IO UInt32 := do
  match args with
  | ["build", genomePath, indexPath] =>
    let byteGenome ← Spec.readFasta (← IO.FS.Handle.mk genomePath .read)
    IO.FS.writeBinFile indexPath (Spec.buildIndex byteGenome)
    IO.FS.writeFile (indexPath ++ ".chromosomes") (Spec.chromosomeListText byteGenome)
    return 0
  | ["map", indexPath, reads1Path, reads2Path, outPath, minFragment, maxFragment] =>
    let insertSettings : Spec.InsertSettings := { range := (minFragment.toNat!, maxFragment.toNat!) }
    -- TRUSTED: the index file is `buildIndex byteGenome` for the genome (the theorem's `hIndex`),
    -- and INDEX.chromosomes lists that genome's names and lengths
    let index ← IO.FS.readBinFile indexPath
    let chromosomes ← Spec.readChromosomeList (indexPath ++ ".chromosomes")
    let out ← IO.FS.Handle.mk outPath .write
    for line in Spec.samHeader chromosomes do
      out.putStrLn line
    Pipe.run insertSettings index chromosomes (← IO.FS.Handle.mk reads1Path .read) (← IO.FS.Handle.mk reads2Path .read) out
    return 0
  | _ =>
    IO.eprintln "usage: shim build GENOME.fa INDEX\n       shim map INDEX READS_1.fq READS_2.fq OUT.sam MIN_FRAGMENT MAX_FRAGMENT"
    return 1
