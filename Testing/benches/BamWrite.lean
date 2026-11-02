import Proofs.Sam

/-! # BAM writer prototype (benchmark only, unproved IO; NOT part of Spec/).

Pure Lean, no extern/unsafe/zlib: BAM records (4-bit sequence, raw qualities, binary fields) inside BGZF blocks
whose deflate payload is a STORED block, the gzip CRC32 computed here (table driven), and the BGZF EOF block.
`bamPair` mirrors `Spec.samLines` field for field (same `PairResult`).

    lake exe bam_write INDEX.idx READS_1.fq READS_2.fq OUT_PREFIX [REPS] [real|synthetic] [LIMIT]

Maps the pairs once with the proved `alignPairs` (100000-pair chunks, as the shim), keeps the results, then times only
the OUTPUT stage on those fixed results, REPS times each: SAM text (`Spec.samChunk` + write) and BAM stored
(`bamChunk` + BGZF framing + write). Writes OUT_PREFIX.sam and OUT_PREFIX.bam from the last repetition.
`m1`: results of the same shape as today's, made without `alignPairs` (fast to run). `synthetic`: every pair gets an invented found pair (150M-style CIGAR, fake coordinates) so the writers' mapped path
is exercised and sized as it will be at M2; the real results (M1) have every pair unmapped. -/

open Spec

-- a chunk of read pairs, as `alignPairs` takes them (as Main.lean)
def chunkPairs (chunk : Array (FastqRecord × FastqRecord)) : List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (record1, record2) => (some record1.letters, some record2.letters)

namespace Bam

/-! ## CRC32 (IEEE, as gzip) -/

def crcEntry (n : Nat) : UInt32 := Id.run do
  let mut c : UInt32 := n.toUInt32
  for _ in [0:8] do
    c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
  return c

-- slice-by-8 tables: table k, entry i at 256 * k + i  (k = 0 is the plain byte table)
def crcTables : Array UInt32 := Id.run do
  let mut t : Array UInt32 := (Array.range 256).map crcEntry
  for k in [1:8] do
    for i in [0:256] do
      let prev := t[256 * (k - 1) + i]!
      t := t.push (t[(prev &&& 0xFF).toNat]! ^^^ (prev >>> 8))
  return t

-- CRC32 of `data[lo, hi)`, 8 bytes per step
def crc32 (data : ByteArray) (lo hi : Nat) : UInt32 := Id.run do
  assert! hi ≤ data.size
  let mut c : UInt32 := 0xFFFFFFFF
  let mut i := lo
  while i + 8 ≤ hi do
    let x := c ^^^ (data[i]!.toUInt32 ||| (data[i + 1]!.toUInt32 <<< 8) ||| (data[i + 2]!.toUInt32 <<< 16) ||| (data[i + 3]!.toUInt32 <<< 24))
    c := crcTables[1792 + (x &&& 0xFF).toNat]! ^^^ crcTables[1536 + ((x >>> 8) &&& 0xFF).toNat]! ^^^
         crcTables[1280 + ((x >>> 16) &&& 0xFF).toNat]! ^^^ crcTables[1024 + (x >>> 24).toNat]! ^^^
         crcTables[768 + data[i + 4]!.toNat]! ^^^ crcTables[512 + data[i + 5]!.toNat]! ^^^
         crcTables[256 + data[i + 6]!.toNat]! ^^^ crcTables[data[i + 7]!.toNat]!
    i := i + 8
  while i < hi do
    c := crcTables[((c ^^^ data[i]!.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
    i := i + 1
  return c ^^^ 0xFFFFFFFF

/-! ## little-endian fields -/

def put8 (b : ByteArray) (v : Nat) : ByteArray := b.push v.toUInt8
def put16 (b : ByteArray) (v : Nat) : ByteArray := (b.push v.toUInt8).push (v >>> 8).toUInt8
def put32 (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8
-- two's complement of an Int (must fit 32 bits)
def putI32 (b : ByteArray) (v : Int) : ByteArray :=
  assert! -2147483648 ≤ v ∧ v < 4294967296
  put32 b (v % 4294967296).toNat.toUInt32

/-! ## BGZF with stored deflate blocks -/

def blockPayload : Nat := 65280   -- as htslib: 0xff00 bytes per block (stored: 18 + 5 + n + 8 ≤ 65536)

-- one BGZF block holding `data[lo, hi)` as a stored deflate block
def bgzfBlock (data : ByteArray) (lo hi : Nat) : ByteArray :=
  let n := hi - lo
  assert! n ≤ 65505
  let b := ByteArray.emptyWithCapacity (n + 31)
  -- gzip header: ID1 ID2 CM FLG(FEXTRA) MTIME XFL OS XLEN, then the BC subfield with BSIZE = total - 1
  let b := b.append ⟨#[0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0]⟩
  let b := put16 b (n + 30)
  -- stored deflate block: BFINAL=1 BTYPE=00, LEN, NLEN
  let b := put16 (put16 (b.push 1) n) (65535 - n)
  let b := data.copySlice lo b b.size n
  put32 (put32 b (crc32 data lo hi)) n.toUInt32

def eofBlock : ByteArray :=
  ⟨#[0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0, 0x1b, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- the data cut into blocks; one task per block (CRC + copy)
def bgzf (data : ByteArray) : ByteArray :=
  let count := (data.size + blockPayload - 1) / blockPayload
  let tasks := (List.range count).map fun k => Task.spawn fun _ =>
    bgzfBlock data (k * blockPayload) (min data.size ((k + 1) * blockPayload))
  tasks.foldl (fun out t => out ++ t.get) ByteArray.empty

/-! ## BAM -/

def bamHeader (chromosomes : ChromosomeList) : ByteArray :=
  let text := String.join ((samHeader chromosomes).map (· ++ "\n"))
  let b := (ByteArray.empty.append ⟨#[66, 65, 77, 1]⟩)
  let b := putI32 b text.utf8ByteSize
  let b := b.append text.toUTF8
  let b := putI32 b chromosomes.size
  chromosomes.foldl (init := b) fun b (name, length) =>
    let b := putI32 b (name.utf8ByteSize + 1)
    let b := (b.append name.toUTF8).push 0
    putI32 b length

-- 4-bit code of a base: index in "=ACMGRSVTWYHKDBN"
def seqCodes : Array UInt8 := Id.run do
  let mut t := Array.replicate 256 (255 : UInt8)
  for (c, i) in "=ACMGRSVTWYHKDBN".toList.zip (List.range 16) do
    t := t.set! c.toNat i.toUInt8
  return t

-- SAM's reg2bin (SAM spec 5.3) on [beg, end)
def reg2bin (beg «end» : Nat) : Nat :=
  let e := «end» - 1
  if beg >>> 14 == e >>> 14 then 4681 + (beg >>> 14)
  else if beg >>> 17 == e >>> 17 then 585 + (beg >>> 17)
  else if beg >>> 20 == e >>> 20 then 73 + (beg >>> 20)
  else if beg >>> 23 == e >>> 23 then 9 + (beg >>> 23)
  else if beg >>> 26 == e >>> 26 then 1 + (beg >>> 26)
  else 0

-- code of the complement of a base, 255 if not a base letter
def seqCodesRc : Array UInt8 := (Array.range 256).map fun b => seqCodes[(complementByte b.toUInt8).toNat]!

-- SEQ as on the forward strand: reversed and complemented on the reverse strand (`samSequence`), 4 bits per base
def putSeq (out : ByteArray) (letters : ByteArray) (rev : Bool) : ByteArray := Id.run do
  let n := letters.size
  let tab := if rev then seqCodesRc else seqCodes
  let base (i : Nat) : UInt8 := tab[(letters[if rev then n - 1 - i else i]!).toNat]!
  let mut out := out
  let mut bad : UInt8 := 0
  for k in [0:n / 2] do
    let hi := base (2 * k)
    let lo := base (2 * k + 1)
    bad := bad ||| hi ||| lo
    out := out.push ((hi <<< 4) ||| lo)
  if n % 2 == 1 then
    let hi := base (n - 1)
    bad := bad ||| hi
    out := out.push (hi <<< 4)
  assert! bad < 16   -- every letter was one of "=ACMGRSVTWYHKDBN" (invalid codes are 255)
  return out

-- QUAL: Phred = byte - 33, reversed with the sequence
def putQual (out : ByteArray) (quality : ByteArray) (rev : Bool) : ByteArray := Id.run do
  let n := quality.size
  let mut out := out
  let mut low : UInt8 := 255
  for i in [0:n] do
    let q := quality[if rev then n - 1 - i else i]!
    low := min low q
    out := out.push (q - 33)
  assert! n == 0 || 33 ≤ low
  return out

-- an integer tag in the smallest BAM type that holds it
def putIntTag (out : ByteArray) (tag : String) (v : Int) : ByteArray :=
  let out := out.append tag.toUTF8
  if 0 ≤ v then
    if v < 256 then (out.push 'C'.toNat.toUInt8).push v.toNat.toUInt8
    else if v < 65536 then put16 (out.push 'S'.toNat.toUInt8) v.toNat
    else put32 (out.push 'I'.toNat.toUInt8) v.toNat.toUInt32
  else
    if -128 ≤ v then (out.push 'c'.toNat.toUInt8).push (v % 256).toNat.toUInt8
    else if -32768 ≤ v then put16 (out.push 's'.toNat.toUInt8) (v % 65536).toNat
    else putI32 (out.push 'i'.toNat.toUInt8) v

def putStrTag (out : ByteArray) (tag value : String) : ByteArray :=
  ((out.append tag.toUTF8).push 'Z'.toNat.toUInt8 |>.append value.toUTF8).push 0

-- the custom tags of `answerTags`
def putAnswerTags (out : ByteArray) (answer : PairAnswer) : ByteArray :=
  let out := putIntTag out "XB" answer.bestPossibleScore
  let out := putStrTag out "XU" (uniquenessText answer.uniqueness)
  putStrTag out "XT" (tierText answer.tier)

def cigarOp : Step → Nat
  | .diag => 0   -- M
  | .gapY => 1   -- I
  | .gapX => 2   -- D

-- one BAM record, appended to `out`: block_size is filled in at the end
def putRecord (out : ByteArray) (qname : String) (flag : Nat) (refId pos : Int) (mapq bin : Nat)
    (cigar : Array (Step × Nat)) (record : FastqRecord) (rev : Bool) (nextRef nextPos tlen : Int)
    (tags : ByteArray → ByteArray) : ByteArray :=
  let start := out.size
  let out := putI32 out 0
  let out := putI32 out refId
  let out := putI32 out pos
  let out := put16 (put8 (put8 out (qname.utf8ByteSize + 1)) mapq) bin
  let out := put16 (put16 out cigar.size) flag
  let out := putI32 out record.letters.size
  let out := putI32 (putI32 (putI32 out nextRef) nextPos) tlen
  let out := (out.append qname.toUTF8).push 0
  let out := cigar.foldl (init := out) fun out (step, count) => put32 out ((count <<< 4 ||| cigarOp step).toUInt32)
  let out := putSeq out record.letters rev
  let out := putQual out record.quality.toUTF8 rev
  let out := tags out
  let size := out.size - start - 4
  let b := (size.toUInt32 : UInt32)
  (((out.set! start b.toUInt8).set! (start + 1) (b >>> 8).toUInt8).set! (start + 2) (b >>> 16).toUInt8).set!
    (start + 3) (b >>> 24).toUInt8

-- a mate of a found pair (`mappedLine`)
def bamMapped (out : ByteArray) (record : FastqRecord) (which : Mate) (mate other : MateReport)
    (answer : PairAnswer) : ByteArray :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let left := min mate.placement.start other.placement.start
  let right := max mate.placement.stop other.placement.stop
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then right - left else -((right - left : Nat) : Int)
  let refLength := mate.cigar.foldl (init := 0) fun n (step, count) => if step == .gapY then n else n + count
  putRecord out (samName record.name) flag mate.placement.chromosome mate.placement.start (mapq answer)
    (reg2bin mate.placement.start (mate.placement.start + refLength)) mate.cigar record
    (mate.placement.strand == .reverse) other.placement.chromosome other.placement.start tlen
    fun out => putAnswerTags (putIntTag out "AS" mate.score) answer

-- a mate with no alignment reported
def bamUnmapped (out : ByteArray) (record : FastqRecord) (which : Mate) (tags : ByteArray → ByteArray) : ByteArray :=
  putRecord out (samName record.name) (flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which) (-1) (-1) 0 4680
    #[] record false (-1) (-1) 0 tags

-- the two BAM records for one pair (`samLines`)
def bamPair (out : ByteArray) (record1 record2 : FastqRecord) (result : PairResult) : ByteArray :=
  match result with
  | .trimmedAway mate =>
      let tags := fun out => putStrTag out "XT" s!"trimmedAway{if mate = .one then 1 else 2}"
      bamUnmapped (bamUnmapped out record1 .one tags) record2 .two tags
  | .aligned answer =>
      match answer.found with
      | some pair =>
          bamMapped (bamMapped out record1 .one pair.mate1 pair.mate2 answer) record2 .two pair.mate2 pair.mate1 answer
      | none =>
          let tags := fun out => putAnswerTags out answer
          bamUnmapped (bamUnmapped out record1 .one tags) record2 .two tags

-- one chunk's uncompressed BAM records, formatted in `parts` tasks (as `samChunk`)
def bamChunk (chunk : Array (FastqRecord × FastqRecord)) (results : List PairResult) (parts : Nat) : ByteArray :=
  let pairs := chunk.zip results.toArray
  let size := (pairs.size + parts - 1) / parts
  let tasks := (List.range parts).map fun part => Task.spawn fun _ =>
    let mine := pairs.extract (part * size) ((part + 1) * size)
    -- room for the part's records (bases + qualities + names + ~120 bytes of fixed fields and tags per mate)
    let room := mine.foldl (init := 0) fun n ((r1, r2), _) =>
      n + r1.letters.size * 2 + r2.letters.size * 2 + r1.name.utf8ByteSize + r2.name.utf8ByteSize + 300
    mine.foldl (init := ByteArray.emptyWithCapacity room)
      fun out ((record1, record2), result) => bamPair out record1 record2 result
  tasks.foldl (fun bytes task => bytes ++ task.get) ByteArray.empty

end Bam

/-! ## the benchmark -/

-- user + system CPU seconds of this process (/proc/self/stat fields 14, 15, in 1/100 s)
def cpuSeconds : IO Float := do
  let stat ← IO.FS.readFile "/proc/self/stat"
  let fields := ((stat.splitOn ") ").getLast!.splitOn " ").toArray
  return (fields[11]!.toNat! + fields[12]!.toNat!).toFloat / 100.0

def secs (a b : Nat) : Float := (b - a).toFloat / 1e9

-- invented found pair for pair number `i` (150M-style), to size the mapped path; NOT a real alignment
def syntheticResult (chromosomes : ChromosomeList) (i : Nat) (len1 len2 : Nat) : PairResult :=
  let chr := i % chromosomes.size
  let start := (i * 7919) % 1000000
  let m1 : MateReport := ⟨⟨chr, start, start + len1, .forward⟩, #[(.diag, len1)], -(i % 9 : Nat)⟩
  let m2 : MateReport := ⟨⟨chr, start + 250, start + 250 + len2, .reverse⟩, #[(.diag, 40), (.gapY, 1), (.diag, len2 - 41)], -(i % 5 : Nat)⟩
  .aligned { found := some ⟨m1, m2⟩, bestPossibleScore := -(i % 17 : Nat), uniqueness := .unique, tier := .eachMateUnique }

def main (args : List String) : IO UInt32 := do
  let [indexPath, reads1Path, reads2Path, outPrefix] := args.take 4 | IO.eprintln "usage: bam_write INDEX R1 R2 OUT_PREFIX [REPS] [real|synthetic|m1] [LIMIT]"; return 1
  let reps := (args[4]?.map String.toNat!).getD 3
  let mode := args[5]?.getD "real"
  assert! mode == "real" || mode == "synthetic" || mode == "m1"
  let synthetic := mode != "real"   -- no alignPairs, no index read
  let limit := (args[6]?.map String.toNat!).getD 1000000000
  let insertSettings : InsertSettings := { range := (100, 1000) }
  let index ← if synthetic then pure ByteArray.empty else IO.FS.readBinFile indexPath
  let chromosomes ← readChromosomeList (indexPath ++ ".chromosomes")
  let reads1 ← FastqReader.ofHandle (← IO.FS.Handle.mk reads1Path .read)
  let reads2 ← FastqReader.ofHandle (← IO.FS.Handle.mk reads2Path .read)
  -- read and map all chunks once; keep chunks and results
  let t0 ← IO.monoNanosNow
  let mut chunks : Array (Array (FastqRecord × FastqRecord) × List PairResult) := #[]
  let mut total := 0
  let mut mapSecs := 0.0
  repeat
    let chunk ← readChunk reads1 reads2 (min 100000 (limit - total))
    if chunk.isEmpty then break
    let a ← IO.monoNanosNow
    let results ← if mode == "m1" then   -- the shape of today's results: no pair found
        pure (chunk.toList.map fun _ => PairResult.aligned { found := none, bestPossibleScore := -16, uniqueness := .unknown, tier := .eachMateUnique })
      else if synthetic then
        pure (chunk.toList.zipIdx.map fun ((r1, r2), i) => syntheticResult chromosomes (total + i) r1.letters.size r2.letters.size)
      else pure (alignPairs insertSettings index (chunkPairs chunk))
    assert! results.length == chunk.size   -- forces the mapping here
    mapSecs := mapSecs + secs a (← IO.monoNanosNow)
    total := total + chunk.size
    chunks := chunks.push (chunk, results)
  IO.println s!"pairs {total}, {if synthetic then "synthetic results" else "alignPairs"} {mapSecs} s (not part of the output timings)"
  let mappedCount := chunks.foldl (init := 0) fun n (_, rs) => n + (rs.filter fun r => match r with | .aligned a => a.found.isSome | _ => false).length
  IO.println s!"results with a found pair: {mappedCount}"
  -- output stage, timed on the fixed results
  for rep in [0:reps] do
    for format in ["sam", "bam"] do
      let path := outPrefix ++ "." ++ format
      let c0 ← cpuSeconds
      let w0 ← IO.monoNanosNow
      let out ← IO.FS.Handle.mk path .write
      let mut formatNs := 0
      let mut writeNs := 0
      let mut bytes := 0
      let mut recordNs := 0   -- BAM only: the uncompressed records, then the BGZF framing (CRC32 + copy)
      let header ← pure (if format == "sam" then (String.join ((samHeader chromosomes).map (· ++ "\n"))).toUTF8
                         else Bam.bgzf (Bam.bamHeader chromosomes))
      out.write header
      bytes := bytes + header.size
      for (chunk, results) in chunks do
        let a ← IO.monoNanosNow
        let (text, mid) ← if format == "sam" then pure (samChunk chromosomes chunk results 16, a)
          else do
            let records := Bam.bamChunk chunk results 16
            let _ := records.size
            let mid ← IO.monoNanosNow
            pure (Bam.bgzf records, mid)
        let size := text.size   -- forces the formatting here
        let b ← IO.monoNanosNow
        recordNs := recordNs + (mid - a)
        out.write text
        let c ← IO.monoNanosNow
        formatNs := formatNs + (b - a)
        writeNs := writeNs + (c - b)
        bytes := bytes + size
      if format == "bam" then
        out.write Bam.eofBlock
        bytes := bytes + Bam.eofBlock.size
      out.flush
      let w1 ← IO.monoNanosNow
      let c1 ← cpuSeconds
      IO.println s!"rep {rep} {format}: bytes {bytes}, format {formatNs.toFloat / 1e9} s, write {writeNs.toFloat / 1e9} s, (BAM: records {recordNs.toFloat / 1e9} s) wall {secs w0 w1} s, cpu {c1 - c0} s"
  return 0
