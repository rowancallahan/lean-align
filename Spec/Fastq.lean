import ReadTrim
import AdapterTrim

/-! # Paired FASTQ reading. Unproved (trusted) plumbing for the shim: the file is read in 4 MB blocks
and split into lines on newline bytes; only the read name and qualities become Strings. Each mate is
cut at the TruSeq adapter (`AdapterTrim.cutTruSeq`, proved) then quality-trimmed with the proved
trimmer (`ReadTrim.trimRead`), then dropped if shorter than `minLength` (`AdapterTrim.dropShort`). Reading (`readChunk`) and
trimming (`trimChunk`, many pairs at once) are separate steps. -/

namespace Spec

-- one FASTQ record: the read's name, its letters, and their qualities
structure FastqRecord where
  name    : String
  letters : ByteArray
  quality : String

-- a FASTQ file read in blocks: the unread bytes are `buffer` from `pos` on
structure FastqReader where
  handle : IO.FS.Handle
  buffer : IO.Ref ByteArray
  pos    : IO.Ref Nat

def FastqReader.ofHandle (handle : IO.FS.Handle) : IO FastqReader :=
  return { handle, buffer := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef 0 }

-- the first newline byte at or after `i` (or `bytes.size` when there is none)
def findNewline (bytes : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < bytes.size && bytes[j]! != 10 do
    j := j + 1
  return j

-- the next line without its "\n" (or "\r\n"); none at the end of the file
def FastqReader.line (reader : FastqReader) : IO (Option ByteArray) := do
  repeat
    let buffer ← reader.buffer.get
    let pos ← reader.pos.get
    let newline := findNewline buffer pos
    if newline < buffer.size then
      reader.pos.set (newline + 1)
      let stop := if pos < newline && buffer[newline - 1]! == 13 then newline - 1 else newline
      return some (buffer.extract pos stop)
    let block ← reader.handle.read (4 * 1024 * 1024)
    if block.isEmpty then
      reader.buffer.set ByteArray.empty
      reader.pos.set 0
      return if pos < buffer.size then some (buffer.extract pos buffer.size) else none
    reader.buffer.set (buffer.extract pos buffer.size ++ block)
    reader.pos.set 0
  return none

-- every byte satisfies `p`
def allBytes (p : UInt8 → Bool) (bytes : ByteArray) : Bool := Nat.all bytes.size fun i _ => p bytes[i]!

-- `allBytes` as one loop over the bytes, last first; compiled code runs it (`allBytes_eq`)
@[specialize] def allBytesGo (p : UInt8 → Bool) (bytes : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => p bytes[n]! && allBytesGo p bytes n

@[inline] def allBytesF (p : UInt8 → Bool) (bytes : ByteArray) : Bool := allBytesGo p bytes bytes.size

theorem allBytesGo_eq (p : UInt8 → Bool) (bytes : ByteArray) :
    ∀ n, allBytesGo p bytes n = Nat.all n fun i _ => p bytes[i]!
  | 0 => by simp [allBytesGo]
  | n + 1 => by rw [allBytesGo, Nat.all_succ, allBytesGo_eq p bytes n, Bool.and_comm]

@[csimp] theorem allBytes_eq : @allBytes = @allBytesF := by
  funext p bytes
  exact (allBytesGo_eq p bytes bytes.size).symm

-- the letters the spec's `GenomeIsDNA` allows: A C G T N
def isDnaByte (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84 || b == 78

-- the four lines of a record, checked: header '@' + printable ASCII, '+' line, letters A C G T N, qualities '!'..'~'.
-- Pure, so that `Proofs/TrimRecord.lean` can state what every record the reader returns satisfies.
def parseRecord (header letters plus quality : ByteArray) : Except String FastqRecord :=
  if !(0 < header.size && header[0]! == 64 && allBytes (fun b => 32 ≤ b && b ≤ 126) header) then
    .error "header line is not '@' + printable ASCII"
  else if !(0 < plus.size && plus[0]! == 43) then .error "third line of a record does not start with '+'"
  else if !allBytes isDnaByte letters then .error "letters other than A C G T N (lowercase, IUPAC)"
  else if !allBytes (fun b => 33 ≤ b && b ≤ 126) quality then .error "quality outside '!'..'~'"
  else .ok { name := String.fromUTF8! (header.extract 1 header.size), letters, quality := String.fromUTF8! quality }

def readFastqRecord (reader : FastqReader) : IO (Option FastqRecord) := do
  let some header ← reader.line | return none
  let cut := throw (IO.userError "FASTQ: file ends inside a record")
  let some letters ← reader.line | cut
  let some plus ← reader.line | cut
  let some quality ← reader.line | cut
  match parseRecord header letters plus quality with
  | .ok record => return some record
  | .error why => throw (IO.userError s!"FASTQ: {why}")

-- a read's name without its comment (after the first space) and without a trailing "/1" or "/2"
def mateName (name : String) : String :=
  let base := (name.splitOn " ").headD ""
  if base.endsWith "/1" || base.endsWith "/2" then String.ofList (base.toList.dropLast.dropLast) else base

-- shortest mate kept after trimming; shorter mates become empty (trimmed away)
def minLength : Nat := 25

-- adapter cut, then quality trimming, then the minimum length, all with proved functions: cut letters
-- and qualities at the first TruSeq adapter, keep the best window, and drop a mate shorter than
-- `minLength`; a mate with nothing worth keeping comes back with no letters (trimmed away)
def trimRecord (record : FastqRecord) : FastqRecord :=
  let (letters, qual) := AdapterTrim.cutTruSeq record.letters record.quality.toUTF8
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  let (letters, qual) := AdapterTrim.dropShort minLength letters qual
  { record with letters, quality := String.fromUTF8! qual }

-- up to `size` pairs, reading the two FASTQ files in step; stops with an error if two mates'
-- names differ or one file ends before the other (the files are out of step); the pairs come back
-- untrimmed, as read (`trimChunk` trims them)
def readChunk (reads1 reads2 : FastqReader) (size : Nat) : IO (Array (FastqRecord × FastqRecord)) := do
  let mut chunk := #[]
  for _ in [0:size] do
    match ← readFastqRecord reads1, ← readFastqRecord reads2 with
    | some record1, some record2 =>
      if mateName record1.name != mateName record2.name then
        throw (IO.userError s!"FASTQ files out of step: mate names {record1.name} / {record2.name}")
      for record in [record1, record2] do
        let name := mateName record.name
        unless 0 < name.length && name.length ≤ 254 && name.all (fun c => ('!' ≤ c && c ≤ '?') || ('A' ≤ c && c ≤ '~')) do
          throw (IO.userError s!"FASTQ: read name '{record.name}' is not a SAM QNAME")
      if record1.letters.size != record1.quality.utf8ByteSize || record2.letters.size != record2.quality.utf8ByteSize then
        throw (IO.userError s!"FASTQ record {record1.name}: sequence and quality lengths differ")
      chunk := chunk.push (record1, record2)
    | none, none => break
    | _, _ => throw (IO.userError "FASTQ files out of step: one file has more reads than the other")
  return chunk

-- trim every pair of a chunk with `trimRecord`, in `parts` tasks running at once; the result is the
-- pairs in their original order, each trimmed (`trimChunk_eq`, Proofs/TrimRecord.lean)
def trimChunk (chunk : Array (FastqRecord × FastqRecord)) (parts : Nat) : Array (FastqRecord × FastqRecord) :=
  let size := (chunk.size + parts - 1) / parts
  let tasks := (List.range parts).map fun part => Task.spawn fun _ =>
    (chunk.extract (part * size) ((part + 1) * size)).map fun (record1, record2) => (trimRecord record1, trimRecord record2)
  tasks.foldl (fun out task => out ++ task.get) #[]

-- a chunk of read pairs, as `alignPairs` takes them: a mate trimmed away (no letters left) is `none`
def chunkPairs (chunk : Array (FastqRecord × FastqRecord)) : List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (record1, record2) =>
    (if record1.letters.isEmpty then none else some record1.letters,
     if record2.letters.isEmpty then none else some record2.letters)

end Spec
