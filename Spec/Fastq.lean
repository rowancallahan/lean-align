import ReadTrim

/-! # Paired FASTQ reading. Unproved (trusted) plumbing for the shim: the file is read in 4 MB blocks
and split into lines on newline bytes; only the read name and qualities become Strings. Each mate is
quality-trimmed with the proved trimmer (`ReadTrim.trimRead`) as it is read. -/

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

def readFastqRecord (reader : FastqReader) : IO (Option FastqRecord) := do
  let some header ← reader.line | return none
  let some letters ← reader.line | return none
  let some _plus ← reader.line | return none
  let some quality ← reader.line | return none
  return some { name := String.fromUTF8! (header.extract 1 header.size), letters,
                quality := String.fromUTF8! quality }

-- a read's name without its comment (after the first space) and without a trailing "/1" or "/2"
def mateName (name : String) : String :=
  let base := (name.splitOn " ").headD ""
  if base.endsWith "/1" || base.endsWith "/2" then String.ofList (base.toList.dropLast.dropLast) else base

-- quality trimming with the proved trimmer: keep the best window of letters and qualities; a mate
-- with nothing worth keeping comes back with no letters (trimmed away)
def trimRecord (record : FastqRecord) : FastqRecord :=
  let qual := record.quality.toUTF8
  match ReadTrim.trimRead record.letters qual with
  | some (s, e) => { record with letters := record.letters.extract s e,
                                 quality := String.fromUTF8! (qual.extract s e) }
  | none => { record with letters := ByteArray.empty, quality := "" }

-- up to `size` pairs, reading the two FASTQ files in step; stops with an error if two mates'
-- names differ or one file ends before the other (the files are out of step)
def readChunk (reads1 reads2 : FastqReader) (size : Nat) : IO (Array (FastqRecord × FastqRecord)) := do
  let mut chunk := #[]
  for _ in [0:size] do
    match ← readFastqRecord reads1, ← readFastqRecord reads2 with
    | some record1, some record2 =>
      if mateName record1.name != mateName record2.name then
        throw (IO.userError s!"FASTQ files out of step: mate names {record1.name} / {record2.name}")
      if record1.letters.size != record1.quality.utf8ByteSize || record2.letters.size != record2.quality.utf8ByteSize then
        throw (IO.userError s!"FASTQ record {record1.name}: sequence and quality lengths differ")
      chunk := chunk.push (trimRecord record1, trimRecord record2)
    | none, none => break
    | _, _ => throw (IO.userError "FASTQ files out of step: one file has more reads than the other")
  return chunk

end Spec
