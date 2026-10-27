/-! # Paired FASTQ reading. Unproved (trusted) plumbing for the shim: the file is read in 4 MB blocks
and split into lines on newline bytes; only the read name and qualities become Strings. -/

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

-- up to `size` pairs, reading the two FASTQ files in step
def readChunk (reads1 reads2 : FastqReader) (size : Nat) : IO (Array (FastqRecord × FastqRecord)) := do
  let mut chunk := #[]
  for _ in [0:size] do
    match ← readFastqRecord reads1, ← readFastqRecord reads2 with
    | some record1, some record2 => chunk := chunk.push (record1, record2)
    | _, _ => break
  return chunk

end Spec
