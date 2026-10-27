/-! # Paired FASTQ reading. Unproved (trusted) plumbing for the shim. -/

namespace Spec

-- one FASTQ record: the read's name, its letters, and their qualities
structure FastqRecord where
  name    : String
  letters : ByteArray
  quality : String

def readFastqRecord (handle : IO.FS.Handle) : IO (Option FastqRecord) := do
  let header ← handle.getLine
  if header.isEmpty then
    return none
  let letters ← handle.getLine
  let _plus ← handle.getLine
  let quality ← handle.getLine
  return some { name := (header.trimAscii.toString.drop 1).toString,
                letters := letters.trimAscii.toString.toUTF8,
                quality := quality.trimAscii.toString }

-- up to `size` pairs, reading the two FASTQ files in step
def readChunk (reads1 reads2 : IO.FS.Handle) (size : Nat) : IO (Array (FastqRecord × FastqRecord)) := do
  let mut chunk := #[]
  for _ in [0:size] do
    match ← readFastqRecord reads1, ← readFastqRecord reads2 with
    | some record1, some record2 => chunk := chunk.push (record1, record2)
    | _, _ => break
  return chunk

end Spec
