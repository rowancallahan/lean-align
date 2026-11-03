import Proofs.Sam
/-! DRAFT for Rowan (not built by lake, not part of Spec/). The SAM output file as bytes, stated with the
readable String functions already in Spec/Sam.lean. A fast byte writer (S4's samChunkB, research/io2) is
proved to produce exactly `samFile`. -/
namespace Spec.Draft

-- one text line per String, each followed by '\n', as bytes
def linesBytes (lines : List String) : ByteArray := (String.join (lines.map (· ++ "\n"))).toUTF8

-- THE output spec: the header, then each pair's lines, pairs in input order
def samFile (chromosomes : ChromosomeList) (pairs : List ((FastqRecord × FastqRecord) × PairResult)) : ByteArray :=
  linesBytes (samHeader chromosomes) ++
    linesBytes (pairs.flatMap fun ((record1, record2), result) => samLines chromosomes record1 record2 result)

-- chunking does not change the file: writing chunk after chunk = writing all pairs at once
theorem samFile_chunks (chromosomes : ChromosomeList) (chunks : List (List ((FastqRecord × FastqRecord) × PairResult))) :
    samFile chromosomes chunks.flatten =
      linesBytes (samHeader chromosomes) ++
        (chunks.map fun c => linesBytes (c.flatMap fun ((r1, r2), res) => samLines chromosomes r1 r2 res)).foldl (· ++ ·) ByteArray.empty := by
  sorry

-- the digit writer a byte SAM writer needs: decimal digits pushed straight into the buffer
def pushNat (out : ByteArray) (n : Nat) : ByteArray := out ++ (toString n).toUTF8   -- spec; fast version proved equal

end Spec.Draft
