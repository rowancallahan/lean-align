import Proofs.Aligner

/-! Index round trip on a tiny synthetic genome: `lake env lean tests/IndexRoundTrip.lean`.
Expected: `(442, #[0, 300, 430], #[300, 130, 12], ?, true, true, true, true, true)` (genome
letters, offsets, lengths, index bytes (B = 26: 2^26 + 1 bucket offsets), indexOk of what the saved
index loads to, the loaded genome and slots are the saved bytes, buildIndex = saved, empty and
truncated indexes load to none). Interpreted: ~12 min. These
chromosomes are < 2^20 letters, so the builder takes the `buildWP` path, not `buildWV`. -/

open Spec

def tinyGenome : GenomeFile :=
  let lcg (s : Nat) := (s * 1103515245 + 12345) % 2147483648
  let chrom (seed n : Nat) : ByteArray := Id.run do
    let mut s := seed
    let mut b := ByteArray.empty
    for i in [0:n] do
      s := lcg s
      b := b.push (if i % 97 == 50 then 78 else (#[65, 67, 71, 84] : Array UInt8)[(s / 65536) % 4]!)
    return b
  #[("chr1", chrom 1 300), ("chr2", chrom 2 130), ("chrM", "ACGTNNNNACGT".toUTF8)]

#eval
  let L := buildLoaded tinyGenome
  let saved := saveIndex L
  let ld := (loadIndex saved).get!
  let ok := indexOk tinyGenome ld
  let shared := ld.2.1.w.size == saved.size && ld.1.sl.size == saved.size
  let built := buildIndex tinyGenome
  (L.2.1.n, L.2.2.1, L.2.2.2, saved.size, ok, shared, built.size == saved.size,
    loadIndex ByteArray.empty |>.isNone, loadIndex (saved.extract 0 (saved.size - 1)) |>.isNone)
