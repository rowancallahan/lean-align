import Spec.Fastq

/-! Benchmark only (unproved IO): CPU of `AdapterTrim.cutTruSeq` on the mates of a FASTQ file, and how
many reads it cuts / bases it removes.   adapter_bench READS.fq [REPEAT] -/

def main (args : List String) : IO Unit := do
  let path := args[0]!
  let rep := (args[1]?.bind String.toNat?).getD 5
  let reader ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk path .read)
  let mut reads : Array (ByteArray × ByteArray) := #[]
  repeat
    let some r ← Spec.readFastqRecord reader | break
    reads := reads.push (r.letters, r.quality.toUTF8)
  let mut cut := 0
  let mut removed := 0
  for (l, q) in reads do
    let (l', _) := AdapterTrim.cutTruSeq l q
    if l'.size < l.size then cut := cut + 1
    removed := removed + (l.size - l'.size)
  IO.println s!"reads {reads.size} cut {cut} bases_removed {removed}"
  for _ in [0:rep] do
    let t0 ← IO.monoNanosNow
    let mut s := 0
    for (l, _) in reads do
      s := s + AdapterTrim.cutPos AdapterTrim.truSeq 6 1 l
    let t1 ← IO.monoNanosNow
    IO.println s!"scan {(t1 - t0).toFloat / 1e6} ms ({s})"
