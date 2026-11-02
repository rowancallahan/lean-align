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
  -- after adapter cut + quality trim: mates already empty, and non-empty mates shorter than 25 / 50
  let mut empty := 0
  let mut short25 := 0
  let mut short50 := 0
  let mut emptyQ := 0
  for (l, q) in reads do
    let (l', q') := AdapterTrim.cutTruSeq l q
    let n := match ReadTrim.trimRead l' q' with | some (s, e) => e - s | none => 0
    let n0 := match ReadTrim.trimRead l q with | some (s, e) => e - s | none => 0
    if n0 == 0 then emptyQ := emptyQ + 1
    if n == 0 then empty := empty + 1
    else
      if n < 25 then short25 := short25 + 1
      if n < 50 then short50 := short50 + 1
  IO.println s!"empty_quality_only {emptyQ} empty_after_cut {empty} removed_by_min25 {short25} removed_by_min50 {short50}"
  for _ in [0:rep] do
    let t0 ← IO.monoNanosNow
    let mut s := 0
    for (l, _) in reads do
      s := s + AdapterTrim.cutPos AdapterTrim.truSeq 6 1 l
    let t1 ← IO.monoNanosNow
    IO.println s!"scan {(t1 - t0).toFloat / 1e6} ms ({s})"
