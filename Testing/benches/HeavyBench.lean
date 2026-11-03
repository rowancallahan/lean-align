import Proofs.HeavyBuild
import Spec.Fasta

/-! Benchmark only (unproved IO): `heavy_bench GENOME.fa OUT` builds `HeavyBuild.table`, prints its entries and time,
writes the table bytes to OUT. -/

def main (args : List String) : IO Unit := do
  let [fa, out] := args | throw (IO.userError "usage: heavy_bench GENOME.fa OUT")
  let t0 ← IO.monoMsNow
  let g ← Spec.readFasta (← IO.FS.Handle.mk fa .read)
  let t1 ← IO.monoMsNow
  IO.println s!"read {g.size} chromosomes in {t1 - t0} ms"
  let H := Spec.HeavyBuild.table (g.map (·.2))
  IO.println s!"entries {H.size / 25} ({H.size} bytes)"
  let t2 ← IO.monoMsNow
  IO.println s!"table built in {t2 - t1} ms"
  IO.FS.writeBinFile out H
