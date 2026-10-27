import SeedMapper
import LeanAlign.Mapper

/-!
Benchmark only.  Per-read results of the proved mapper (`MapSpec.mapWithIndex`):

    lake exe map_dump <genome.txt> <reads.txt> <l0> <T> <n_reads>

prints `name<TAB>start<TAB>len<TAB>score` or `name<TAB>none` per read.
-/

open MapSpec LeanAlign.Mapper

def scoring : AlignmentSpec.Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

def readNamed (path : String) : IO (List Named) := do
  match parseNamed (((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")) with
  | .ok xs => return xs
  | .error e => throw (IO.userError e)

def main (args : List String) : IO UInt32 := do
  let [gp, rp, l0s, ts, ns] := args | panic! "usage: map_dump <genome> <reads> <l0> <T> <n>"
  let genome : Genome := (← readNamed gp).map fun x => { name := x.name, seq := x.seq.toList }
  let idx := buildIndex l0s.toNat! genome
  for r in (← readNamed rp).take ns.toNat! do
    match mapWithIndex scoring ts.toInt! idx r.seq.toList with
    | some (w, s) => IO.println s!"{r.name}\t{w.start}\t{w.len}\t{s}"
    | none => IO.println s!"{r.name}\tnone"
    (← IO.getStdout).flush
  return 0
