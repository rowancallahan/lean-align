import LowErrorMapper
import LeanAlign.Mapper

/-!
Benchmark only (prints to stdout; not part of the tool).

    lake exe lowerr_bench <genome.txt> <reads.txt> <l0> <T>

Maps every read with `mapWithIndex` and with `mapLowErrorIndex` (both proved
equal to `mapSpec`), times each, and fails if any answer differs.
-/

open MapSpec LeanAlign.Mapper

def scoring : AlignmentSpec.Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

def readNamed (path : String) : IO (List Named) := do
  let text ← IO.FS.readFile path
  match parseNamed ((text.splitOn "\n").filter (· ≠ "")) with
  | .ok xs => return xs
  | .error e => throw (IO.userError e)

def main (args : List String) : IO UInt32 := do
  let genomePath :: readsPath :: l0s :: ts :: _ := args
    | IO.eprintln "usage: lowerr_bench <genome> <reads> <l0> <T>"; return 2
  let some l0 := l0s.toNat? | return 2
  let some T := ts.toInt? | return 2
  let chromosomes ← readNamed genomePath
  let reads ← readNamed readsPath
  let genome : Genome := chromosomes.map fun (x : Named) => { name := x.name, seq := x.seq.toList }
  let idx := buildIndex l0 genome
  let ga := genomeArrays genome
  let ref ← IO.mkRef (idx, ga)
  IO.println s!"index words: {idx.table.size}  chromosomes: {ga.size}"
  let (idx, ga) ← ref.get
  let t0 ← IO.monoNanosNow
  let mut fast : Array (Option (Window × Int)) := #[]
  for (r : Named) in reads do
    fast := fast.push (mapLowErrorIndex scoring T idx ga r.seq.toList)
  let keepF ← IO.mkRef fast
  let t1 ← IO.monoNanosNow
  let mut slow : Array (Option (Window × Int)) := #[]
  for (r : Named) in reads do
    slow := slow.push (mapWithIndex scoring T idx r.seq.toList)
  let keepS ← IO.mkRef slow
  let t2 ← IO.monoNanosNow
  let fastR ← keepF.get
  let slowR ← keepS.get
  let diff := ((fastR.zip slowR).filter fun (a, b) => a != b).size
  let sF := Float.ofNat (t1 - t0) / 1.0e9
  let sS := Float.ofNat (t2 - t1) / 1.0e9
  IO.println s!"reads: {fastR.size}  mapped: {(fastR.filter (·.isSome)).size}  differences: {diff}"
  IO.println s!"lowError_seconds: {sF}  reads_per_second: {Float.ofNat fastR.size / sF}"
  IO.println s!"mapWith_seconds: {sS}  reads_per_second: {Float.ofNat slowR.size / sS}"
  return (if diff == 0 then 0 else 1)
