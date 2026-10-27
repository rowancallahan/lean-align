import SeedMapper2
import LeanAlign.Mapper

/-!
Benchmark only (prints to stdout; not part of the tool).

    lake exe map_bench2 <mode> <genome.txt> <reads.txt> <l0> <T> [truth.tsv]

Like `map_bench`; `mode` picks the mapping call: `1` = `mapWithIndex`,
`2` = `mapWithIndex2`, `2v` = `mapWithIndex2V` (each proved = `mapSpec`).
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
  let mode :: genomePath :: readsPath :: l0s :: ts :: rest := args
    | IO.eprintln "usage: map_bench2 <1|2|2v> <genome> <reads> <l0> <T> [truth.tsv]"; return 2
  let f := match mode with
    | "2" => mapWithIndex2
    | "2v" => mapWithIndex2V
    | _ => mapWithIndex
  let some l0 := l0s.toNat? | return 2
  let some T := ts.toInt? | return 2
  let chromosomes ← readNamed genomePath
  let reads ← readNamed readsPath
  let genome : Genome := chromosomes.map fun (x : Named) => { name := x.name, seq := x.seq.toList }
  let t0 ← IO.monoNanosNow
  let idx := buildIndex l0 genome
  let idxRef ← IO.mkRef idx
  IO.println s!"index words: {idx.table.size}"
  let t1 ← IO.monoNanosNow
  let idx ← idxRef.get
  let mut results : Array (String × Option (Window × Int)) := #[]
  for (r : Named) in reads do
    results := results.push (r.name, f scoring T idx r.seq.toList)
  let keep ← IO.mkRef results
  let t2 ← IO.monoNanosNow
  let done ← keep.get
  let mapped := (done.filter fun x => x.2.isSome).size
  let secs := Float.ofNat (t2 - t1) / 1.0e9
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1.0e9}"
  IO.println s!"map_seconds: {secs}"
  IO.println s!"reads: {done.size}  mapped: {mapped}  reads_per_second: {Float.ofNat done.size / secs}"
  match rest with
  | truthPath :: _ =>
    let lines := ((← IO.FS.readFile truthPath).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, (_, res)) in lines.zip done.toList do
      match line.splitOn "\t", res with
      | [_, chrName, pos, _], some (w, _) =>
        let name := (chromosomes[w.chr]?.map (·.name)).getD ""
        if name == chrName && pos.toNat? == some (w.start + 1) then right := right + 1
      | _, _ => pure ()
    IO.println s!"mapped_at_true_position: {right}"
  | [] => pure ()
  return 0
