import ParMap
import LeanAlign.Mapper

/-!
Benchmark only (prints to stdout; not part of the tool).  Checks that
`ParMap.parMap` runs its batches in parallel and shares read-only data.

    lake exe par_bench synth <threads> <items> <work> <sharedMB>
    lake exe par_bench map <genome.txt> <reads.txt> <l0> <T> <threads>

`synth`: every item does `work` pseudo-random reads of a shared `sharedMB` MB
byte array.  `map`: `MapSpec.mapWithIndex` through `parMap` (the function of
`mapReadsParArray_eq_mapSpec`).  Both print wall time and peak RSS (VmHWM).
-/

open MapSpec LeanAlign.Mapper ParMap

def peakRssMB : IO Nat := do
  let st ← IO.FS.readFile "/proc/self/status"
  let line := ((st.splitOn "\n").find? (·.startsWith "VmHWM:")).get!
  let kb := ((line.splitOn " ").filter (· ≠ "")).getD 1 "0"
  return kb.toNat! / 1024

def work (shared : ByteArray) (steps : Nat) (i : Nat) : UInt64 := Id.run do
  let mut h : UInt64 := i.toUInt64 * 0x9E3779B97F4A7C15 + 1
  let mut acc : UInt64 := 0
  let n := shared.size.toUInt64
  for _ in [0:steps] do
    h := h ^^^ (h <<< 13); h := h ^^^ (h >>> 7); h := h ^^^ (h <<< 17)
    acc := acc + (shared.get! (h % n).toNat).toUInt64
  return acc

def scoring : AlignmentSpec.Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

def readNamed (path : String) : IO (List Named) := do
  let text ← IO.FS.readFile path
  match parseNamed ((text.splitOn "\n").filter (· ≠ "")) with
  | .ok xs => return xs
  | .error e => throw (IO.userError e)

def timeIt {β : Type} (label : String) (x : Unit → β) (sz : β → Nat) : IO β := do
  let t0 ← IO.monoNanosNow
  let r ← IO.mkRef (x ())
  let v ← r.get
  let n := sz v
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: items {n}  seconds {Float.ofNat (t1 - t0) / 1.0e9}  peak_rss_MB {← peakRssMB}"
  return v

def main (args : List String) : IO UInt32 := do
  match args with
  | ["synth", ts, ns, ws, mbs] =>
    let nt := ts.toNat!; let items := ns.toNat!; let steps := ws.toNat!
    let shared := ByteArray.mk (Array.ofFn (n := mbs.toNat! * 1048576) fun i => (i.val * 31 % 251).toUInt8)
    IO.println s!"shared bytes: {shared.size}  peak_rss_MB {← peakRssMB}"
    let xs := Array.range items
    let res ← timeIt s!"synth threads {nt}" (fun _ => parMap nt (work shared steps) xs) (·.size)
    IO.println s!"checksum: {res.foldl (· + ·) 0}"
    return 0
  | ["map", gp, rp, l0s, tstr, ts] =>
    let l0 := l0s.toNat!; let T := tstr.toInt!; let nt := ts.toNat!
    let genome : Genome := (← readNamed gp).map fun (x : Named) => { name := x.name, seq := x.seq.toList }
    let reads : Array (List Char) := ((← readNamed rp).map fun (x : Named) => x.seq.toList).toArray
    let idxRef ← IO.mkRef (buildIndex l0 genome)
    let idx ← idxRef.get
    IO.println s!"index words: {idx.table.size}  peak_rss_MB {← peakRssMB}"
    let res ← timeIt s!"map threads {nt}" (fun _ => parMap nt (mapWithIndex scoring T idx) reads) (·.size)
    IO.println s!"mapped: {(res.filter (·.isSome)).size}"
    return 0
  | _ => IO.eprintln "usage: see bench/ParBench.lean"; return 2
