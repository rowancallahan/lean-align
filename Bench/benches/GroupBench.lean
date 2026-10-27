import ParGroup
import LeanAlign.Mapper

/-!
Benchmark only (prints to stdout; not part of the tool).  Plain streaming
(`ParMap.streamTasks`) against the grouped pipelines of `ParGroup`.

    lake exe group_bench <mode> <workers> <items> <steps> <dupPercent> <chunk> <bin> <out-file>

Items are 100-letter ACGT strings; `dupPercent` % of them copy an earlier item.
Per item: `steps` xorshift rounds seeded by the item's letters (CPU only), then
one ~100-byte line.  Modes:
  plain  streamTasks workers chunk                      (no grouping)
  dedup  pipelineTasks workers chunk bin (first 10 letters order)
  dedupns  same, keys left in first-seen order (comparison always true)
  sort   streamTasksH workers chunk, sortMap inside each chunk (no dedup)
The writer writes each task's UTF-8 bytes in order and drops the task.

    lake exe group_bench map <genome.txt> <reads.txt> <l0> <T> <bin> <dupPercent>

Mapper (`MapSpec.mapWithIndex`, dedicated tasks of `bin` reads): `parMapBins`
against `dedupMap` on the reads with `dupPercent` % replaced by earlier reads.
-/

open ParMap

def peakRssMB : IO Nat := do
  let st ← IO.FS.readFile "/proc/self/status"
  let line := ((st.splitOn "\n").find? (·.startsWith "VmHWM:")).get!
  return ((line.splitOn " ").filter (· ≠ "")).getD 1 "0" |>.toNat! |> (· / 1024)

def mix (h : UInt64) : UInt64 :=
  let h := h ^^^ (h <<< 13); let h := h ^^^ (h >>> 7); h ^^^ (h <<< 17)

def randRead (seed : Nat) : String := Id.run do
  let mut h : UInt64 := seed.toUInt64 * 0x9E3779B97F4A7C15 + 7
  let mut s := ""
  for _ in [0:100] do
    h := mix h
    s := s.push ("ACGT".toList[(h % 4).toNat]!)
  return s

def makeItems (n dup : Nat) : Array String := Id.run do
  let mut xs : Array String := Array.emptyWithCapacity n
  for i in [0:n] do
    let h := mix (i.toUInt64 + 12345)
    if i > 0 && (h % 100).toNat < dup then xs := xs.push xs[(mix h % i.toUInt64).toNat]!
    else xs := xs.push (randRead i)
  return xs

def cpu (steps : Nat) (s : String) : String × UInt64 := Id.run do
  let mut h : UInt64 := 1
  for c in s.toList do h := mix (h + c.toNat.toUInt64)
  for _ in [0:steps] do h := mix h
  return (s.take 12 |>.toString, h)

def fmt (r : String × UInt64) : String :=
  let v := r.2
  s!"{r.1}\t{v}\t{v * 3}\t{v * 7}\t{v * 11}\n"

def le10 (a b : String) : Bool := decide ((a.take 10).toString ≤ (b.take 10).toString)

def writeAll (h : IO.FS.Handle) : List (Task String) → Nat → IO Nat
  | [], n => pure n
  | t :: ts, n => do
    let s := t.get
    h.write s.toUTF8
    writeAll h ts (n + s.utf8ByteSize)

def scoring : AlignmentSpec.Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

def readNamed (path : String) : IO (List LeanAlign.Mapper.Named) := do
  match LeanAlign.Mapper.parseNamed (((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")) with
  | .ok xs => return xs
  | .error e => throw (IO.userError e)

def timeIt {β : Type} (label : String) (x : Unit → Array β) : IO (Array β) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.mkRef (x ())
  let v ← r.get
  let n := v.size
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: reads {n}  seconds {Float.ofNat (t1 - t0) / 1.0e9}"
  return v

def mapMode (gp rp : String) (l0 : Nat) (T : Int) (bin dup : Nat) : IO UInt32 := do
  let genome : MapSpec.Genome := (← readNamed gp).map fun x => { name := x.name, seq := x.seq.toList }
  let base : Array (List Char) := ((← readNamed rp).map fun x => x.seq.toList).toArray
  let mut reads : Array (List Char) := #[]
  for i in [0:base.size] do
    let h := mix (i.toUInt64 + 12345)
    if i > 0 && (h % 100).toNat < dup then reads := reads.push reads[(mix h % i.toUInt64).toNat]!
    else reads := reads.push base[i]!
  let idxRef ← IO.mkRef (MapSpec.buildIndex l0 genome)
  let idx ← idxRef.get
  IO.println s!"reads {reads.size} distinct {(distinct reads).size}"
  let f := MapSpec.mapWithIndex scoring T idx
  let a ← timeIt s!"parMapBins bin {bin}" fun _ => parMapBins .dedicated bin f reads
  let b ← timeIt s!"dedupMap bin {bin}" fun _ => dedupMap .dedicated bin (fun _ _ => true) f reads
  IO.println s!"same answers: {a.toList == b.toList}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let ["map", gp, rp, l0s, ts, bs, ds] := args then
    return ← mapMode gp rp l0s.toNat! ts.toInt! bs.toNat! ds.toNat!
  let [mode, ws, ns, ss, ds, cs, bs, out] := args | IO.eprintln "usage: see bench/GroupBench.lean"; return 2
  let w := ws.toNat!; let steps := ss.toNat!; let chunk := cs.toNat!; let bin := bs.toNat!
  let r ← IO.mkRef (makeItems ns.toNat! ds.toNat!)
  let xs ← r.get
  let nd := (distinct xs).size
  let t0 ← IO.monoNanosNow
  let h ← IO.FS.Handle.mk out .write
  let tasks :=
    if mode == "plain" then streamTasks w chunk (cpu steps) fmt xs
    else if mode == "dedup" then pipelineTasks w chunk bin le10 (cpu steps) fmt xs
    else if mode == "dedupns" then pipelineTasks w chunk bin (fun _ _ => true) (cpu steps) fmt xs
    else streamTasksH w chunk (fun c => formatAll fmt (sortMap .default bin le10 (cpu steps) c)) xs
  let bytes ← writeAll h tasks.toList 0
  h.flush
  let t1 ← IO.monoNanosNow
  IO.println s!"{mode} w {w} items {xs.size} distinct {nd} chunk {chunk} bin {bin}: seconds {Float.ofNat (t1 - t0) / 1.0e9}  bytes {bytes}  peak_rss_MB {← peakRssMB}"
  return 0
