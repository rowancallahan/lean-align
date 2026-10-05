import MzView
import ParMap

/-!
Benchmark only (unproved IO).  Whole genome with the genome held once
(codecs/MzView.lean: `buildWV_eq`, `check3V_eq`, `pairFastGB_view_eq_pairSpec`).

    lake exe whole_genome build <index_prefix> <chr.fa>...       build over the view, save
    lake exe whole_genome bytes <index_prefix> <chr.fa>...       same with `Mz.buildW` on the concatenation
    WG_READS='r1:r2:dump.tsv|-:limit|0;…' WG_TASKS=1,4 lake exe whole_genome map <index_prefix> <chr.fa>...
    env: WG_K (22) WG_B (26) WG_C (0) WG_W (5) WG_T (6)  index; WG_P (16) WG_MIN (100) WG_MAX (1000)
         WG_TASKS (1)  WG_MINLEN (150 at P = 16, 100 at P = 12): pairs with a shorter mate are skipped
Chromosome files: one record each.  Mates: `>name` / sequence lines, or FASTQ.
Index files: <prefix>.meta (k B c sw t pb nruns), .offs, .sl, .runs (LE u64).
-/

open MapSpec MapSpec.Fast

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  return " ".intercalate ((s.splitOn "\n").filter (fun l => l.startsWith "VmHWM" || l.startsWith "VmRSS")
    |>.map (fun l => l.replace "\t" "" |>.replace "  " ""))

def envN (k : String) (d : Nat) : IO Nat := do return ((← IO.getEnv k).map String.toNat!).getD d

/-- A one-record FASTA, sequence only, into one buffer of the file's size (no copy). -/
def readChrom (path : String) : IO ByteArray := do
  let total := (← System.FilePath.metadata path).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let mut cur := ByteArray.emptyWithCapacity total
  let mut header := true
  repeat
    let chunk ← h.read 16777216
    if chunk.isEmpty then break
    let mut i := 0
    if header then
      while i < chunk.size && chunk.get! i != 10 do i := i + 1
      if i < chunk.size then header := false; i := i + 1
    while i < chunk.size do
      let mut j := i
      while j < chunk.size && chunk.get! j != 10 && chunk.get! j != 13 do j := j + 1
      cur := chunk.copySlice i cur cur.size (j - i)
      i := j + 1
  assert! !header
  return cur

/-- A binary file into one buffer of its size. -/
def readBin (path : String) : IO ByteArray := do
  let total := (← System.FilePath.metadata path).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let mut cur := ByteArray.emptyWithCapacity total
  repeat
    let chunk ← h.read 16777216
    if chunk.isEmpty then break
    cur := chunk.copySlice 0 cur cur.size chunk.size
  assert! cur.size == total
  return cur

/-- Sequences of a read file (`>name`/seq or FASTQ), streamed in 16 MB chunks. -/
def readSeqs (path : String) : IO (Array ByteArray) := do
  let h ← IO.FS.Handle.mk path .read
  let mut out : Array ByteArray := #[]
  let mut line := ByteArray.empty
  let mut ln := 0
  let mut fq := false
  repeat
    let chunk ← h.read 16777216
    if chunk.isEmpty then break
    let mut i := 0
    while i < chunk.size do
      let mut j := i
      while j < chunk.size && chunk.get! j != 10 do j := j + 1
      line := chunk.copySlice i line line.size (j - i)
      if j < chunk.size then
        if ln == 0 then fq := line.get! 0 == 64  -- '@'
        if line.size > 0 then
          if (fq && ln % 4 == 1) || (!fq && ln % 2 == 1) then out := out.push line
          ln := ln + 1
        line := ByteArray.empty
      i := j + 1
  assert! line.size == 0
  return out

def wrU64s (path : String) (a : Array Nat) : IO Unit :=
  IO.FS.writeBinFile path ((Array.range a.size).foldl (fun b i => Mz.wrLE b (8 * i) a[i]!.toUInt64 8) (Mz.zeros (8 * a.size)))

def rdU64s (b : ByteArray) : Array Nat :=
  (Array.range (b.size / 8)).map fun i => ((Mz.rd4 b (8 * i)) ||| (Mz.rd4 b (8 * i + 4) <<< 32)).toNat

def save (pre : String) (ix : Mz.MzIdx) (pb : Nat) : IO Unit := do
  IO.FS.writeFile (pre ++ ".meta") s!"{ix.k} {ix.B} {ix.c} {ix.sw} {ix.t} {pb} {ix.runs.size}\n"
  IO.FS.writeBinFile (pre ++ ".offs") ix.offs
  IO.FS.writeBinFile (pre ++ ".sl") ix.sl
  wrU64s (pre ++ ".runs") ix.runs

def load (pre : String) : IO Mz.MzIdx := do
  let m := ((← IO.FS.readFile (pre ++ ".meta")).trim.splitOn " ").map String.toNat!
  let [k, B, c, sw, t, pb, nr] := m | throw (IO.userError "bad meta")
  let runs := rdU64s (← readBin (pre ++ ".runs"))
  assert! runs.size == nr
  return { Mz.mkIdx k B c sw pb t with offs := ← readBin (pre ++ ".offs"), sl := ← readBin (pre ++ ".sl"), runs }

def loadGenome (files : List String) : IO (Array ByteArray × Array Nat × GV) := do
  let t0 ← IO.monoNanosNow
  let mut gbs : Array ByteArray := #[]
  for f in files do gbs := gbs.push (← readChrom f)
  let offs := (gbs.foldl (fun (o, n) g => (o.push n, n + g.size)) ((#[] : Array Nat), 0)).1
  let V := GV.ofChroms gbs
  let t1 ← IO.monoNanosNow
  IO.println s!"genome: {gbs.size} chromosomes, {V.n} letters, load {secs t0 t1} s; {← rss}"
  let ok ← (← IO.mkRef (if t1 == 1 then false else catOkVPar V offs gbs)).get
  let t2 ← IO.monoNanosNow
  IO.println s!"catOkV: {ok} ({secs t1 t2} s)"
  assert! ok
  return (gbs, offs, V)

def showHit (h : Placement × Int) : String :=
  s!"{h.1.1.chr}\t{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

def main (args : List String) : IO UInt32 := do
  let k ← envN "WG_K" 22
  let B ← envN "WG_B" 26
  let c ← envN "WG_C" 0
  let sw ← envN "WG_W" 5
  let t ← envN "WG_T" 6
  match args with
  | mode :: pre :: files =>
    if mode == "build" || mode == "bytes" then
      let (gbs, _, V) ← loadGenome files
      let t0 ← IO.monoNanosNow
      let ix ← if mode == "build" then IO.mkRef (if t0 == 1 then default else Mz.buildWV V k B c sw t) >>= (·.get) else do
        let G := gbs.foldl (· ++ ·) (ByteArray.emptyWithCapacity V.n)
        IO.mkRef (if t0 == 1 then default else Mz.buildW G k B c sw t) >>= (·.get)
      IO.println s!"built: {ix.sl.size / sw} entries, sl {ix.sl.size} B, offs {ix.offs.size} B, runs {ix.runs.size}"
      let t1 ← IO.monoNanosNow
      IO.println s!"build {secs t0 t1} s ({Float.ofNat (ix.sl.size + ix.offs.size) / Float.ofNat V.n} B/letter); {← rss}"
      save pre ix (V.n.log2 + 1)
      IO.println s!"saved {pre}.*"
      return 0
    else if mode == "map" then
      let P ← envN "WG_P" 16
      let lo ← envN "WG_MIN" 100
      let hi ← envN "WG_MAX" 1000
      let taskL := ((← IO.getEnv "WG_TASKS").getD "1").splitOn "," |>.map String.toNat!
      let minLen ← envN "WG_MINLEN" (if P ≥ 16 then 150 else 100)
      let sets := ((← IO.getEnv "WG_READS").getD "").splitOn ";" |>.filter (· ≠ "")
      let (gbs, offs, V) ← loadGenome files
      let t0 ← IO.monoNanosNow
      let ix ← load pre
      let t1 ← IO.monoNanosNow
      IO.println s!"index loaded {secs t0 t1} s: {ix.sl.size / ix.sw} entries; {← rss}"
      let ok ← (← IO.mkRef (if t1 == 1 then false else Mz.check3V ix V 4)).get
      let t2 ← IO.monoNanosNow
      IO.println s!"index check (check3V = check2V, 4 tasks): {ok} ({secs t1 t2} s); {← rss}"
      assert! ok
      for st in sets do
        let [p1, p2, dump, lim] := st.splitOn ":" | throw (IO.userError "WG_READS: r1:r2:dump|-:limit|0;...")
        let r1 ← readSeqs p1
        let r2 ← readSeqs p2
        assert! r1.size == r2.size
        let n := if lim.toNat! == 0 then r1.size else min r1.size lim.toNat!
        let idx := (Array.range n).filter fun i => r1[i]!.size ≥ minLen && r2[i]!.size ≥ minLen
        IO.println s!"{p1}: pairs {n}, both mates >= {minLen}: {idx.size}; {← rss}"
        let f (i : Nat) := pairFastGB P lo hi (ix, V) ByteArray.empty offs gbs r1[i]! r2[i]!
        let mut first : Option (Array (Option ((Placement × Int) × (Placement × Int)))) := none
        for tasks in taskL do
          let t3 ← IO.monoNanosNow
          let out ← (← IO.mkRef (if t3 == 1 then #[] else if tasks ≤ 1 then idx.map f else ParMap.parMap tasks f idx)).get
          let t4 ← IO.monoNanosNow
          IO.println s!"T = -{P}, tasks {tasks}: mapped {idx.size} pairs, kept {(out.filter (·.isSome)).size}"
          IO.println s!"map_seconds: {secs t3 t4}  pairs/s: {Float.ofNat idx.size / secs t3 t4}; {← rss}"
          match first with
          | some o => assert! o == out
          | none =>
            first := some out
            if dump != "-" then
              IO.FS.writeFile dump (String.join ((idx.zip out).toList.map fun (i, x) => match x with
                | some (a, b) => s!"p{i + 1}\t{showHit a}\t{showHit b}\n"
                | none => s!"p{i + 1}\tnone\n"))
      return 0
    else throw (IO.userError "mode: build | bytes | map")
  | _ => throw (IO.userError "usage: whole_genome build|bytes|map <index_prefix> ...")
