import FastGenPairPacked
import FastGenPair

/-!
Seeding lab (benchmark only, unproved IO): cost of seed lookups on the whole genome.

    lake exe seed_lab <index_prefix> <genome_prefix> <r1.fq> <r2.fq>

Index: bench/WholeGenome.lean format (<prefix>.meta .offs .sl .runs).  Genome: the packed
files written by bench/pack_genome.py (<prefix>.pgw .pgx .pgn), loaded as one `PGen`; a
sample of index buckets is checked against it with the proved checker's `entryOkP`
(not the full check: that is the 16-minute run).
env: SL_N pairs (2000), SL_TASKS (1,4), SL_K seeds per strand (0 = s+1 by length:
5 from 150 letters, 4 from 100), SL_ALL=1 also every seed.
-/
open MapSpec MapSpec.Fast

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  return " ".intercalate ((s.splitOn "\n").filter (fun l => l.startsWith "VmHWM" || l.startsWith "VmRSS")
    |>.map (fun l => l.replace "\t" "" |>.replace "  " ""))

def envN (k : String) (d : Nat) : IO Nat := do return ((← IO.getEnv k).map String.toNat!).getD d

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

def rdU64s (b : ByteArray) : Array Nat :=
  (Array.range (b.size / 8)).map fun i => ((Mz.rd4 b (8 * i)) ||| (Mz.rd4 b (8 * i + 4) <<< 32)).toNat

def loadIdx (pre : String) : IO Mz.MzIdx := do
  let m := ((← IO.FS.readFile (pre ++ ".meta")).trim.splitOn " ").map String.toNat!
  let [k, B, c, sw, t, pb, nr] := m | throw (IO.userError "bad meta")
  let runs := rdU64s (← readBin (pre ++ ".runs"))
  assert! runs.size == nr
  return { Mz.mkIdx k B c sw pb t with offs := ← readBin (pre ++ ".offs"), sl := ← readBin (pre ++ ".sl"), runs }

def loadPG (pre : String) : IO PGen := do
  let n := (← IO.FS.readFile (pre ++ ".pgn")).trim.toNat!
  return ⟨n, 0, ← readBin (pre ++ ".pgw"), ← readBin (pre ++ ".pgx")⟩

/-- Sequences of a FASTQ file. -/
def readFq (path : String) (lim : Nat) : IO (Array ByteArray) := do
  let b ← readBin path
  let mut out : Array ByteArray := #[]
  let mut i := 0
  let mut ln := 0
  let mut j := 0
  while j < b.size && out.size < lim do
    if b.get! j == 10 then
      if ln % 4 == 1 then out := out.push (b.extract i j)
      ln := ln + 1
      i := j + 1
    j := j + 1
  return out

/-! ## Prototype: lookups with a direct (non-generic) genome compare and borrowed arguments -/

def eqRunF (a : @& PGen) (b : @& ByteArray) (i j : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => a.get i == b.get! j && eqRunF a b (i + 1) (j + 1) k

@[inline] def okAtF (ix : @& Mz.MzIdx) (G : @& PGen) (R : @& ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) : Bool :=
  let e := (ix.slot t)
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     let tg := ix.tagOf e
     decide (o ≤ pos) &&
      (if ix.flagF tg = 0 then (ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw &&
         decide (pos - o + Mz.q ≤ G.n) && eqRunF G R (pos - o) s n1 &&
         eqRunF G R (pos + a2) (s + o + a2) n2 &&
         (ix.kf == ix.kb || eqRunF G R pos (s + o) ix.k)
       else decide (pos - o + Mz.q ≤ G.n) && eqRunF G R (pos - o) s Mz.q))

def scanF (ix : @& Mz.MzIdx) (G : @& PGen) (R : @& ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanF ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if okAtF ix G R s o key bw aw pmo o2 n1 a2 n2 t then acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

def lookF (ix : @& Mz.MzIdx) (G : @& PGen) (R : @& ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanF ix G R s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base bit (ix.loB p.b) #[]

def lookSF (ix : @& PkMz) (R : @& ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookF ix.1 ix.2 R s p base 0 else mzLookSP ix.1 ix.2 R s base p

/-- Seeds per strand a cap-exact search needs at worst (s + 1). -/
def needK (n K : Nat) : Nat := if K != 0 then K else if 150 ≤ n then 5 else 4

/-- One strand: look up the `k` seeds with the smallest buckets; (anchors, bucket entries). -/
def strandCost (F : Bool) (ix : PkMz) (R : ByteArray) (k : Nat) : Nat × Nat :=
  let m := R.size / 25
  let Ls := R.size / m
  let ps := prepG ix R m Ls
  let ord := ((Array.range m).qsort fun a b => LookG.size ix ps[a]! < LookG.size ix ps[b]!).toList.take k
  ord.foldl (fun (a, e) j =>
    let p := ps[j]!
    let r := if F then lookSF ix R (j * Ls) 0 p else LookG.look ix ByteArray.empty R (j * Ls) 0 p
    (a + r.size, e + LookG.size ix p)) (0, 0)

def mateCost (F : Bool) (ix : PkMz) (K : Nat) (R : ByteArray) : Nat × Nat :=
  if R.size < 100 then (0, 0) else
  let k := needK R.size K
  let (a1, e1) := strandCost F ix R k
  let (a2, e2) := strandCost F ix (revCompB2 R) k
  (a1 + a2, e1 + e2)

def runChunk (F : Bool) (ix : PkMz) (K : Nat) (ms : Array ByteArray) (lo hi : Nat) : Nat × Nat := Id.run do
  let mut a := 0
  let mut e := 0
  for i in [lo:hi] do
    let (x, y) := mateCost F ix K ms[i]!
    a := a + x; e := e + y
  return (a, e)

def main (args : List String) : IO Unit := do
  let [ipre, gpre, f1, f2] := args | throw (IO.userError "usage: seed_lab <index> <genome> <r1.fq> <r2.fq>")
  let N ← envN "SL_N" 2000
  let t0 ← IO.monoNanosNow
  let ix ← loadIdx ipre
  let G ← loadPG gpre
  let t1 ← IO.monoNanosNow
  say s!"loaded {secs t0 t1} s: {ix.sl.size / ix.sw} entries, {G.n} letters; {← rss}"
  -- sample check: random buckets' entries against the packed genome
  let mut bad := 0
  let mut seen := 0
  let mut x : Nat := 12345
  for _ in [0:2000] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2^64
    let b := (x >>> 20) % 2 ^ ix.B
    for t in [ix.loB b:ix.hiB b] do
      seen := seen + 1
      if !Mz.entryOkP ix G b (ix.hiB b) t then bad := bad + 1
  say s!"sample check: {seen} entries, {bad} bad"
  let r1 ← readFq f1 N
  let r2 ← readFq f2 N
  let ms := (Array.range r1.size).foldl (fun acc i => (acc.push r1[i]!).push r2[i]!) #[]
  let K ← envN "SL_K" 0
  let ixp : PkMz := (ix, G)
  let tasksS := (← IO.getEnv "SL_TASKS").getD "1,4"
  -- the prototype lookup gives the same anchors
  let mut diff := 0
  for R in ms.extract 0 400 do
    if R.size ≥ 100 then
      let m := R.size / 25
      let Ls := R.size / m
      for j in [0:m] do
        let p := LookG.prep ixp (seedHashAt R (j * Ls))
        if lookSF ixp R (j * Ls) 0 p != LookG.look ixp ByteArray.empty R (j * Ls) 0 p then diff := diff + 1
  say s!"prototype lookups differing: {diff}"
  for (T, F) in ((tasksS.splitOn ",").map String.toNat!).flatMap (fun T => [(T, false), (T, true)]) do
    let ta ← IO.monoNanosNow
    let n := ms.size
    let mut ts := #[]
    for c in [0:T] do
      -- `.dedicated`: on this box default-priority tasks (IO.asTask / Task.spawn) run one at a time
      ts := ts.push (← IO.asTask (prio := .dedicated) (do
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure fun _ => runChunk F ixp K ms (c * n / T) ((c + 1) * n / T)
        let t1 ← IO.monoNanosNow
        return (r, secs t0 t1)))
    let mut rs := []
    let mut times := #[]
    for t in ts do
      match ← IO.wait t with
      | .ok (r, dt) => rs := r :: rs; times := times.push dt
      | .error e => throw e
    say s!"  chunk seconds {times}"
    let (a, e) := rs.foldl (fun (a, e) (x, y) => (a + x, e + y)) (0, 0)
    let tb ← IO.monoNanosNow
    say s!"tasks {T} K {K} {if F then "fast" else "mzLookSP"}: {n} mates, {secs ta tb} s, {Float.ofNat (tb - ta) / 1e3 / Float.ofNat n * Float.ofNat T} us/mate/thread; anchors/mate {Float.ofNat a / Float.ofNat n}, bucket entries/mate {Float.ofNat e / Float.ofNat n}"
  say s!"{← rss}"
