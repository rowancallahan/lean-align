import MzView
import ParMap
import WgPacked
import ReadTrim

/-!
Benchmark only (unproved IO).  Whole genome with the genome held once
(codecs/MzView.lean: `buildWV_eq`, `check3V_eq`, `pairFastGB_view_eq_pairSpec`;
codecs/WgPacked.lean: `check3P_eq`, `pairDispatch_view_eq`, `pairDispatchP_mz_eq`,
`pairDispatchKP_mz_eq`, `pairFastGBKP_mz_eq_pairSpec`).

    lake exe whole_genome build <index_prefix> <chr.fa>...       build over the view, save
    lake exe whole_genome bytes <index_prefix> <chr.fa>...       same with `Mz.buildW` on the concatenation
    WG_READS='name=r1:r2:limit|0;…' WG_TASKS=1,4 WG_OUT=dir lake exe whole_genome map <index_prefix> <chr.fa>...
        byte chromosomes, genome held once as a view (mode B: pairDispatch_view_eq / pairFastGB_view_eq_pairSpec)
    … lake exe whole_genome pmap <index_prefix> <chr.fa>...
        genome packed while read (no byte genome), index checked on it (check3P_eq); WG_MODES=P,PK
        P: pairDispatchP / pairFastGBP; PK: word kernels pairDispatchKP / pairFastGBKP
    env: WG_K (22) WG_B (26) WG_C (0) WG_W (5) WG_T (6)  index; WG_P (0 = length dispatch: −16 from
         150 letters, −12 from 100, shorter pairs skipped; else one T = −P) WG_MIN (100) WG_MAX (1000)
         WG_TASKS (1), WG_OUT: dumps <dir>/<mode>_<name>.tsv (one line per pair: hits, or `none`),
         WG_PROF=1: per-read profile (lookups, hits, gapped stage) of mode PK on 1 thread
Chromosome files: one record each.  Mates: `>name` / sequence lines (no trimming), or FASTQ
(4-line records, empty reads kept; both mates trimmed by the proved `ReadTrim.trimRead`).
Index files: <prefix>.meta (k B c sw t pb nruns), .offs, .sl, .runs (LE u64).
-/
open MapSpec MapSpec.Fast

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def rss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  return " ".intercalate ((s.splitOn "\n").filter (fun l => l.startsWith "VmHWM" || l.startsWith "VmRSS")
    |>.map (fun l => l.replace "\t" "" |>.replace "  " ""))

/-- Print one line and flush (stdout to a pipe is block-buffered; a killed run kept nothing). -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

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
  say s!"genome: {gbs.size} chromosomes, {V.n} letters, load {secs t0 t1} s; {← rss}"
  let ok ← (← IO.mkRef (if t1 == 1 then false else catOkVPar V offs gbs)).get
  let t2 ← IO.monoNanosNow
  say s!"catOkV: {ok} ({secs t1 t2} s)"
  assert! ok
  return (gbs, offs, V)


def showHit (h : Placement × Int) : String :=
  s!"{h.1.1.chr}\t{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

/-- All lines of a file (a final line without newline included; empty lines kept). -/
def readLines (path : String) : IO (Array ByteArray) := do
  let b ← readBin path
  let mut out : Array ByteArray := Array.mkEmpty (b.size / 100)
  let mut i := 0
  let mut j := 0
  while j < b.size do
    if b.get! j == 10 then
      let e := if j > i && b.get! (j - 1) == 13 then j - 1 else j
      out := out.push (b.extract i e)
      i := j + 1
    j := j + 1
  if i < b.size then out := out.push (b.extract i b.size)
  return out

/-- Mates of a file: FASTQ (4-line records, trimmed by `ReadTrim.trimRead`; `none` =
trimmed away) or `>name`/sequence pairs of lines (untrimmed). -/
def readMates (path : String) : IO (Array (Option ByteArray)) := do
  let ls ← readLines path
  if ls.size == 0 then return #[]
  if ls[0]!.get! 0 == 64 then
    if ls.size % 4 != 0 then throw (IO.userError s!"{path}: {ls.size} lines, not 4 per record")
    return (Array.range (ls.size / 4)).map fun r =>
      let s := ls[4 * r + 1]!
      let q := ls[4 * r + 3]!
      if s.size != q.size then none else
      match ReadTrim.trimRead s q with
      | some (b, e) => some (s.extract b e)
      | none => none
  else
    if ls.size % 2 != 0 then throw (IO.userError s!"{path}: odd number of lines")
    return (Array.range (ls.size / 2)).map fun r => some ls[2 * r + 1]!

abbrev PairOut := Option ((Placement × Int) × (Placement × Int))

/-- Prototype (profile only): anchors held by a strand. -/
def gsAnchors (s : GS) : Nat := s.acc.foldl (fun a l => a + l.foldl (fun a2 arr => a2 + arr.size) 0) 0

/-- Prototype (profile only): live with `X` extra lookups once a strand holds `A` anchors. -/
def liveX (A X P : Nat) (s : GS) (b : Best) : Bool :=
  !s.ord.isEmpty && (!decide (sbound (min b.pen P) < s.J.length) ||
    (decide (s.J.length < sbound (min b.pen P) + 1 + X) && decide (A ≤ gsAnchors s)))

/-- Prototype: seed `R[s, s+25)` matches `G` at `p`. -/
def matchQx {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (s p : Nat) : Bool :=
  p + 25 ≤ GRead.size G && go 0 25
where go (k : Nat) : Nat → Bool
  | 0 => true
  | f + 1 => GRead.get G (p + k) == R.get! (s + k) && go (k + 1) f

/-- Prototype: some `p ∈ [lo, lo + w)` matches. -/
def nearX {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (s lo : Nat) : Nat → Bool
  | 0 => false
  | w + 1 => matchQx R G s lo || nearX R G s (lo + 1) w

/-- Prototype: at least `need` of the `m` seeds match within `r` of diagonal `D`
(early exits both ways). -/
def dOkX {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (m Ls need r D : Nat) : Bool :=
  go 0 0 0 m
where go (j pass fail : Nat) : Nat → Bool
  | 0 => need ≤ pass
  | f + 1 =>
    if need ≤ pass then true else if m < need + fail then false else
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else nearX R G (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1)
    if ok then go (j + 1) (pass + 1) fail f else go (j + 1) pass (fail + 1) f

/-- Prototype: seeds `us` (not looked up) checked directly; reject once more than `sb` fail. -/
def unlookX {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (Ls r D sb : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j :: us, fail =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else nearX R G (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1)
    if ok then unlookX R G Ls r D sb us fail
    else if sb < fail + 1 then false else unlookX R G Ls r D sb us (fail + 1)

def chromKBX (kf : Ker) (R : ByteArray) (gbs : Array PGen) (c P : Nat) (acc : List (Array Nat)) (J : List Nat) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let m := R.size / 25
  let Ls := R.size / m
  let G := gbs[c]!
  let us := (List.range m).filter (fun j => !J.contains j)
  let r := 2 * gapBound sc0 (-(Q1 : Int))
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      (diags acc).foldl (fun b D =>
        let Q := min lim b.pen
        let rq := 2 * gapBound sc0 (-(Q : Int))
        let fJ := acc.length - suppA acc D rq
        if fJ ≤ sbound Q && unlookX R G Ls rq D (sbound Q) us fJ then
          (shapesKT Q1).foldl (fun b sh => addKF kf c lim (dst R.size D sh) (wlen R.size sh) b) b
        else b) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int))))
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

def ilX {L Pp : Type} [LookG L Pp] [Inhabited Pp] (A X : Nat) (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array PGen) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := liveX A X P s2 b
    if liveX A X P s1 b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advFG kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilX A X kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advFG kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilX A X kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- Per-read profile of the packed word-kernel mapper (bench only: the proved
functions' parts called one by one and timed). -/
structure Prof where
  reads : Nat := 0
  lookups : Nat := 0
  hits : Nat := 0
  bucket : Nat := 0
  bigHits : Nat := 0
  bigLookups : Nat := 0
  prepNs : Nat := 0
  p1Ns : Nat := 0
  kbNs : Nat := 0
  slowReads : Nat := 0
  slowNs : Nat := 0
  slowHits : Nat := 0
  slowLookups : Nat := 0
  slowP1 : Nat := 0
  slowAmb : Nat := 0
  slowAmb0 : Nat := 0
  slowNone : Nat := 0
  slowDiags : Nat := 0
  slowPass : Nat := 0
  slowFiltNs : Nat := 0
  penHist : Array Nat := Array.replicate 18 0
  lkHist : Array Nat := Array.replicate 25 0

def profRead (XA XN : Nat) (XF : Bool) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (P : Nat) (R : ByteArray) (pf : Prof) :
    IO Prof := do
  let n := pgs.size
  let gbs2 := pgs ++ pgs
  let t0 ← IO.monoNanosNow
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  let ps := prepGK ix R K1 m Ls
  let pr := prepGK ix Rr K2 m Ls
  let kf1 := kerHKG R K1 gbs2 gbs2
  let kf2 := kerHKG Rr K2 gbs2 gbs2
  let o1 := ordG (ps.map (LookG.size ix)) m
  let o2 := ordG (pr.map (LookG.size ix)) m
  let o1 ← (← IO.mkRef o1).get
  let o2 ← (← IO.mkRef o2).get
  let t1 ← IO.monoNanosNow
  let x ← (← IO.mkRef (if t1 == 0 then (default, default, initP P) else if XN == 0 then
    ilGFG kf1 kf2 ix ByteArray.empty R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
      ⟨o1, [], Array.replicate n []⟩ ⟨o2, [], Array.replicate n []⟩ (initP P)
    else ilX XA XN kf1 kf2 ix ByteArray.empty R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
      ⟨o1, [], Array.replicate n []⟩ ⟨o2, [], Array.replicate n []⟩ (initP P))).get
  let t2 ← IO.monoNanosNow
  let b := (List.range n).foldl (fun b c => if XF then chromKBX kf1 R gbs2 c P x.1.acc[c]! x.1.J b
    else chromKBFG kf1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2
  let b := (List.range n).foldl (fun b c => if XF then chromKBX kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b
    else chromKBFG kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b) b
  let b ← (← IO.mkRef b).get
  let t3 ← IO.monoNanosNow
  let lk := x.1.J.length + x.2.1.J.length
  let hits := (x.1.acc.toList ++ x.2.1.acc.toList).foldl (fun a l => a + l.foldl (fun a2 arr => a2 + arr.size) 0) 0
  let szs := (x.1.J.map fun j => LookG.size ix ps[j]!) ++ (x.2.1.J.map fun j => LookG.size ix pr[j]!)
  let bk := szs.foldl (· + ·) 0
  let big := szs.filter (· > 1000)
  let slow := t3 - t1 > 1000000
  let bigSum := big.foldl (fun a v => a + v) 0
  let pf := { pf with reads := pf.reads + 1, lookups := pf.lookups + lk }
  let pf := { pf with hits := pf.hits + hits, bucket := pf.bucket + bk }
  let pf := { pf with bigLookups := pf.bigLookups + big.length, bigHits := pf.bigHits + bigSum }
  let pf := { pf with prepNs := pf.prepNs + (t1 - t0), p1Ns := pf.p1Ns + (t2 - t1), kbNs := pf.kbNs + (t3 - t2) }
  let pf := if slow then { pf with slowReads := pf.slowReads + 1, slowNs := pf.slowNs + (t3 - t1) } else pf
  let pf := if slow then { pf with slowHits := pf.slowHits + hits, slowLookups := pf.slowLookups + lk } else pf
  let a1 : Nat := if b.amb && decide (b.pen ≤ P) then 1 else 0
  let a0 : Nat := if b.amb && b.pen == 0 then 1 else 0
  let a2 : Nat := if decide (b.pen > P) then 1 else 0
  let pf := if slow then { pf with slowP1 := pf.slowP1 + (t2 - t1), slowAmb := pf.slowAmb + a1 } else pf
  let pf := if slow then { pf with slowAmb0 := pf.slowAmb0 + a0, slowNone := pf.slowNone + a2 } else pf
  let pf ← if slow then do
      let fl := fun (Rx : ByteArray) (t : Nat) (s : GS) =>
        (List.range n).foldl (fun (a : Nat × Nat) c =>
          let acc := s.acc[c]!
          let ds := diags acc
          let us := unseen (Rx.size / 25) s.J
          (a.1 + ds.length, a.2 + (ds.filter fun D => kfilt Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D).length)) (0, 0)
      let u0 ← IO.monoNanosNow
      let r1 ← (← IO.mkRef (fl R 0 x.1)).get
      let r2 ← (← IO.mkRef (fl Rr n x.2.1)).get
      let u1 ← IO.monoNanosNow
      let pf := { pf with slowDiags := pf.slowDiags + r1.1 + r2.1, slowPass := pf.slowPass + r1.2 + r2.2 }
      pure { pf with slowFiltNs := pf.slowFiltNs + (u1 - u0) }
    else pure pf
  let pf := { pf with penHist := pf.penHist.modify (min b.pen 17) (fun v => v + 1) }
  return { pf with lkHist := pf.lkHist.modify (min lk 24) (fun v => v + 1) }

def showProf (pf : Prof) : IO Unit := do
  let r := Float.ofNat (max pf.reads 1)
  say s!"profile: {pf.reads} reads; per read: lookups {Float.ofNat pf.lookups / r}, anchors {Float.ofNat pf.hits / r}, bucket entries scanned {Float.ofNat pf.bucket / r}"
  say s!"  lookups of buckets > 1000 entries: {pf.bigLookups} ({Float.ofNat pf.bigHits / Float.ofNat (max pf.bigLookups 1)} entries avg)"
  say s!"  time per read: prep {Float.ofNat pf.prepNs / r / 1000} us, lookups + phase 1 {Float.ofNat pf.p1Ns / r / 1000} us, stages K/B {Float.ofNat pf.kbNs / r / 1000} us"
  say s!"  reads > 1 ms: {pf.slowReads} taking {secs 0 pf.slowNs} s of {secs 0 (pf.p1Ns + pf.kbNs)} s; their lookups {Float.ofNat pf.slowLookups / Float.ofNat (max pf.slowReads 1)}, anchors {Float.ofNat pf.slowHits / Float.ofNat (max pf.slowReads 1)} per read"
  say s!"  reads > 1 ms: phase 1 {secs 0 pf.slowP1} s; ambiguous {pf.slowAmb} (at 0: {pf.slowAmb0}), none {pf.slowNone}"
  say s!"  reads > 1 ms: diagonals {pf.slowDiags}, passing the filter at the final best {pf.slowPass}; filter alone {secs 0 pf.slowFiltNs} s"
  say s!"  best penalty histogram (0..16, 17 = none): {pf.penHist}"
  say s!"  lookups per read histogram (0..23, 24+): {pf.lkHist}"

/-- Map every read set with each mode and task count; dumps and timings. -/
def runSets (modes : List (String × (ByteArray → ByteArray → PairOut))) (okLen : ByteArray → Bool)
    (prof : List (String × (ByteArray → Prof → IO Prof))) : IO Unit := do
  let taskL := ((← IO.getEnv "WG_TASKS").getD "1").splitOn "," |>.map String.toNat!
  let sets := ((← IO.getEnv "WG_READS").getD "").splitOn ";" |>.filter (· ≠ "")
  let outDir := (← IO.getEnv "WG_OUT").getD ""
  for st in sets do
    let [name, rest] := st.splitOn "=" | throw (IO.userError "WG_READS: name=r1:r2:limit;...")
    let [p1, p2, lim] := rest.splitOn ":" | throw (IO.userError "WG_READS: name=r1:r2:limit;...")
    let m1 ← readMates p1
    let m2 ← readMates p2
    if m1.size != m2.size then throw (IO.userError s!"{p1}: {m1.size} records, {p2}: {m2.size}")
    let n := if lim.toNat! == 0 then m1.size else min m1.size lim.toNat!
    let trimmed := (Array.range n).filter fun i => m1[i]!.isNone || m2[i]!.isNone
    let idx := (Array.range n).filter fun i => match m1[i]!, m2[i]! with
      | some a, some b => okLen a && okLen b
      | _, _ => false
    let r1 := idx.map fun i => m1[i]!.get!
    let r2 := idx.map fun i => m2[i]!.get!
    let rk := Array.range idx.size
    say s!"set {name}: pairs {n}, trimmed away {trimmed.size}, both mates taken by the mapper {idx.size}; {← rss}"
    let plim ← envN "WG_PROF_LIM" rk.size
    for (lab, pr) in prof do
      let mut pf : Prof := {}
      for k in rk.extract 0 plim do
        pf ← pr r1[k]! pf
        pf ← pr r2[k]! pf
      say s!"profile {lab}"
      showProf pf
    for (mode, f) in modes do
      let g (k : Nat) : PairOut := f r1[k]! r2[k]!
      let mut first : Option (Array PairOut) := none
      for tasks in taskL do
        let t3 ← IO.monoNanosNow
        let out ← (← IO.mkRef (if t3 == 1 then #[] else if tasks ≤ 1 then rk.map g else ParMap.parMap tasks g rk)).get
        let t4 ← IO.monoNanosNow
        say s!"RESULT set {name} mode {mode} tasks {tasks}: mapped {idx.size} pairs, kept {(out.filter (·.isSome)).size}, {secs t3 t4} s, pairs/s {Float.ofNat idx.size / secs t3 t4}; {← rss}"
        match first with
        | some o => if o != out then say s!"MISMATCH between task counts ({mode})"
        | none =>
          first := some out
          if outDir != "" then
            let mut res : Array String := Array.replicate n "none\tshort\n"
            for i in trimmed do res := res.set! i "none\ttrimmed\n"
            for (i, x) in idx.zip out do
              res := res.set! i (match x with
                | some (a, b) => s!"{showHit a}\t{showHit b}\n"
                | none => "none\n")
            let path := s!"{outDir}/{mode}_{name}.tsv"
            let txt := String.join ((Array.range n).toList.map fun i => s!"p{i + 1}\t{res[i]!}")
            if ← System.FilePath.pathExists path then
              -- an earlier dump is kept, never overwritten: compare
              let old ← IO.FS.readFile path
              say s!"dump {path} kept; this run {if old == txt then "SAME" else "DIFFERENT"}"
            else
              IO.FS.writeFile path txt
              say s!"dump {path}"

/-- All chromosomes packed into one genome as they are read; offsets and lengths. -/
def loadPacked (files : List String) : IO (PGen × Array Nat × Array Nat) := do
  let t0 ← IO.monoNanosNow
  let mut total := 0
  for f in files do total := total + (← System.FilePath.metadata f).byteSize.toNat
  let mut s := PB.init total
  let mut offs : Array Nat := #[]
  for f in files do
    offs := offs.push s.n
    let h ← IO.FS.Handle.mk f .read
    let mut header := true
    repeat
      let chunk ← h.read 16777216
      if chunk.isEmpty then break
      for b in chunk do
        if header then
          if b == 10 then header := false
        else if b != 10 && b != 13 then
          s := s.push b
  let G := s.finish
  let ns := (Array.range offs.size).map fun c => (offs[c + 1]?.getD G.n) - offs[c]!
  let t1 ← IO.monoNanosNow
  say s!"genome packed: {ns.size} chromosomes, {G.n} letters, {G.w.size + 4 * G.ex.size} bytes ({secs t0 t1} s); {← rss}"
  return (G, offs, ns)

def main (args : List String) : IO UInt32 := do
  let k ← envN "WG_K" 22
  let B ← envN "WG_B" 26
  let c ← envN "WG_C" 0
  let sw ← envN "WG_W" 5
  let t ← envN "WG_T" 6
  let P ← envN "WG_P" 0
  let lo ← envN "WG_MIN" 100
  let hi ← envN "WG_MAX" 1000
  let okLen : ByteArray → Bool := if P == 0 then dispatchOk else fastT P
  match args with
  | mode :: pre :: files =>
    if mode == "build" || mode == "bytes" then
      let (gbs, _, V) ← loadGenome files
      let t0 ← IO.monoNanosNow
      let ix ← if mode == "build" then IO.mkRef (if t0 == 1 then default else Mz.buildWV V k B c sw t) >>= (·.get) else do
        let G := gbs.foldl (· ++ ·) (ByteArray.emptyWithCapacity V.n)
        IO.mkRef (if t0 == 1 then default else Mz.buildW G k B c sw t) >>= (·.get)
      say s!"built: {ix.sl.size / sw} entries, sl {ix.sl.size} B, offs {ix.offs.size} B, runs {ix.runs.size}"
      let t1 ← IO.monoNanosNow
      say s!"build {secs t0 t1} s ({Float.ofNat (ix.sl.size + ix.offs.size) / Float.ofNat V.n} B/letter); {← rss}"
      save pre ix (V.n.log2 + 1)
      say s!"saved {pre}.*"
      return 0
    else if mode == "map" then
      let (gbs, offs, V) ← loadGenome files
      let t0 ← IO.monoNanosNow
      let ix ← load pre
      let t1 ← IO.monoNanosNow
      say s!"index loaded {secs t0 t1} s: {ix.sl.size / ix.sw} entries; {← rss}"
      let ok ← (← IO.mkRef (if t1 == 1 then false else Mz.check3V ix V 4)).get
      let t2 ← IO.monoNanosNow
      say s!"index check (check3V = check2V, 4 tasks): {ok} ({secs t1 t2} s); {← rss}"
      if !ok then throw (IO.userError "index check failed")
      -- pairDispatch_view_eq / pairFastGB_view_eq_pairSpec
      let f : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatch lo hi (ix, V) ByteArray.empty offs gbs
        else pairFastGB P lo hi (ix, V) ByteArray.empty offs gbs
      runSets [("B", f)] okLen []
      return 0
    else if mode == "pmap" then
      let (G, offs, ns) ← loadPacked files
      if !cutOk G offs ns then throw (IO.userError "cutOk failed")
      let pgs := cutAll G offs ns
      let t0 ← IO.monoNanosNow
      let ix ← load pre
      let t1 ← IO.monoNanosNow
      say s!"index loaded {secs t0 t1} s: {ix.sl.size / ix.sw} entries; {← rss}"
      if (← IO.getEnv "WG_NOCHECK").isSome then
        say "WARNING: index check skipped (WG_NOCHECK): profiling only, not the proved setting"
      else
        let ok ← (← IO.mkRef (if t1 == 1 then false else Mz.check3P ix G 4)).get
        let t2 ← IO.monoNanosNow
        say s!"index check (check3P = check2P, 4 tasks): {ok} ({secs t1 t2} s); {← rss}"
        if !ok then throw (IO.userError "index check failed")
      let pk : PkMz := (ix, G)
      -- pairDispatchP_mz_eq / pairFastGBP_mz_eq_pairSpec; pairDispatchKP_mz_eq / pairFastGBKP_mz_eq_pairSpec
      let fP : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchP lo hi pk offs pgs
        else pairFastGBP P lo hi pk offs pgs
      let fK : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchKP lo hi pk ByteArray.empty offs pgs
        else pairFastGBKP P lo hi pk ByteArray.empty offs pgs
      let ms := ((← IO.getEnv "WG_MODES").getD "P,PK").splitOn ","
      let modes := ms.filterMap fun m => if m == "P" then some ("P", fP) else if m == "PK" then some ("PK", fK) else none
      -- WG_PROF=A:X,A:X,…: profile with X extra lookups once a strand holds A anchors (0:0 = as proved)
      let cfgs := ((← IO.getEnv "WG_PROF").getD "").splitOn "," |>.filter (· ≠ "")
      let prof : List (String × (ByteArray → Prof → IO Prof)) := cfgs.map fun (cf : String) =>
        let ax := cf.splitOn ":"
        let XA := ax[0]!.toNat!
        let XN := (ax[1]?.getD "0").toNat!
        let XF := (ax[2]?.getD "0") == "1"
        (cf, fun (R : ByteArray) (pf : Prof) => profRead XA XN XF pk offs pgs (if P == 0 then penOf R else P) R pf)
      runSets modes okLen prof
      return 0
    else throw (IO.userError "mode: build | bytes | map | pmap")
  | _ => throw (IO.userError "usage: whole_genome build|bytes|map|pmap <index_prefix> ...")
