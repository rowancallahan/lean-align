import MzView
import ParMap
import WgPacked
import PairRegion
import ReadTrim
import PairRouter
import PairNear
import AlignmentCigarCheck

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
        packed genome loaded from <prefix>.pgw/.pgx/.pgc (hash-checked; WG_FASTA=1 or no .pgc: packed
        while the FASTA is read; no byte genome), index checked on it (check3P_eq); WG_MODES=P,PK
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

/-- 64-bit FNV-style hash of bytes `[lo, hi)` (trusted IO: ties a loaded index to the checked one). -/
def hashRange (b : ByteArray) (lo hi : Nat) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for i in [lo:hi] do
    h := (h ^^^ (b.get! i).toUInt64) * 0x100000001b3
  return h

/-- `hashRange` over 64 MB chunks on parallel tasks, combined in order with the size. -/
def hashBytes (b : ByteArray) : UInt64 :=
  let ch := 67108864
  let n := (b.size + ch - 1) / ch
  let ts := (List.range n).map fun i => Task.spawn (prio := .dedicated) fun _ => hashRange b (i * ch) (min b.size ((i + 1) * ch))
  ts.foldl (fun h t => (h ^^^ t.get) * 0x100000001b3 + 0x9e3779b97f4a7c15) b.size.toUInt64

def envN (k : String) (d : Nat) : IO Nat := do return ((← IO.getEnv k).map String.toNat!).getD d

/-- Process CPU time (user + system, clock ticks of 10 ms) and the machine's steal ticks. -/
def cpuTicks : IO (Nat × Nat) := do
  let s ← IO.FS.readFile "/proc/self/stat"
  let rest := (s.splitOn ") ").getLast!
  let fs := rest.splitOn " "
  let st ← IO.FS.readFile "/proc/stat"
  let cpu := ((st.splitOn "\n").head!.splitOn " ").filter (· ≠ "")
  return (fs[11]!.toNat! + fs[12]!.toNat!, cpu[8]!.toNat!)

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


/-! ## Tiered certificate check (bench only, unproved heuristic search; each reported over-cap
alignment is re-scored by the proved checker `AlignmentSpec.checkRuns`) -/

/-- Semi-global affine DP of the whole read `R` in the window `[ws, we)` of `G` (free ends in the
genome), sc0 penalties (mismatch 4, gap 6 + 2L): start, length, penalty and the runs, or `none`. -/
def semiDP (R : ByteArray) (G : PGen) (ws we : Nat) : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := Id.run do
  let n := R.size
  let we := min we G.n
  if we ≤ ws || n == 0 then return none
  let cols := we - ws + 1
  let INF : Nat := 1000000
  let mut H : Array Nat := Array.replicate ((n + 1) * cols) 0
  let mut E : Array Nat := Array.replicate ((n + 1) * cols) INF
  let mut F : Array Nat := Array.replicate ((n + 1) * cols) INF
  for i in [1:n + 1] do
    let ri := R.get! (i - 1)
    let k0 := i * cols
    let f0 := min (H[k0 - cols]! + 8) (F[k0 - cols]! + 2)
    F := F.set! k0 f0
    H := H.set! k0 f0
    for j in [1:cols] do
      let k := k0 + j
      let e := min (H[k - 1]! + 8) (E[k - 1]! + 2)
      let f := min (H[k - cols]! + 8) (F[k - cols]! + 2)
      let d := H[k - cols - 1]! + (if ri == G.get (ws + j - 1) then 0 else 4)
      E := E.set! k e
      F := F.set! k f
      H := H.set! k (min d (min e f))
  -- best end
  let mut bj := 0
  let mut bv := INF
  for j in [0:cols] do
    let v := H[n * cols + j]!
    if v < bv then
      bv := v
      bj := j
  -- traceback (0 = H, 1 = E, 2 = F)
  let mut i := n
  let mut j := bj
  let mut st : Nat := 0
  let mut steps : List AlignmentSpec.Step := []
  let mut fuel := 4 * (n + cols) + 8
  while i > 0 && fuel > 0 do
    fuel := fuel - 1
    let k := i * cols + j
    if st == 0 then
      if j > 0 && H[k]! == H[k - cols - 1]! + (if R.get! (i - 1) == G.get (ws + j - 1) then 0 else 4) then
        steps := .diag :: steps
        i := i - 1
        j := j - 1
      else if j > 0 && H[k]! == E[k]! then st := 1
      else st := 2
    else if st == 1 then
      steps := .gapX :: steps
      let ext := j > 1 && E[k]! == E[k - 1]! + 2
      j := j - 1
      if !ext then st := 0
    else
      steps := .gapY :: steps
      let ext := i > 1 && F[k]! == F[k - cols]! + 2
      i := i - 1
      if !ext then st := 0
  if i > 0 then return none
  let runs := steps.foldr (fun s acc => match acc with
    | (t, c) :: rest => if s == t then (t, c + 1) :: rest else (s, 1) :: acc
    | [] => [(s, 1)]) []
  return some (ws + j, bj - j, bv, runs)

/-- The proved checker on the runs: the read against the genome window. -/
def rescoreRuns (R : ByteArray) (G : PGen) (st len : Nat) (runs : List (AlignmentSpec.Step × Nat)) : Option Int :=
  let xa : Array Char := (List.range R.size).toArray.map fun i => Char.ofNat (R.get! i).toNat
  let ya : Array Char := (List.range len).toArray.map fun i => Char.ofNat (G.get (st + i)).toNat
  AlignmentSpec.checkRuns sc0 xa ya runs ⟨0, 0, none, 0⟩

@[inline] def baseCode (b : UInt8) : Nat :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

/-- k-mers (code, offset) of `len` letters from `get`, skipping non-ACGT. -/
def kmersOf (get : Nat → UInt8) (len k : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut h := 0
  let mut v := 0
  let msk := 4 ^ k
  for i in [0:len] do
    let c := baseCode (get i)
    if c == 4 then
      v := 0
      h := 0
    else
      h := (h * 4 + c) % msk
      v := v + 1
      if v ≥ k then out := out.push (h, i + 1 - k)
  return out

/-- Clusters of sorted diagonals (gap ≤ g): (support, lowest, highest), most support first. -/
def clusterD (ds : Array Nat) (g top : Nat) : List (Nat × Nat × Nat) := Id.run do
  let ds := ds.qsort (· < ·)
  let mut cl : Array (Nat × Nat × Nat) := #[]
  for d in ds do
    match cl.back? with
    | some (c, lo, hi) => if d ≤ hi + g then cl := cl.pop.push (c + 1, lo, d) else cl := cl.push (1, d, d)
    | none => cl := cl.push (1, d, d)
  return ((cl.qsort fun a b => a.1 > b.1).toList.take top)

/-- Best semi-global hit of `R` in `[x0, x1)` of `G`, diagonals chosen by shared k-mers
(top `top` clusters), each searched in a window `g` wider. -/
def regionX (R : ByteArray) (G : PGen) (x0 x1 k g top : Nat) : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) :=
  let x1 := min x1 G.n
  if x1 ≤ x0 then none else
  let n := R.size
  let rk := (kmersOf (fun i => R.get! i) n k).qsort (fun a b => a.1 < b.1)
  let gk := (kmersOf (fun i => G.get (x0 + i)) (x1 - x0) k).qsort (fun a b => a.1 < b.1)
  -- merge join on the code: diagonal = read end on the genome
  let ds := Id.run do
    let mut out : Array Nat := #[]
    let mut a := 0
    let mut b := 0
    while a < rk.size && b < gk.size && out.size < 20000 do
      let (ca, qa) := rk[a]!
      let (cb, _) := gk[b]!
      if ca < cb then a := a + 1
      else if cb < ca then b := b + 1
      else
        let mut b2 := b
        while b2 < gk.size && gk[b2]!.1 == ca do
          out := out.push (x0 + gk[b2]!.2 + n - qa)
          b2 := b2 + 1
        a := a + 1
    return out
  (clusterD ds g top).foldl (fun best (_, lo, hi) =>
    match semiDP R G (max x0 (lo - n - g)) (min x1 (hi + g)) with
    | some r => match best with
      | some b => if r.2.2.1 < b.2.2.1 then some r else best
      | none => some r
    | none => best) none

/-- Anchors `(vc, D, q)` of the seeds whose bucket holds ≤ `BK` places, both strands: `vc` = chromosome
(+ #chromosomes on the reverse strand), `D` = read end on the chromosome on that diagonal, `q` = seed
start in the read (each anchor is an exact 25-letter match, `mzLookS_ok`). -/
def anchorsX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (BK : Nat) :
    Array (Nat × Nat × Nat) := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 then return #[]
  let Ls := n / m
  let nc := pgs.size
  let mut out : Array (Nat × Nat × Nat) := #[]
  for b in [0:2] do
    let Rx := if b == 0 then R else s.Rr
    let pp := if b == 0 then s.ps else s.pr
    for j in [0:m] do
      if LookG.size pk pp[j]! ≤ BK then
        let a := LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
        for e in a do
          -- chromosome of the seed (offs increasing), seed inside it
          let p := e / 16 + j * Ls - n
          let mut lo := 0
          let mut hi := nc
          while lo + 1 < hi do
            let mid := (lo + hi) / 2
            if offs[mid]! ≤ p then lo := mid else hi := mid
          if offs[lo]! ≤ p && p + 25 ≤ offs[lo]! + pgs[lo]!.n then
            out := out.push (b * nc + lo, e / 16 - offs[lo]!, j * Ls)
  return out

@[inline] def keyLt (a b : Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- First index of sorted `A` with `(vc, D) ≥ (v, d)`. -/
def lbX (A : Array (Nat × Nat × Nat)) (v d : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := A.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let x := A[mid]!
    if x.1 < v || (x.1 == v && x.2.1 < d) then lo := mid + 1 else hi := mid
  return lo

/-- Seed bounds of one read of `n` letters over its sorted anchors `A`: (U bound = best single
diagonal, 4·(n − covered); chain bound = 4·(read letters outside seeds and gaps) + Σ (6 + 2|Δ|) over
chains increasing in read and genome, diagonal steps ≤ `Gm`; the best chain's (vc, Dlo, Dhi)).
Only alignments lying inside the chromosome count.  `INF` = none. -/
def chainX (n : Nat) (pgs : Array PGen) (A : Array (Nat × Nat × Nat)) (Gm : Nat) : Nat × Nat × (Nat × Nat × Nat) := Id.run do
  let INF := 1000000
  let nc := pgs.size
  let ord := (Array.range A.size).qsort (fun i j => A[i]!.2.2 < A[j]!.2.2)
  let mut f : Array Int := Array.replicate A.size (-1)
  let mut f0 : Array Int := Array.replicate A.size (-1)
  let mut d0 : Array Nat := Array.replicate A.size 0   -- first anchor's D
  let mut dl : Array Nat := Array.replicate A.size 0
  let mut dh : Array Nat := Array.replicate A.size 0
  let mut bU := INF
  let mut bC := INF
  let mut sp : Nat × Nat × Nat := (0, 0, 0)
  for j in ord do
    let (v, D, q) := A[j]!
    let mut bf : Int := 100
    let mut bf0 : Int := 100
    let mut bd0 := D
    let mut bl := D
    let mut bh := D
    let mut i := lbX A v (D - Gm)
    while i < A.size && A[i]!.1 == v && A[i]!.2.1 ≤ D + Gm do
      let (_, Di, qi) := A[i]!
      if qi + 25 ≤ q && f[i]! ≥ 0 then
        let cand : Option Int :=
          if Di == D then some (f[i]! + 100)
          else if Di < D then some (f[i]! + 100 - (6 + 2 * ((D - Di : Nat) : Int)))
          else if q - qi - 25 ≥ Di - D then some (f[i]! + 100 + 4 * ((Di - D : Nat) : Int) - (6 + 2 * ((Di - D : Nat) : Int)))
          else none
        if let some c := cand then
          if c > bf then
            bf := c
            bd0 := d0[i]!
            bl := min dl[i]! D
            bh := max dh[i]! D
        if Di == D && f0[i]! + 100 > bf0 then bf0 := f0[i]! + 100
      i := i + 1
    f := f.set! j bf
    f0 := f0.set! j bf0
    d0 := d0.set! j bd0
    dl := dl.set! j bl
    dh := dh.set! j bh
    let cl := pgs[v % nc]!.n
    if n ≤ D && D ≤ cl && 4 * n - bf0.toNat < bU then bU := 4 * n - bf0.toNat
    if n ≤ bd0 && D ≤ cl && (4 * (n : Int) - bf).toNat < bC then
      bC := (4 * (n : Int) - bf).toNat
      sp := (v, bl, bh)
  return (bU, bC, sp)

/-- Gapless mismatch count of the read on the diagonal `(vc, D)` (stops above `lim`). -/
def hamD (R Rr : ByteArray) (pgs : Array PGen) (v D lim : Nat) : Nat := Id.run do
  let nc := pgs.size
  let n := R.size
  let Rx := if v < nc then R else Rr
  let G := pgs[v % nc]!
  let st := D - n
  let mut mm := 0
  for i in [0:n] do
    if Rx.get! i != G.get (st + i) then
      mm := mm + 1
      if mm > lim then return mm
  return mm

/-- Best gapless diagonal among the `top` best-supported distinct diagonals of sorted `A` that lie
inside the chromosome: (vc, D, mismatches). -/
def hamX (R Rr : ByteArray) (pgs : Array PGen) (A : Array (Nat × Nat × Nat)) (top : Nat) : Option (Nat × Nat × Nat) := Id.run do
  let n := R.size
  let nc := pgs.size
  let mut ds : Array (Nat × Nat × Nat) := #[]   -- (support, vc, D)
  let mut i := 0
  while i < A.size do
    let (v, D, _) := A[i]!
    let mut j := i
    while j < A.size && A[j]!.1 == v && A[j]!.2.1 == D do j := j + 1
    if n ≤ D && D ≤ pgs[v % nc]!.n then ds := ds.push (j - i, v, D)
    i := j
  let sel := (ds.qsort fun a b => a.1 > b.1).extract 0 top
  let mut best : Option (Nat × Nat × Nat) := none
  for (_, v, D) in sel do
    let lim := match best with | some b => b.2.2 | none => n
    let mm := hamD R Rr pgs v D lim
    if mm < lim || best.isNone then best := some (v, D, mm)
  return best

/-- Common values of two increasing arrays. -/
def interS (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  let mut j := 0
  while i < a.size && j < b.size do
    let x := a[i]!
    let y := b[j]!
    if x < y then i := i + 1
    else if y < x then j := j + 1
    else
      out := out.push x
      i := i + 1
      j := j + 1
  return out

/-- Union of two increasing arrays (increasing, no repeats). -/
def unionS (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    let x := if i < a.size then a[i]! else 0
    let y := if j < b.size then b[j]! else 0
    let v := if j ≥ b.size || (i < a.size && x ≤ y) then x else y
    if i < a.size && x == v then i := i + 1
    if j < b.size && y == v then j := j + 1
    if out.back? != some v then out := out.push v
  return out

/-- A superset of the seed's places (bench only): the bucket's slots whose key and stored context
match (`Mz.okAt` without the genome letters it reads), as anchors `(pos − o + base)·16`, increasing.
The candidates are checked against the genome afterwards. -/
def rawLook (ix : Mz.MzIdx) (p : MzP) (base : Nat) : Array Nat := Id.run do
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  let key := p.h &&& ix.kbM
  let bw := (v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!
  let aw := (v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!
  let pmo := ix.pm[m1]!
  let o2 := 2 * (ix.c - m2)
  let mut out : Array Nat := #[]
  let mut sorted := true
  for t in [ix.loB p.b:ix.hiB p.b] do
    let e := ix.slot t
    if (e &&& ix.kbM) == key then
      let pos := ix.posOf e
      let tg := ix.tagOf e
      if o ≤ pos && (ix.flagF tg != 0 || ((ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw)) then
        let a := (pos - o + base) * 16
        if let some l := out.back? then
          if a < l then sorted := false
        out := out.push a
  return if sorted then out else out.qsort (· < ·)

/-- Perfect hits `(vc, start)` of a read over the genome, up to `L + 1` (bench only, unproved): a
perfect hit holds every seed, so the candidates are the two rarest seeds' common diagonals (bucket
supersets, `rawLook`), each checked letter by letter; plus the candidates checked and the smallest
bucket sizes per strand. -/
def perfX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (L : Nat) :
    Array (Nat × Nat) × Nat × List Nat := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 then return (#[], 0, [])
  let Ls := n / m
  let nc := pgs.size
  let mut hits : Array (Nat × Nat) := #[]
  let mut ncand := 0
  let mut szs : List Nat := []
  for b in [0:2] do
    if hits.size > L then break
    let Rx := if b == 0 then R else s.Rr
    let pp := if b == 0 then s.ps else s.pr
    let sel := (((List.range m).map fun j => (LookG.size pk pp[j]!, j)).mergeSort (fun x y => x.1 ≤ y.1)).take 2
    szs := szs ++ sel.map (·.1)
    let look := fun (j : Nat) => if pp[j]!.ok then rawLook pk.1 pp[j]! (n - j * Ls)
      else LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
    let A := sel.toArray.map fun x => look x.2
    let cands := if A.size == 1 then A[0]! else interS A[0]! A[1]!
    for e in cands do
      if hits.size > L then break
      ncand := ncand + 1
      let D := e / 16
      if D < n then continue
      let st0 := D - n
      let mut lo := 0
      let mut hi := nc
      while lo + 1 < hi do
        let mid := (lo + hi) / 2
        if offs[mid]! ≤ st0 then lo := mid else hi := mid
      if st0 < offs[lo]! then continue
      let st := st0 - offs[lo]!
      let G := pgs[lo]!
      if st + n > G.n then continue
      let mut ok := true
      for i in [0:n] do
        if Rx.get! i != G.get (st + i) then
          ok := false
          break
      if ok then hits := hits.push (b * nc + lo, st)
  return (hits, ncand, szs)

/-- Hits of a mate with ≤ `mmax` mismatches (gapless) forming a proper pair (`properPairU sl`) with
the partner's placement `pp`, by a letter scan of the region `regionB` (bench only). -/
def localX (R Rr : ByteArray) (pgs : Array PGen) (sl lo hi : Nat) (pp : Placement) (mmax : Nat) :
    Array (Placement × Nat) := Id.run do
  let n := R.size
  let w := regionB (4 * mmax) lo hi n pp
  let rev := pp.2 != Strand.rev
  let Rx := if rev then Rr else R
  let G := pgs[pp.1.chr]!
  let x1 := min w.2 G.n
  let mut out : Array (Placement × Nat) := #[]
  if x1 < w.1 + n then return out
  for st in [w.1:x1 + 1 - n] do
    let mut mm := 0
    for i in [0:n] do
      if Rx.get! i != G.get (st + i) then
        mm := mm + 1
        if mm > mmax then break
    if mm ≤ mmax then
      let pl : Placement := (⟨pp.1.chr, st, n⟩, if rev then Strand.rev else Strand.fwd)
      if properPairU sl lo hi pp pl then out := out.push (pl, 4 * mm)
  return out

/-- Candidates `(strand, anchor)` for the hits of a read with ≤ `mmax` ∈ {0, 1} mismatches (bench only;
pigeonhole on disjoint seeds, bucket supersets `rawLook`): cap 0, the two rarest seeds' common diagonals;
1 mismatch, the union of the pairwise intersections of the three rarest (two seeds: their union).
`none` when the pigeonhole does not apply (no seed; one seed at 1 mismatch). -/
def candX (pk : PkMz) (R : ByteArray) (s : PrepM MzP) (mmax : Nat) : Option (Array (Nat × Nat)) := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 || (mmax == 1 && m < 2) then return none
  let Ls := n / m
  let mut out : Array (Nat × Nat) := #[]
  for b in [0:2] do
    let Rx := if b == 0 then R else s.Rr
    let pp := if b == 0 then s.ps else s.pr
    let k := if mmax == 0 then min 2 m else min 3 m
    let sel := (((List.range m).map fun j => (LookG.size pk pp[j]!, j)).mergeSort (fun x y => x.1 ≤ y.1)).take k
    let look := fun (j : Nat) => if pp[j]!.ok then rawLook pk.1 pp[j]! (n - j * Ls)
      else LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
    let A := sel.toArray.map fun x => look x.2
    let cs := if mmax == 0 then (if k == 1 then A[0]! else interS A[0]! A[1]!)
      else if k == 2 then unionS A[0]! A[1]!
      else unionS (unionS (interS A[0]! A[1]!) (interS A[0]! A[2]!)) (interS A[1]! A[2]!)
    out := out ++ cs.map fun e => (b, e)
  return some out

/-- A candidate checked: `(vc, start, mismatches)` when the window lies in a chromosome and has
≤ `mmax` mismatches. -/
def verX (offs : Array Nat) (pgs : Array PGen) (R Rr : ByteArray) (b e mmax : Nat) : Option (Nat × Nat × Nat) := Id.run do
  let n := R.size
  let nc := pgs.size
  let D := e / 16
  if D < n then return none
  let st0 := D - n
  let mut lo := 0
  let mut hi := nc
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if offs[mid]! ≤ st0 then lo := mid else hi := mid
  if st0 < offs[lo]! then return none
  let st := st0 - offs[lo]!
  let G := pgs[lo]!
  if st + n > G.n then return none
  let Rx := if b == 0 then R else Rr
  let mut mm := 0
  for i in [0:n] do
    if Rx.get! i != G.get (st + i) then
      mm := mm + 1
      if mm > mmax then return none
  return some (b * nc + lo, st, mm)

/-- Pair-level guarantee at `G` ∈ {0, 4} (bench only, unproved): the proper pairs (`properPairU sl`)
with summed penalty ≤ G.  Such a pair has both mates within `G / 4` mismatches and one mate perfect,
so the mate with fewer candidates (`candX`) is enumerated and its partner checked letter by letter
in the region near each of its hits (0 / 1 mismatch so that the total stays ≤ G).  Stops at the
second qualifying pair (multimapping within G).  Answer: candidate counts, candidates checked, and
`none` (pigeonhole not applicable), else the first qualifying pair with a second-pair flag, or none. -/
def pairGX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (sl lo hi : Nat) (a b : ByteArray)
    (sa sb : PrepM MzP) (G : Nat) :
    (Nat × Nat) × Nat × Option (Option ((Placement × Nat) × (Placement × Nat) × Bool)) ×
      (Bool × Bool × Option (Nat × Nat × Nat)) := Id.run do
  let nc := pgs.size
  let mmax := G / 4
  -- the mate to enumerate: the smaller bucket scan (sizes are free; candidates of the other mate are
  -- never computed)
  let kk := if mmax == 0 then 2 else 3
  let scanC := fun (R : ByteArray) (s : PrepM MzP) =>
    let m := R.size / 25
    let one := fun (pp : Array MzP) =>
      (((List.range m).map fun j => LookG.size pk pp[j]!).mergeSort (· ≤ ·)).take kk |>.foldl (· + ·) 0
    one s.ps + one s.pr
  let swap := scanC b sb < scanC a sa
  let (X, sX, Y, sY) := if swap then (b, sb, a, sa) else (a, sa, b, sb)
  let okY : Bool := decide (Y.size / 25 ≥ (if mmax == 0 then 1 else 2))
  match (if okY then candX pk X sX mmax else none) with
  | some cs =>
    let ca := if swap then 0 else cs.size
    let cb := if swap then cs.size else 0
    let mut first : Option ((Placement × Nat) × (Placement × Nat)) := none
    let mut two := false
    let mut nscan := 0
    let mut bx : Option (Nat × Nat × Nat) := none
    for (st, e) in cs do
      if two then break
      nscan := nscan + 1
      if let some (vc, s0, mm) := verX offs pgs X sX.Rr st e mmax then
        if bx.all (fun h => mm < h.2.2) then bx := some (vc, s0, mm)
        let x : Placement := decB nc ⟨vc, s0, X.size⟩
        for y in localX Y sY.Rr pgs sl lo hi x (mmax - mm) do
          if first.isNone then first := some ((x, 4 * mm), y)
          else two := true
          if two then break
    let res := first.map fun (x, y) => if swap then (y, x, two) else (x, y, two)
    return ((ca, cb), nscan, some res, (swap, !two, bx))
  | none => return ((0, 0), 0, none, (swap, false, none))

/-- Floor and ceiling inputs of one mate (bench): per strand, the blocks whose (ACGT) seed lookup is
empty — `floor_look` (codecs/MateFloor.lean) gives penalty ≥ 4 per empty block on that strand; and the
best gapless diagonal `(vc, D, mismatches)` among at most `top` places of the rarest seed (bucket
1 … `BK`, either strand) that lie inside the chromosome (the ceiling, re-scored by the caller). -/
def boundX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (BK top : Nat) :
    Nat × Nat × Option (Nat × Nat × Nat) := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 then return (0, 0, none)
  let Ls := n / m
  let nc := pgs.size
  let mut e0 := 0
  let mut e1 := 0
  let mut rb : Option (Nat × Nat × Nat) := none   -- (bucket size, strand, block)
  for b in [0:2] do
    let pp := if b == 0 then s.ps else s.pr
    let Rx := if b == 0 then R else s.Rr
    for j in [0:m] do
      let p := pp[j]!
      if p.ok then
        let z := LookG.size pk p
        if z == 0 then
          if (LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) p).isEmpty then
            if b == 0 then e0 := e0 + 1 else e1 := e1 + 1
        else if z ≤ BK && rb.all (fun r => z < r.1) then rb := some (z, b, j)
  let mut best : Option (Nat × Nat × Nat) := none
  if top == 0 then return (e0, e1, none)
  if let some (_, b, j) := rb then
    let Rx := if b == 0 then R else s.Rr
    let pp := if b == 0 then s.ps else s.pr
    let a := LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
    for e in a.extract 0 top do
      let p := e / 16 + j * Ls - n
      let mut lo := 0
      let mut hi := nc
      while lo + 1 < hi do
        let mid := (lo + hi) / 2
        if offs[mid]! ≤ p then lo := mid else hi := mid
      if offs[lo]! ≤ p && p + 25 ≤ offs[lo]! + pgs[lo]!.n then
        let D := e / 16 - offs[lo]!
        if n ≤ D && D ≤ pgs[lo]!.n then
          let v := b * nc + lo
          let lim := match best with | some x => x.2.2 | none => n
          let mm := hamD R s.Rr pgs v D lim
          if mm < lim || best.isNone then best := some (v, D, mm)
  return (e0, e1, best)

/-- One mate of the tiered check: `st` = U (unique best, `pen`), T (tied best, `pen`), O (over:
best > `cd`, proved by the exact search at rung `cd`), S (no seed: no bound); `pl` = the best
placement (U/T) or the upper-bound alignment (O); bounds pU (one diagonal), pC (seed chain), pH (best
gapless diagonal), pD (DP on the best chain), pR (DP near the partner); `rs` = re-scored by
`checkRuns`. -/
structure MateX where
  st : String := "S"
  cap : Nat := 0
  cd : Nat := 0
  pen : Nat := 0
  pl : Option (Placement × Int) := none
  pU : Nat := 1000000
  pC : Nat := 1000000
  pH : Nat := 1000000
  pD : Nat := 1000000
  pR : Nat := 1000000
  rs : Bool := true
deriving Inhabited

def MateX.show (m : MateX) : String :=
  let pl := match m.pl with
    | some h => s!"{h.1.1.chr}\t{h.1.1.start}\t{h.1.1.len}\t{if h.1.2 == Strand.rev then "-" else "+"}\t{(-h.2).toNat}"
    | none => "-\t-\t-\t-\t-"
  s!"{m.st}\t{m.cap}\t{m.cd}\t{m.pen}\t{pl}\t{m.pU}\t{m.pC}\t{m.pH}\t{m.pD}\t{m.pR}\t{if m.rs then 1 else 0}"

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
  -- WG_TRIMQ: the trimmer's neutral quality (default `ReadTrim.defQ`; proved for Q ≤ 93)
  let tq := ((← IO.getEnv "WG_TRIMQ").bind String.toNat?).getD ReadTrim.defQ
  if ls[0]!.get! 0 == 64 then
    if ls.size % 4 != 0 then throw (IO.userError s!"{path}: {ls.size} lines, not 4 per record")
    return (Array.range (ls.size / 4)).map fun r =>
      let s := ls[4 * r + 1]!
      let q := ls[4 * r + 3]!
      if s.size != q.size then none else
      match ReadTrim.trimReadQ tq s q with
      | some (b, e) => some (s.extract b e)
      | none => none
  else
    if ls.size % 2 != 0 then throw (IO.userError s!"{path}: odd number of lines")
    -- an empty sequence line = trimmed away (as written by `WG_TRIMOUT`)
    return (Array.range (ls.size / 2)).map fun r =>
      let s := ls[2 * r + 1]!
      if s.size == 0 then none else some s

/-- `>r{i}`/sequence text of trimmed mates (empty line = trimmed away). -/
def writeMates (path : String) (m : Array (Option ByteArray)) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for i in [0:m.size] do
    h.putStr s!">r{i}\n"
    match m[i]! with
    | some s => h.write s
    | none => pure ()
    h.putStr "\n"
  h.flush

abbrev PairOut := Option ((Placement × Int) × (Placement × Int))

/-- Prototype (profile only): anchors held by a strand. -/
def gsAnchors (s : GS) : Nat := s.acc.foldl (fun a l => a + l.foldl (fun a2 arr => a2 + arr.size) 0) 0

/-- Prototype (profile only): live with `X` extra lookups once a strand holds `A` anchors. -/
def liveX (A X P : Nat) (s : GS) (b : Best) : Bool :=
  !s.ord.isEmpty && (!decide (sbound (min b.pen P) < s.J.length) ||
    (decide (s.J.length < sbound (min b.pen P) + 1 + X) && decide (A ≤ gsAnchors s)))

/-- Prototype: seed `R[s, s+25)` matches `G` at `p`. -/
def matchQx (R : ByteArray) (G : PGen) (s p : Nat) : Bool :=
  p + 25 ≤ GRead.size G && go 0 25
where go (k : Nat) : Nat → Bool
  | 0 => true
  | f + 1 => GRead.get G (p + k) == R.get! (s + k) && go (k + 1) f

/-- Prototype: some `p ∈ [lo, lo + w)` matches. -/
def nearX (R : ByteArray) (G : PGen) (s lo : Nat) : Nat → Bool
  | 0 => false
  | w + 1 => matchQx R G s lo || nearX R G s (lo + 1) w

/-- Prototype: at least `need` of the `m` seeds match within `r` of diagonal `D`
(early exits both ways). -/
def dOkX (R : ByteArray) (G : PGen) (m Ls need r D : Nat) : Bool :=
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
def unlookX (R : ByteArray) (G : PGen) (Ls r D sb : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j :: us, fail =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else nearX R G (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1)
    if ok then unlookX R G Ls r D sb us fail
    else if sb < fail + 1 then false else unlookX R G Ls r D sb us (fail + 1)

/-- Prototype word path: seed at read offset `s` spelled at some `p ∈ [lo, lo + w)`
(window flagged, read packed): 25 letters compared as one 50-bit field. -/
def nearSW (K : RP) (P : PGen) (s lo w : Nat) : Bool :=
  let rw := K.w
  let rs := comb rw[s / 32]! rw[s / 32 + 1]! (s % 32) (2 * (s % 32)).toUInt64 (64 - 2 * (s % 32)).toUInt64
  go rs (P.o + lo) w
where go (rs : UInt64) (a : Nat) : Nat → Bool
  | 0 => false
  | w + 1 =>
    let g := comb (gword P.w (a / 32)) (gword P.w (a / 32 + 1)) (a % 32) (2 * (a % 32)).toUInt64 (64 - 2 * (a % 32)).toUInt64
    ((g ^^^ rs) &&& 0x3FFFFFFFFFFFF) == 0 || go rs (a + 1) w

def unlookW (K : RP) (R : ByteArray) (G : PGen) (Ls r D sb : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j :: us, fail =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else
      let lo := a + r - n - min (2 * r) (a + r - n)
      let w := min (2 * r) (a + r - n) + 1
      if K.ok && winOk G lo (w + 24) then nearSW K G (j * Ls) lo w else nearX R G (j * Ls) lo w
    if ok then unlookW K R G Ls r D sb us fail
    else if sb < fail + 1 then false else unlookW K R G Ls r D sb us (fail + 1)

/-- Prototype: letters `[0, l)` of the piece at read offset `s` match at `p`. -/
def matchLx (R : ByteArray) (G : PGen) (s p l : Nat) : Bool := go 0 l
where go (k : Nat) : Nat → Bool
  | 0 => true
  | f + 1 => GRead.get G (p + k) == R.get! (s + k) && go (k + 1) f

def nearLx (R : ByteArray) (G : PGen) (l s lo : Nat) : Nat → Bool
  | 0 => false
  | w + 1 => matchLx R G s lo l || nearLx R G l s (lo + 1) w

/-- Prototype fine filter: pieces of `l` letters (spacing `n / (n / l)`); reject once more
than `sb` fail within `r` of `D`. -/
def fineX (R : ByteArray) (G : PGen) (l r D sb : Nat) : Bool :=
  let m := R.size / l
  let Ls := R.size / m
  go Ls 0 0 m
where go (Ls j f : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else
      nearLx R G l (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1)
    if ok then go Ls (j + 1) f k else if sb < f + 1 then false else go Ls (j + 1) (f + 1) k

/-- Prototype fine filter, pieces tried in order `ord` (a permutation of the pieces):
the answer does not depend on the order; also returns the failing pieces met. -/
def fineM (R : ByteArray) (G : PGen) (l r D sb : Nat) (ord : List Nat) : Bool × List Nat :=
  let m := R.size / l
  let Ls := R.size / m
  go Ls ord 0 []
where go (Ls : Nat) : List Nat → Nat → List Nat → Bool × List Nat
  | [], _, fs => (true, fs)
  | j :: rest, f, fs =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else
      nearLx R G l (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1)
    if ok then go Ls rest f fs else if sb < f + 1 then (false, j :: fs) else go Ls rest (f + 1) (j :: fs)

/-- Memo, two entries per piece `j`: `M[2j] = a`, `M[2j+1] = 2e + f`: no match at
`[a, e)`; `f = 1`: a match at `e`. -/
abbrev FMemo := Array Nat

/-- First match of the piece at read offset `s` in `[p, hi)`, else `hi`. -/
def scanL (R : ByteArray) (G : PGen) (l s p : Nat) : Nat → Nat
  | 0 => p
  | w + 1 => if matchLx R G s p l then p else scanL R G l s (p + 1) w

/-- Is there a match of piece `j` (read offset `s`) in `[lo, lo + w)`, through the memo. -/
@[inline] def qMemo (R : ByteArray) (G : PGen) (l j s lo w : Nat) (M : FMemo) : Bool × FMemo :=
  let a := M[2 * j]!
  let ef := M[2 * j + 1]!
  let e := ef / 2
  let hi := lo + w
  if a ≤ lo && lo ≤ e then
    if ef % 2 == 1 then (decide (e < hi), M)
    else if hi ≤ e then (false, M)
    else
      let p := scanL R G l s e (hi - e)
      let ok := decide (p < hi)
      (ok, M.set! (2 * j + 1) (2 * p + if ok then 1 else 0))
  else
    let p := scanL R G l s lo w
    let ok := decide (p < hi)
    (ok, (M.set! (2 * j) lo).set! (2 * j + 1) (2 * p + if ok then 1 else 0))

def fineMemo (R : ByteArray) (G : PGen) (l r D sb : Nat) (M : FMemo) : Bool × FMemo :=
  let m := R.size / l
  let Ls := R.size / m
  go Ls 0 0 m M
where go (Ls j f : Nat) : Nat → FMemo → Bool × FMemo
  | 0, M => (true, M)
  | k + 1, M =>
    let a := D + j * Ls
    let n := R.size
    let (ok, M) := if a + r < n then (false, M) else
      qMemo R G l j (j * Ls) (a + r - n - min (2 * r) (a + r - n)) (min (2 * r) (a + r - n) + 1) M
    if ok then go Ls (j + 1) f k M else if sb < f + 1 then (false, M) else go Ls (j + 1) (f + 1) k M

/-- Prototype word test: a match of read letters `[s, s + l)` at some genome start in
`[lo, lo + w)` (`l < 32`, `w + l ≤ 33`, window flagged, read packed), 2 bits per letter. -/
@[inline] def nearW (K : RP) (P : PGen) (l s lo w : Nat) : Bool :=
  let a := P.o + lo
  let g := comb (gword P.w (a / 32)) (gword P.w (a / 32 + 1)) (a % 32) (2 * (a % 32)).toUInt64 (64 - 2 * (a % 32)).toUInt64
  let mk : UInt64 := (1 <<< (2 * l).toUInt64) - 1
  let rw := K.w
  let rp := comb rw[s / 32]! rw[s / 32 + 1]! (s % 32) (2 * (s % 32)).toUInt64 (64 - 2 * (s % 32)).toUInt64 &&& mk
  go g mk rp w
where go (g mk rp : UInt64) : Nat → Bool
  | 0 => false
  | i + 1 => (g &&& mk) == rp || go (g >>> 2) mk rp i

def fineW (K : RP) (R : ByteArray) (G : PGen) (l r D sb : Nat) : Bool :=
  let m := R.size / l
  let Ls := R.size / m
  go Ls 0 0 m
where go (Ls j f : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else
      let lo := a + r - n - min (2 * r) (a + r - n)
      let w := min (2 * r) (a + r - n) + 1
      if K.ok && decide (w + l ≤ 33) && winOk G lo (w + l - 1) then nearW K G l (j * Ls) lo w
      else nearLx R G l (j * Ls) lo w
    if ok then go Ls (j + 1) f k else if sb < f + 1 then false else go Ls (j + 1) (f + 1) k

def chromKBX (XL : Nat) (kf : Ker) (KR : RP) (R : ByteArray) (gbs : Array PGen) (c P : Nat) (acc : List (Array Nat)) (J : List Nat) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let m := R.size / 25
  let Ls := R.size / m
  let G := gbs[c]!
  let us := (List.range m).filter (fun j => !J.contains j)
  let r := 2 * gapBound sc0 (-(Q1 : Int))
  let fl := XL % 100
  let ord0 := List.range (R.size / max fl 1)
  let mz := R.size / max fl 1
  let M0 : FMemo := (Array.range (2 * mz)).map fun i => if i % 2 == 0 then 1 else 0
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      if 200 ≤ XL && XL < 300 then ((diags acc).foldl (fun (x : Best × FMemo) D =>
        let b := x.1
        let Q := min lim b.pen
        let rq := 2 * gapBound sc0 (-(Q : Int))
        let fJ := acc.length - suppA acc D rq
        if fJ ≤ sbound Q && unlookX R G Ls rq D (sbound Q) us fJ then
          let (okF, M) := if XL == 299 then (false, x.2) else fineMemo R G fl rq D (sbound Q) x.2
          if okF then ((shapesKT Q1).foldl (fun b sh => addKF kf c lim (dst R.size D sh) (wlen R.size sh) b) b, M)
          else (b, M)
        else x) (b1, M0)).1 else
      ((diags acc).foldl (fun (x : Best × List Nat) D =>
        let b := x.1
        let Q := min lim b.pen
        let rq := 2 * gapBound sc0 (-(Q : Int))
        let fJ := acc.length - suppA acc D rq
        if fJ ≤ sbound Q && (if XL == 500 then unlookW KR R G Ls rq D (sbound Q) us fJ else unlookX R G Ls rq D (sbound Q) us fJ) then
          let (okF, ord) := if XL == 0 || XL == 500 then (true, x.2) else if XL < 100 then (fineX R G XL rq D (sbound Q), x.2)
            else if 400 ≤ XL then (fineW KR R G (XL - 400) rq D (sbound Q), x.2)
            else
              let (o, fs) := fineM R G fl rq D (sbound Q) x.2
              (o, if fs.isEmpty then x.2 else fs ++ x.2.filter (fun j => !fs.contains j))
          if okF then ((shapesKT Q1).foldl (fun b sh => addKF kf c lim (dst R.size D sh) (wlen R.size sh) b) b, ord)
          else (b, ord)
        else x) (b1, ord0)).1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int))))
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

/-- Prototype word test for any window width: read letters `[s, s + l)` (`l ≤ 16`) at some
genome start in `[lo, lo + w)` (window flagged, read packed); one 64-bit genome field per
`33 − l` starts. -/
def nearWL (K : RP) (P : PGen) (l s lo w : Nat) : Bool :=
  let mk : UInt64 := (1 <<< (2 * l).toUInt64) - 1
  let rw := K.w
  let rp := comb rw[s / 32]! rw[s / 32 + 1]! (s % 32) (2 * (s % 32)).toUInt64 (64 - 2 * (s % 32)).toUInt64 &&& mk
  outer mk rp (P.o + lo) w (w + 1)
where
  inner (mk rp g : UInt64) : Nat → Bool
    | 0 => false
    | i + 1 => (g &&& mk) == rp || inner mk rp (g >>> 2) i
  outer (mk rp : UInt64) (a w : Nat) : Nat → Bool
    | 0 => false
    | f + 1 =>
      if w == 0 then false else
      let c := min w (33 - l)
      let g := comb (gword P.w (a / 32)) (gword P.w (a / 32 + 1)) (a % 32) (2 * (a % 32)).toUInt64 (64 - 2 * (a % 32)).toUInt64
      inner mk rp g c || outer mk rp (a + c) (w - c) f

/-- Prototype: `fineOk` (pieces of `l` letters) with the word test where the window is flagged. -/
def fineWL (K : RP) (R : ByteArray) (G : PGen) (l Ls r D sb : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | j, f, k + 1 =>
    let a := D + j * Ls
    let n := R.size
    let ok := if a + r < n then false else
      let lo := a + r - n - min (2 * r) (a + r - n)
      let w := min (2 * r) (a + r - n) + 1
      if K.ok && decide (lo + w + l ≤ GRead.size G) && winOk G lo (w + l - 1) then nearWL K G l (j * Ls) lo w
      else nearL R G (j * Ls) l lo w
    if ok then fineWL K R G l Ls r D sb (j + 1) f k
    else if sb < f + 1 then false else fineWL K R G l Ls r D sb (j + 1) (f + 1) k

/-- Prototype: `kfilt` with word tests (unseen seeds: `unlookW`; pieces: `fineWL`). -/
@[inline] def kfiltW (K : RP) (R : ByteArray) (G : PGen) (acc : List (Array Nat)) (us : List Nat)
    (Ls lim : Nat) (b : Best) (D : Nat) : Bool :=
  let Q := min lim b.pen
  let r := 2 * gapBound sc0 (-(Q : Int))
  let fJ := acc.length - suppA acc D r
  decide (fJ ≤ sbound Q) && unlookW K R G Ls r D (sbound Q) us fJ &&
    fineWL K R G pl (R.size / (R.size / pl)) r D (sbound Q) 0 0 (R.size / pl)

/-- Word filter cut at level `lv` (profile): 0 count only, 1 + wordWin, 2 + loadG,
3 + unlookV, 4 full. Returns a checksum. -/
def kfLv (lv : Nat) (K : RP) (R : ByteArray) (P : PGen) (acc : List (Array Nat)) (us : List Nat)
    (Ls lim : Nat) (b : Best) (D s : Nat) : Nat :=
  let Q := min lim b.pen
  let r := 2 * gapBound sc0 (-(Q : Int))
  let n := R.size
  let fJ := acc.length - s
  let sb := sbound Q
  if fJ ≤ sb then
    if lv == 0 then 1 else
    if wordWin K n r D P then
      if lv == 1 then 1 else
      let a := P.o + (D - n - r)
      let o := a % 32
      let gs := loadG P.w (a / 32) ((o + 2 * r + n) / 32 + 2)
      if lv == 2 then (gs.get 1).toNat % 2 + 1 else
      if lv == 5 then
        let gs2 := loadG P.w (a / 32) ((o + 2 * r + n) / 32 + 2 + (gs.get 1).toNat % 2)
        ((gs.get 1) ^^^ (gs2.get 2)).toNat % 2 + 1 else
      let u := usIn Ls n us && unlookV K gs o Ls r sb us fJ
      if lv == 3 then (if u then 1 else 0) else
      if u && fineE K gs o n r (n / pl) (n / pl) 0 ((n + 31) / 32) sb then 1 else 0
    else 0
  else 0

/-- Prototype (profile only): `chromKBFG` with stage B's diagonals through `kfiltW` at cap `P`. -/
def chromKBPw (kf : Ker) (K : RP) (R : ByteArray) (gbs : Array PGen) (c P : Nat) (acc : List (Array Nat))
    (J : List Nat) (b1 : Best) (noB : Bool := false) (noF : Bool := false) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let us := unseen (R.size / 25) J
  let Ls := R.size / (R.size / 25)
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageKS (fun D b => stageKF kf R.size c lim (shapesKT Q1) [D] b)
        R gbs[c]! acc us Ls lim (diags acc) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    let ds := (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))).filter
      fun D => !noF && kfiltW K R gbs[c]! acc us Ls P b2 D
    if noB then { b2 with pen := b2.pen + ds.length } else
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
  else b2

/-- Prototype (profile only): `chromKBFG` with stage B's diagonals through `kfilt` at cap `P`. -/
def chromKBPf (kf : Ker) (R : ByteArray) (gbs : Array PGen) (c P : Nat) (acc : List (Array Nat)) (J : List Nat)
    (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let us := unseen (R.size / 25) J
  let Ls := R.size / (R.size / 25)
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageKS (fun D b => stageKF kf R.size c lim (shapesKT Q1) [D] b)
        R gbs[c]! acc us Ls lim (diags acc) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    let ds := (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))).filter
      fun D => kfilt R gbs[c]! acc us Ls P b2 D
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
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
  slowFine : Nat := 0
  slowDiagNs : Nat := 0
  kOnlyNs : Nat := 0
  bDiags : Nat := 0
  bPass : Nat := 0
  bFiltNs : Nat := 0
  bReads : Nat := 0
  bNone : Nat := 0
  bTopNs : Array Nat := #[]
  bWordNs : Nat := 0
  bNoBNs : Nat := 0
  bDiagNs : Nat := 0
  slowDdNs : Nat := 0
  slowSuppNs : Nat := 0
  slowUnNs : Nat := 0
  slowUnPass : Nat := 0
  slowLkNs : Nat := 0
  slowK12Ns : Nat := 0
  slowK16Ns : Nat := 0
  slowKAnc : Nat := 0
  slowVNs : Nat := 0
  slowVPass : Nat := 0
  slowVDiff : Nat := 0
  slowD2Ns : Nat := 0
  blkCur : Nat := 0
  slowSwNs : Nat := 0
  lvNs : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]
  lvCnt : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]
  lvDiags : Nat := 0
  slowSwDiff : Nat := 0
  blkAlt : Nat := 0
  clsAll : Nat := 0
  clsAllC : Nat := 0
  clsAllM : Nat := 0
  clsPass : Nat := 0
  clsPassC : Nat := 0
  clsPassM : Nat := 0
  slowD3Ns : Nat := 0
  slowSlNs : Nat := 0
  penHist : Array Nat := Array.replicate 18 0
  lkHist : Array Nat := Array.replicate 25 0

def profRead (XA XN : Nat) (XF : Bool) (XK XL : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (P : Nat) (R : ByteArray) (pf : Prof) :
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
  -- XK (timing only, not exact): 1 = cap-16 kernel without the two-gap / band fallback;
  -- 2 = every kernel call returns `l + 1` (stage K body cost removed)
  let kx : ByteArray → RP → Ker := fun R K c st len l =>
    if XK == 2 then l + 1
    else if XK == 1 && 16 ≤ l then (let r := kerGKG R K gbs2[c]! gbs2[c]! st len 16; if r ≤ 16 then r else 17)
    else kerHKG R K gbs2 gbs2 c st len l
  let kf1 := kx R K1
  let kf2 := kx Rr K2
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
  let b := (List.range n).foldl (fun b c => if XF then chromKBX XL kf1 K1 R gbs2 c P x.1.acc[c]! x.1.J b
    else chromKBFG kf1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2
  let b := (List.range n).foldl (fun b c => if XF then chromKBX XL kf2 K2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b
    else chromKBFG kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b) b
  let b ← (← IO.mkRef b).get
  let t3 ← IO.monoNanosNow
  -- stage K only (cap 16) and the filtered stage B prototype, timed separately
  let kOnly := fun (Q : Nat) => (List.range n).foldl (fun b c => chromKBFG kf2 Rr gbs2 (n + c) Q x.2.1.acc[c]! x.2.1.J b)
    ((List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c Q x.1.acc[c]! x.1.J b) x.2.2)
  let w0 ← IO.monoNanosNow
  let bk16 ← (← IO.mkRef (kOnly (min P 16))).get
  let w1 ← IO.monoNanosNow
  let bF := (List.range n).foldl (fun b c => chromKBPf kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b)
    ((List.range n).foldl (fun b c => chromKBPf kf1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2)
  let bF ← (← IO.mkRef bF).get
  let w2 ← IO.monoNanosNow
  let bW := (List.range n).foldl (fun b c => chromKBPw kf2 K2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b)
    ((List.range n).foldl (fun b c => chromKBPw kf1 K1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2)
  let bW ← (← IO.mkRef bW).get
  let w3 ← IO.monoNanosNow
  if bW.pen != bF.pen || bW.amb != bF.amb || bW.chr != bF.chr || bW.st != bF.st || bW.len != bF.len then say s!"  WORD DIFF read {pf.reads}"
  let bN := (List.range n).foldl (fun b c => chromKBPw kf2 K2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b true)
    ((List.range n).foldl (fun b c => chromKBPw kf1 K1 R gbs2 c P x.1.acc[c]! x.1.J b true) x.2.2)
  let bN ← (← IO.mkRef bN).get
  let w4 ← IO.monoNanosNow
  let bD := (List.range n).foldl (fun b c => chromKBPw kf2 K2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b true true)
    ((List.range n).foldl (fun b c => chromKBPw kf1 K1 R gbs2 c P x.1.acc[c]! x.1.J b true true) x.2.2)
  let bD ← (← IO.mkRef bD).get
  let w5 ← IO.monoNanosNow
  let pf := { pf with bWordNs := pf.bWordNs + (w3 - w2), bNoBNs := pf.bNoBNs + (w4 - w3) + 0 * bN.pen }
  let pf := { pf with bDiagNs := pf.bDiagNs + (w5 - w4) + 0 * bD.pen }
  if bF.pen != b.pen || bF.amb != b.amb then say s!"  PROTO DIFF read {pf.reads}: {b.pen}/{b.amb} vs {bF.pen}/{bF.amb}"
  let isB := decide (min P 16 < min bk16.pen P)
  let (nd, np) := if isB then
      let cnt := fun (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun (a : Nat × Nat) c =>
        let acc := s.acc[c]!
        let q2 := min bk16.pen P
        let ds := diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(q2 : Int)))
        (a.1 + ds.length, a.2 + (ds.filter fun D => kfilt Rx gbs2[t + c]! acc (unseen (Rx.size / 25) s.J)
          (Rx.size / (Rx.size / 25)) P bk16 D).length)) (0, 0)
      let u := cnt R 0 x.1
      let v := cnt Rr n x.2.1
      (u.1 + v.1, u.2 + v.2)
    else (0, 0)
  let pf := { pf with kOnlyNs := pf.kOnlyNs + (w1 - w0) }
  let pf := { pf with bFiltNs := pf.bFiltNs + (w2 - w1) }
  let pf := { pf with bDiags := pf.bDiags + nd, bPass := pf.bPass + np }
  let pf := { pf with bReads := pf.bReads + (if isB then 1 else 0) }
  let pf := { pf with bNone := pf.bNone + (if isB && decide (b.pen > P) then 1 else 0) }
  let pf := if isB then { pf with bTopNs := pf.bTopNs.push (t3 - t2) } else pf
  let lk := x.1.J.length + x.2.1.J.length
  let hits := (x.1.acc.toList ++ x.2.1.acc.toList).foldl (fun a l => a + l.foldl (fun a2 arr => a2 + arr.size) 0) 0
  let szs := (x.1.J.map fun j => LookG.size ix ps[j]!) ++ (x.2.1.J.map fun j => LookG.size ix pr[j]!)
  let bk := szs.foldl (· + ·) 0
  let big := szs.filter (· > 1000)
  let slow := t3 - t1 > 1000000
  if t3 - t1 > 20000000 then
    let allSz := (ps.toList.map (LookG.size ix)) ++ (pr.toList.map (LookG.size ix))
    say s!"  read {pf.reads}: {R.size} letters, P {P}, {secs t1 t3} s (phase 1 {secs t1 t2}), lookups {lk}, anchors {hits}, best {b.pen} amb {b.amb}, bucket sizes {allSz}"
  let bigSum := big.foldl (fun a v => a + v) 0
  -- block choice: each block of Ls letters may use any 25-letter subwindow (least bucket)
  let slowB := t3 - t1 > 1000000
  let pf := if slowB then
      let bestOf := fun (Rx : ByteArray) (Kx : RP) (j : Nat) =>
        (List.range (Ls - 25 + 1)).foldl (fun a d =>
          min a (LookG.size ix (LookG.prep ix (seedHashK Rx Kx (j * Ls + d)) : MzP))) 1000000000
      let cur := fun (pp : Array MzP) (J : List Nat) => (J.map fun j => LookG.size ix pp[j]!).foldl (· + ·) 0
      let alt := fun (Rx : ByteArray) (Kx : RP) (J : List Nat) =>
        (((List.range m).map (bestOf Rx Kx)).mergeSort (· ≤ ·)).take J.length |>.foldl (· + ·) 0
      let c1 := cur ps x.1.J + cur pr x.2.1.J
      let a1 := alt R K1 x.1.J + alt Rr K2 x.2.1.J
      { pf with blkCur := pf.blkCur + c1, blkAlt := pf.blkAlt + a1 }
    else pf
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
      let Q := min (min P 16) b.pen
      let rq := 2 * gapBound sc0 (-(Q : Int))
      let fl := fun (Rx : ByteArray) (t : Nat) (s : GS) =>
        (List.range n).foldl (fun (a : Nat × Nat × Nat) c =>
          let acc := s.acc[c]!
          let ds := diags acc
          let us := unseen (Rx.size / 25) s.J
          let ps := ds.filter fun D => kfilt Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D
          let fs := ps.filter fun D => fineX Rx gbs2[t + c]! 8 rq D (sbound Q)
          (a.1 + ds.length, a.2.1 + ps.length, a.2.2 + fs.length)) (0, 0, 0)
      let dl := fun (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let us := unseen (Rx.size / 25) s.J
        a + ((diags acc).filter fun D => kfilt Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D).length) 0
      let v0 ← IO.monoNanosNow
      let d1 ← (← IO.mkRef (dl R 0 x.1 + dl Rr n x.2.1)).get
      let v1 ← IO.monoNanosNow
      let dv := fun (Kx : RP) (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let us := unseen (Rx.size / 25) s.J
        a + ((diags acc).filter fun D => kfiltV Kx Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D).length) 0
      let dx := fun (Kx : RP) (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let us := unseen (Rx.size / 25) s.J
        a + ((diags acc).filter fun D => kfiltV Kx Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D !=
          kfilt Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D).length) 0
      let x0 ← IO.monoNanosNow
      let dV ← (← IO.mkRef (dv K1 R 0 x.1 + dv K2 Rr n x.2.1)).get
      let x1 ← IO.monoNanosNow
      let dX := dx K1 R 0 x.1 + dx K2 Rr n x.2.1
      let pf := { pf with slowVNs := pf.slowVNs + (x1 - x0), slowVPass := pf.slowVPass + dV, slowVDiff := pf.slowVDiff + dX }
      -- repeat classes: identical genome windows [D − n − g, D + g) among the read's diagonals
      let g := gapBound sc0 (-(16 : Int))
      let wh := fun (Gx : PGen) (st len : Nat) => (List.range len).foldl (fun (h : UInt64) i =>
        (h ^^^ (Gx.get (st + i)).toUInt64) * 0x100000001b3) 0xcbf29ce484222325
      let hs := fun (pass : Bool) (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun (a : Array UInt64) c =>
        let acc := s.acc[c]!
        let us := unseen (Rx.size / 25) s.J
        let Gx := gbs2[t + c]!
        (diags acc).foldl (fun a D =>
          if Rx.size + g ≤ D && D + g ≤ Gx.n && (!pass || kfilt Rx Gx acc us (Rx.size / (Rx.size / 25)) (min P 16) b D)
          then a.push (wh Gx (D - Rx.size - g) (Rx.size + 2 * g)) else a) a) #[]
      let cls := fun (a : Array UInt64) =>
        let srt := a.qsort (· < ·)
        let r := srt.foldl (fun (st : Nat × Nat × Nat × UInt64 × Bool) h =>
          -- (classes, members of multi-copy classes, current run length, last, first)
          if !st.2.2.2.2 && h == st.2.2.2.1 then (st.1, st.2.1 + (if st.2.2.1 == 1 then 2 else 1), st.2.2.1 + 1, h, false)
          else (st.1 + 1, st.2.1, 1, h, false)) (0, 0, 0, 0, true)
        (a.size, r.1, r.2.1)
      let cA := cls (hs false R 0 x.1 ++ hs false Rr n x.2.1)
      let cP := cls (hs true R 0 x.1 ++ hs true Rr n x.2.1)
      let pf := { pf with clsAll := pf.clsAll + cA.1, clsAllC := pf.clsAllC + cA.2.1, clsAllM := pf.clsAllM + cA.2.2 }
      let pf := { pf with clsPass := pf.clsPass + cP.1, clsPassC := pf.clsPassC + cP.2.1, clsPassM := pf.clsPassM + cP.2.2 }
      let ddq := fun (s : GS) => (List.range n).foldl (fun a c => a + (diags s.acc[c]!).length) 0
      let q0 ← IO.monoNanosNow
      let qq ← (← IO.mkRef (ddq x.1 + ddq x.2.1)).get
      let q1 ← IO.monoNanosNow
      let qq2 ← (← IO.mkRef (ddq x.1 + ddq x.2.1)).get
      let q2 ← IO.monoNanosNow
      let pf := { pf with slowD2Ns := pf.slowD2Ns + (q1 - q0) + 0 * qq, slowD3Ns := pf.slowD3Ns + (q2 - q1) + 0 * qq2 }
      let dd := fun (s : GS) => (List.range n).foldl (fun a c => a + (diags s.acc[c]!).length) 0
      let ds := fun (Rx : ByteArray) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let Q := min (min P 16) b.pen
        let r := 2 * gapBound sc0 (-(Q : Int))
        a + ((diags acc).filter fun D => decide (acc.length - suppA acc D r ≤ sbound Q)).length + 0 * Rx.size) 0
      let y0 ← IO.monoNanosNow
      let e1 ← (← IO.mkRef (dd x.1 + dd x.2.1)).get
      let y1 ← IO.monoNanosNow
      let e2 ← (← IO.mkRef (ds R x.1 + ds Rr x.2.1)).get
      let y2 ← IO.monoNanosNow
      let dsw := fun (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let Q := min (min P 16) b.pen
        let r := 2 * gapBound sc0 (-(Q : Int))
        let cnt := suppCntC acc r (diags acc)
        a + cnt.foldl (fun a v => if acc.length - v ≤ sbound Q then a + 1 else a) 0) 0
      let ys0 ← IO.monoNanosNow
      let e2w ← (← IO.mkRef (dsw x.1 + dsw x.2.1)).get
      let ys1 ← IO.monoNanosNow
      let pf := { pf with slowSwNs := pf.slowSwNs + (ys1 - ys0), slowSwDiff := pf.slowSwDiff + (if e2w == e2 then 0 else 1) }
      let lvRun := fun (lv : Nat) (Kx : RP) (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let ds := diags acc
        let Q := min (min P 16) b.pen
        let r := 2 * gapBound sc0 (-(Q : Int))
        if lv == 10 then a + ds.length else
        let cnt := suppCntC acc r ds
        if lv == 11 then a + cnt.size else
        let us := unseen (Rx.size / 25) s.J
        let rr := ds.foldl (fun (z : Nat × Nat) D =>
          (z.1 + kfLv lv Kx Rx gbs2[t + c]! acc us (Rx.size / (Rx.size / 25)) (min P 16) b D (cnt.getD z.2 0), z.2 + 1)) (0, 0)
        a + rr.1) 0
      let mut lvNs : Array Nat := #[]
      let mut lvCnt : Array Nat := #[]
      for lv in [10, 11, 0, 1, 2, 5, 3, 4] do
        let l0 ← IO.monoNanosNow
        let cc ← (← IO.mkRef (lvRun lv K1 R 0 x.1 + lvRun lv K2 Rr n x.2.1)).get
        let l1 ← IO.monoNanosNow
        lvNs := lvNs.push (l1 - l0)
        lvCnt := lvCnt.push cc
      let pf := { pf with lvNs := (pf.lvNs.zip lvNs).map (fun (u, v) => u + v), lvCnt := (pf.lvCnt.zip lvCnt).map (fun (u, v) => u + v), lvDiags := pf.lvDiags + dd x.1 + dd x.2.1 }
      let du := fun (Rx : ByteArray) (t : Nat) (s : GS) => (List.range n).foldl (fun a c =>
        let acc := s.acc[c]!
        let Q := min (min P 16) b.pen
        let r := 2 * gapBound sc0 (-(Q : Int))
        let fJ := fun D => acc.length - suppA acc D r
        a + ((diags acc).filter fun D => decide (fJ D ≤ sbound Q) &&
          unlook Rx gbs2[t + c]! (Rx.size / (Rx.size / 25)) r D (sbound Q) (unseen (Rx.size / 25) s.J) (fJ D)).length) 0
      let e3 ← (← IO.mkRef (du R 0 x.1 + du Rr n x.2.1)).get
      let y3 ← IO.monoNanosNow
      -- the lookups alone (the seeds the search looked up), then also the per-chromosome slices
      let z0 ← IO.monoNanosNow
      let lk1 ← (← IO.mkRef ((x.1.J.map fun j => (LookG.look ix ByteArray.empty R (j * Ls) (R.size - j * Ls) ps[j]!).size).foldl (· + ·) 0)).get
      let lk2 ← (← IO.mkRef ((x.2.1.J.map fun j => (LookG.look ix ByteArray.empty Rr (j * Ls) (Rr.size - j * Ls) pr[j]!).size).foldl (· + ·) 0)).get
      let z1 ← IO.monoNanosNow
      let sl := fun (Rx : ByteArray) (t : Nat) (J : List Nat) (pp : Array MzP) => (J.map fun j =>
        let a := LookG.look ix ByteArray.empty Rx (j * Ls) (Rx.size - j * Ls) pp[j]!
        (List.range n).foldl (fun acc c => acc + (sliceG a (Rx.size - j * Ls) offs[c]! (GRead.size gbs2[t + c]!)).size) 0).foldl (· + ·) 0
      let sl1 ← (← IO.mkRef (sl R 0 x.1.J ps + sl Rr n x.2.1.J pr)).get
      let z2 ← IO.monoNanosNow
      -- the phase-1 kernel alone at every anchor (same-length window), at cap 12 and 16
      let kall := fun (l : Nat) => (List.range n).foldl (fun a c =>
        let f := fun (kf : Ker) (Rx : ByteArray) (t : Nat) (acc : List (Array Nat)) =>
          acc.foldl (fun a2 arr => arr.foldl (fun a3 e =>
            let st : Int := ((e / 16 : Nat) : Int) - (Rx.size : Int)
            if 0 ≤ st then a3 + kf (t + c) st.toNat Rx.size l else a3) a2) 0
        a + f kf1 R 0 x.1.acc[c]! + f kf2 Rr n x.2.1.acc[c]!) 0
      let k0 ← IO.monoNanosNow
      let q12 ← (← IO.mkRef (kall 12)).get
      let k1 ← IO.monoNanosNow
      let q16 ← (← IO.mkRef (kall 16)).get
      let k2 ← IO.monoNanosNow
      let pf := { pf with slowK12Ns := pf.slowK12Ns + (k1 - k0) + 0 * q12, slowK16Ns := pf.slowK16Ns + (k2 - k1) + 0 * q16, slowKAnc := pf.slowKAnc + hits }
      let pf := { pf with slowLkNs := pf.slowLkNs + (z1 - z0) + 0 * (lk1 + lk2), slowSlNs := pf.slowSlNs + (z2 - z1) + 0 * sl1 }
      let pf := { pf with slowDdNs := pf.slowDdNs + (y1 - y0) + 0 * e1, slowSuppNs := pf.slowSuppNs + (y2 - y1) + 0 * e2, slowUnNs := pf.slowUnNs + (y3 - y2), slowUnPass := pf.slowUnPass + e3 }
      let u0 ← IO.monoNanosNow
      let r1 ← (← IO.mkRef (fl R 0 x.1)).get
      let r2 ← (← IO.mkRef (fl Rr n x.2.1)).get
      let u1 ← IO.monoNanosNow
      let pf := { pf with slowDiags := pf.slowDiags + r1.1 + r2.1, slowPass := pf.slowPass + r1.2.1 + r2.2.1 }
      let pf := { pf with slowFine := pf.slowFine + r1.2.2 + r2.2.2 + 0 * d1, slowDiagNs := pf.slowDiagNs + (v1 - v0) }
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
  say s!"  reads > 1 ms: diagonals {pf.slowDiags}, passing the filter at the final best {pf.slowPass}, also the 8-letter fine filter {pf.slowFine}; diags + kfilt {secs 0 pf.slowDiagNs} s, diags + filters {secs 0 pf.slowFiltNs} s"
  say s!"  reads > 1 ms: diags + word kfiltV {secs 0 pf.slowVNs} s, passing {pf.slowVPass}, differing from kfilt {pf.slowVDiff}; diags again {secs 0 pf.slowD2Ns} s, {secs 0 pf.slowD3Ns} s"
  say s!"  reads > 1 ms: diags + swept supports (suppCntC) {secs 0 pf.slowSwNs} s, reads differing {pf.slowSwDiff}"
  say s!"  reads > 1 ms: word filter by level over {pf.lvDiags} diagonals (diags, +suppCntC, +count, +wordWin, +loadG, +loadG twice, +unlookV, full): ns {pf.lvNs}, ns/diag {pf.lvNs.map (· / max 1 pf.lvDiags)}, counts {pf.lvCnt}"
  say s!"  reads > 1 ms: bucket entries of the seeds looked up {pf.blkCur}; with the least 25-letter subwindow per block {pf.blkAlt}"
  say s!"  reads > 1 ms: repeat classes (identical windows of n + 2·{gapBound sc0 (-16)} letters, per read): all diagonals {pf.clsAll} in {pf.clsAllC} classes ({pf.clsAllM} in multi-copy classes); passing kfilt {pf.clsPass} in {pf.clsPassC} classes ({pf.clsPassM} in multi-copy classes)"
  say s!"  reads > 1 ms: phase-1 kernel alone at all {pf.slowKAnc} anchors: cap 12 {secs 0 pf.slowK12Ns} s, cap 16 {secs 0 pf.slowK16Ns} s"
  say s!"  reads > 1 ms: lookups alone {secs 0 pf.slowLkNs} s, lookups + chromosome slices {secs 0 pf.slowSlNs} s"
  say s!"  reads > 1 ms: diags only {secs 0 pf.slowDdNs} s, diags + seed-count (suppA) only {secs 0 pf.slowSuppNs} s, diags + suppA + unlook (no fine) {secs 0 pf.slowUnNs} s, passing {pf.slowUnPass}"
  say s!"  stage K only (cap 16) {secs 0 pf.kOnlyNs} s vs stages K/B {secs 0 pf.kbNs} s; prototype B through kfilt at P: {secs 0 pf.bFiltNs} s; word kfilt: {secs 0 pf.bWordNs} s (of which stage K + diagsB + word filter, no stage B: {secs 0 pf.bNoBNs} s; stage K + diagsB only: {secs 0 pf.bDiagNs} s)"
  say s!"  reads reaching stage B: {pf.bReads} (none at P: {pf.bNone}); stage-B diagonals {pf.bDiags}, passing kfilt at P {pf.bPass}"
  let tops := pf.bTopNs.qsort (· > ·)
  say s!"  stage-K/B time of stage-B reads, top 10 (ms): {(tops.extract 0 10).map (· / 1000000)}; sum {secs 0 (tops.foldl (· + ·) 0)} s"
  say s!"  best penalty histogram (0..16, 17 = none): {pf.penHist}"
  say s!"  lookups per read histogram (0..23, 24+): {pf.lkHist}"

/-- `f` over `xs` on `n` dedicated tasks, item `i` on task `i % n` (strided, so the few
very slow pairs spread over the tasks), results in the order of `xs`. -/
def parStrided {α β : Type} [Inhabited α] [Inhabited β] (n : Nat) (f : α → β) (xs : Array α) : Array β :=
  let n := max n 1
  let ts := (List.range n).map fun t =>
    Task.spawn (prio := .dedicated) fun _ =>
      ((List.range ((xs.size + n - 1 - t) / n)).map fun i => f xs[t + i * n]!).toArray
  let rs := ts.toArray.map Task.get
  (Array.range xs.size).map fun i => rs[i % n]![i / n]!

/-- `f` over `xs` on `n` dedicated workers taking the next item from a shared counter
(dynamic balance: a slow pair holds up only its own worker), results in the order of `xs`. -/
def parQueue {α β : Type} [Inhabited α] [Inhabited β] (n : Nat) (f : α → β) (xs : Array α) : IO (Array β) := do
  let ctr ← IO.mkRef 0
  let worker : IO (Array (Nat × β)) := do
    let mut acc : Array (Nat × β) := #[]
    repeat
      let k ← ctr.modifyGet fun i => (i, i + 1)
      if k ≥ xs.size then break
      let y ← (← IO.mkRef (f xs[k]!)).get
      acc := acc.push (k, y)
    return acc
  let ts ← (List.range (max n 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  let mut out : Array β := Array.replicate xs.size default
  for t in ts do
    match ← IO.wait t with
    | .ok rs => for (k, y) in rs do out := out.set! k y
    | .error e => throw e
  return out

/-- `f` over `xs` on `n` dedicated workers, each taking the next chunk of `cs` items
from a shared counter; results in the order of `xs`.  Prints each worker's finish time. -/
def parChunk {α β : Type} [Inhabited α] [Inhabited β] (n cs : Nat) (f : α → β) (xs : Array α) : IO (Array β) := do
  let cs := max cs 1
  let nch := (xs.size + cs - 1) / cs
  let ctr ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  let worker : IO (Array (Nat × Array β) × Nat) := do
    let mut acc : Array (Nat × Array β) := #[]
    repeat
      let k ← ctr.modifyGet fun i => (i, i + 1)
      if k ≥ nch then break
      let lo := k * cs
      let hi := min xs.size (lo + cs)
      let ys ← (← IO.mkRef ((Array.range (hi - lo)).map fun i => f xs[lo + i]!)).get
      acc := acc.push (lo, ys)
    let t1 ← IO.monoNanosNow
    return (acc, t1 - t0)
  let ts ← (List.range (max n 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  let mut out : Array β := Array.replicate xs.size default
  let mut fin : Array Nat := #[]
  for t in ts do
    match ← IO.wait t with
    | .ok (rs, dt) =>
      fin := fin.push (dt / 1000000)
      for (lo, ys) in rs do
        for i in [0:ys.size] do out := out.set! (lo + i) ys[i]!
    | .error e => throw e
  IO.eprintln s!"  workers finished at (ms): {fin}"
  return out

/-- Bench estimate for the draft `pairSpecU`: per pair, one thread, at the pass-1 caps: genome
search time of each mate, and region search time of each mate near the other's genome hit (when it
has one).  TSV: idx n1 n2 c1 c2 tg1 tg2 st1 st2 tr1 tr2 rp1 rp2 (ns; st 0 none / 1 hit / 2 tie). -/
def uprofRun (rcfg : RouteCfg) (kK : PassKer) (pk : PkMz) (upN : Nat) (uout : String)
    (r1 r2 : Array ByteArray) : IO Unit := do
  let h ← IO.FS.Handle.mk uout .write
  for k in [0:min upN r1.size] do
    let R1 := r1[k]!
    let R2 := r2[k]!
    let P1 := rcfg.cap1 R1.size
    let P2 := rcfg.cap1 R2.size
    if !(fastT P1 R1 && fastT P2 R2) then continue
    let s1 := kK.prep R1
    let s2 := kK.prep R2
    let t0 ← IO.monoNanosNow
    let m1 ← (← IO.mkRef (kK.mate P1 R1 s1)).get
    let t1 ← IO.monoNanosNow
    let m2 ← (← IO.mkRef (kK.mate P2 R2 s2)).get
    let t2 ← IO.monoNanosNow
    let st1 : Nat := if m1.1.isSome then 1 else if m1.2 then 2 else 0
    let st2 : Nat := if m2.1.isSome then 1 else if m2.2 then 2 else 0
    let mut tr1 := 0
    let mut rp1 := 0
    let mut tr2 := 0
    let mut rp2 := 0
    if let some b := m2.1 then
      let u0 ← IO.monoNanosNow
      rp1 ← (← IO.mkRef (kK.region P1 R1 b.1)).get
      tr1 := (← IO.monoNanosNow) - u0
    if let some a := m1.1 then
      let u0 ← IO.monoNanosNow
      rp2 ← (← IO.mkRef (kK.region P2 R2 a.1)).get
      tr2 := (← IO.monoNanosNow) - u0
    h.putStrLn s!"{k}\t{R1.size}\t{R2.size}\t{kK.cost P1 s1}\t{kK.cost P2 s2}\t{t1 - t0}\t{t2 - t1}\t{st1}\t{st2}\t{tr1}\t{tr2}\t{rp1}\t{rp2}"
  h.flush

/-- Proper-pair mode (`pairUKPR`, pairUKP_mz_eq): per pair, one thread, its time by class
(how many mates have over 1000 seed anchors over both strands: 0 / 1 / 2 = both repeat), with
kept and `pairTie` counts per class. -/
def ukProf (f : ByteArray → ByteArray → Option PairHit × Bool) (anch : ByteArray → Nat) (N : Nat)
    (r1 r2 : Array ByteArray) : IO Unit := do
  let out ← IO.getEnv "WG_UKOUT"
  let h? ← match out with
    | some p => some <$> IO.FS.Handle.mk p IO.FS.Mode.write
    | none => pure none
  let mut tot : Array Nat := #[0, 0, 0]
  let mut cnt : Array Nat := #[0, 0, 0]
  let mut kept : Array Nat := #[0, 0, 0]
  let mut tie : Array Nat := #[0, 0, 0]
  for k in [0:min N r1.size] do
    let R1 := r1[k]!
    let R2 := r2[k]!
    let cl := (if 1000 < anch R1 then 1 else 0) + (if 1000 < anch R2 then 1 else 0)
    let t0 ← IO.monoNanosNow
    let r ← (← IO.mkRef (f R1 R2)).get
    let t1 ← IO.monoNanosNow
    tot := tot.modify cl (· + (t1 - t0))
    cnt := cnt.modify cl (· + 1)
    if r.1.isSome then kept := kept.modify cl (· + 1)
    else if r.2 then tie := tie.modify cl (· + 1)
    if let some h := h? then
      h.putStrLn s!"{k}\t{R1.size}\t{R2.size}\t{cl}\t{t1 - t0}\t{if r.1.isSome then "mapped" else if r.2 then "pairTie" else "none"}"
  for cl in [0:3] do
    say s!"UKPROF class {cl} (mates over 1000 anchors): pairs {cnt[cl]!}, {secs 0 tot[cl]!} s, kept {kept[cl]!}, pairTie {tie[cl]!}"
  let all := tot.foldl (· + ·) 0
  say s!"UKPROF all: pairs {cnt.foldl (· + ·) 0}, {secs 0 all} s; both-repeat share {Float.ofNat tot[2]! / Float.ofNat (max all 1)}"

/-- Stage times of one `hitsAtKP` call (as `hitsSK`, timed): lookups, slices + diagonals,
filter, kernels; counts of diagonals, filter passes, kernel calls. -/
structure HDet where
  tLook : Nat := 0
  tDiag : Nat := 0
  tFilt : Nat := 0
  tKer : Nat := 0
  nAnch : Nat := 0
  nDiag : Nat := 0
  nPass : Nat := 0
  nKer : Nat := 0
  nHit : Nat := 0
  calls : Nat := 0
  byCap : Array (Nat × Nat × Nat) := Array.replicate 5 (0, 0, 0)

def hitsSKT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (d : HDet) : IO HDet := do
  let mut d := d
  let t0 ← IO.monoNanosNow
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk ← (← IO.mkRef (J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!))).get
  let us := unseen m J
  let t1 ← IO.monoNanosNow
  d := { d with tLook := d.tLook + (t1 - t0), nAnch := d.nAnch + lk.foldl (fun x a => x + a.2.size) 0 }
  for c in [0:n] do
    let a0 ← IO.monoNanosNow
    let acc := slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)
    let ds ← (← IO.mkRef (diags acc)).get
    let a1 ← IO.monoNanosNow
    let pass ← (← IO.mkRef (ds.filter fun D => kfiltV K Rs pgs2[t + c]! acc us Ls lim (initP lim) D)).get
    let a2 ← IO.monoNanosNow
    let hs ← (← IO.mkRef (pass.flatMap fun D => (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst Rs.size D sh ∧ 0 ≤ wlen Rs.size sh then
          let k := kerHKG Rs K pgs2 pgs2 (t + c) (dst Rs.size D sh).toNat (wlen Rs.size sh).toNat lim
          if k ≤ lim then some k else none
        else none)).get
    let a3 ← IO.monoNanosNow
    d := { d with tDiag := d.tDiag + (a1 - a0) }
    d := { d with tFilt := d.tFilt + (a2 - a1) }
    d := { d with tKer := d.tKer + (a3 - a2) }
    d := { d with nDiag := d.nDiag + ds.length }
    d := { d with nPass := d.nPass + pass.length }
    d := { d with nKer := d.nKer + pass.length * (shapesAt lim).length }
    d := { d with nHit := d.nHit + hs.length }
  return d

def hitsKPT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (lim : Nat) (d : HDet) : IO HDet := do
  if fastT lim R then
    let n := pgs.size
    let t0 ← IO.monoNanosNow
    let n0 := d.nDiag
    let d ← hitsSKT ix G offs (pgs ++ pgs) n 0 lim R d
    let d ← hitsSKT ix G offs (pgs ++ pgs) n n lim (revCompK R) d
    let t1 ← IO.monoNanosNow
    let i := min (lim / 4) 4
    let d := { d with byCap := d.byCap.modify i fun x => (x.1 + 1, x.2.1 + (t1 - t0), x.2.2 + (d.nDiag - n0)) }
    return { d with calls := d.calls + 1 }
  else return d

/-- Mode U on both-repeat pairs, the ladder traced: time in the hit lists (and their stages,
`hitsKPT`) vs the pairing (`properPairs` / `topW` / `bestPairD`), hit-list sizes, exit rung. -/
def ukDet {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (offs : Array Nat) (pgs : Array PGen)
    (dc : Nat → Nat) (sl lo hi : Nat) (penOf : ByteArray → Nat) (a1f : ByteArray → ByteArray → Bool)
    (anch : ByteArray → Nat) (N : Nat) (r1 r2 : Array ByteArray) : IO Unit := do
  let mut tH := 0
  let mut tP := 0
  let mut nH := 0
  let mut sLen := 0
  let mut mLen := 0
  let mut nPr := 0
  let mut mPr := 0
  let mut np := 0
  let mut exits : Array Nat := Array.replicate 7 0
  let mut d : HDet := {}
  let mut tC := 0
  let mut tF := 0
  let mut nF := 0
  for k in [0:min N r1.size] do
    let R1 := r1[k]!
    let R2 := r2[k]!
    if !(1000 < anch R1 && 1000 < anch R2) then continue
    np := np + 1
    let P1 := penOf R1
    let P2 := penOf R2
    let f0 ← IO.monoNanosNow
    let a1 ← (← IO.mkRef (a1f R1 R2)).get
    let f1 ← IO.monoNanosNow
    let x1 ← (← IO.mkRef (mapFastGBKP P1 ix ByteArray.empty offs pgs R1)).get
    let x2 ← (← IO.mkRef (if x1.isSome then mapFastGBKP P2 ix ByteArray.empty offs pgs R2 else none)).get
    let f2 ← IO.monoNanosNow
    tC := tC + (f1 - f0); tF := tF + (f2 - f1)
    if x1.isSome && x2.isSome then nF := nF + 1
    let mut rung := 0
    let mut fin := false
    for c in capsU do
      if fin then break
      rung := rung + 1
      let c1 := min c P1
      let c2 := min c P2
      let hfT := fun (b : Bool) (cc : Nat) => do
        let t0 ← IO.monoNanosNow
        let l ← (← IO.mkRef (hitsKPF ix ByteArray.empty offs pgs (if b then R1 else R2) cc)).get
        let t1 ← IO.monoNanosNow
        return (l, t1 - t0)
      let (hA, ta) ← hfT a1 (if a1 then c1 else c2)
      tH := tH + ta; nH := nH + 1; sLen := sLen + hA.length; mLen := max mLen hA.length
      d ← hitsKPT ix ByteArray.empty offs pgs (if a1 then R1 else R2) (if a1 then c1 else c2) d
      if hA.isEmpty then
        if (if a1 then P1 ≤ c1 else P2 ≤ c2) then fin := true
        continue
      let (hB, tb) ← hfT (!a1) (if a1 then c2 else c1)
      tH := tH + tb; nH := nH + 1; sLen := sLen + hB.length; mLen := max mLen hB.length
      d ← hitsKPT ix ByteArray.empty offs pgs (if a1 then R2 else R1) (if a1 then c2 else c1) d
      let l1 := if a1 then hA else hB
      let l2 := if a1 then hB else hA
      let p0 ← IO.monoNanosNow
      let prs ← (← IO.mkRef (properPairsF sl lo hi l1 l2)).get
      nPr := nPr + prs.length; mPr := max mPr prs.length
      if P1 ≤ c1 ∧ P2 ≤ c2 then
        let _ ← (← IO.mkRef (bestOfPairs dc prs)).get
        tP := tP + ((← IO.monoNanosNow) - p0); fin := true
      else
        match topW dc prs with
        | none => tP := tP + ((← IO.monoNanosNow) - p0)
        | some w =>
          let e := (-(pairScoreD dc w)).toNat
          if (P1 ≤ c1 ∨ e ≤ c1) ∧ (P2 ≤ c2 ∨ e ≤ c2) then
            let _ ← (← IO.mkRef (bestOfPairs dc prs)).get
            tP := tP + ((← IO.monoNanosNow) - p0)
          else
            tP := tP + ((← IO.monoNanosNow) - p0)
            let (x1, t1) ← hfT true (min P1 e)
            let (x2, t2) ← hfT false (min P2 e)
            tH := tH + t1 + t2; nH := nH + 2
            let q0 ← IO.monoNanosNow
            let _ ← (← IO.mkRef (bestPairF dc sl lo hi x1 x2)).get
            tP := tP + ((← IO.monoNanosNow) - q0)
            rung := rung + 1
          fin := true
    exits := exits.modify (min rung 6) (· + 1)
  say s!"UKDET both-repeat pairs {np}: hits {secs 0 tH} s in {nH} lists (mean len {sLen / max nH 1}, max {mLen}); pairing {secs 0 tP} s (proper pairs total {nPr}, max {mPr}); exit rung {exits}"
  say s!"UKDET stages ({d.calls} calls): look {secs 0 d.tLook} s, slices+diags {secs 0 d.tDiag} s, filter {secs 0 d.tFilt} s, kernels {secs 0 d.tKer} s; anchors {d.nAnch}, diags {d.nDiag}, passed {d.nPass}, kernel calls {d.nKer}, hits {d.nHit}"
  say s!"UKDET by cap 0/4/8/12/16 (calls, ns, diags): {d.byCap}"
  say s!"UKDET costP {secs 0 tC} s, fast path {secs 0 tF} s (both mates unique {nF})"

/-- Map every read set with each mode and task count; dumps and timings. -/
def runSets (modes : List (String × (ByteArray → ByteArray → PairOut))) (okLen : ByteArray → Bool)
    (prof : List (String × (ByteArray → Prof → IO Prof)))
    (margF : Option (ByteArray → (Placement × Int) → Nat → Nat × Nat) := none)
    (tally : List (String × (ByteArray → ByteArray → String)) := [])
    (pprof : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := [])
    (xdump : List (String × (ByteArray → ByteArray → String)) := []) : IO Unit := do
  -- WG_TASKS: comma list of `tasks` or `tasks/chunk` (chunk 0 = strided)
  let taskL := ((← IO.getEnv "WG_TASKS").getD "1").splitOn "," |>.map fun s => match s.splitOn "/" with
    | [a, c] => (a.toNat!, some c.toNat!)
    | _ => (s.toNat!, none)
  let sets := ((← IO.getEnv "WG_READS").getD "").splitOn ";" |>.filter (· ≠ "")
  let outDir := (← IO.getEnv "WG_OUT").getD ""
  for st in sets do
    let [name, rest] := st.splitOn "=" | throw (IO.userError "WG_READS: name=r1:r2:limit;...")
    let [p1, p2, lim] := rest.splitOn ":" | throw (IO.userError "WG_READS: name=r1:r2:limit;...")
    let m1 ← readMates p1
    let m2 ← readMates p2
    if m1.size != m2.size then throw (IO.userError s!"{p1}: {m1.size} records, {p2}: {m2.size}")
    -- WG_TRIMOUT=prefix: write the trimmed mates once (prefix_R1.txt / _R2.txt) for later runs
    if let some pre ← IO.getEnv "WG_TRIMOUT" then
      writeMates s!"{pre}_R1.txt" m1
      writeMates s!"{pre}_R2.txt" m2
      say s!"trimmed mates written to {pre}_R1.txt / _R2.txt"
    let n := if lim.toNat! == 0 then m1.size else min m1.size lim.toNat!
    let trimmed := (Array.range n).filter fun i => m1[i]!.isNone || m2[i]!.isNone
    let idx := (Array.range n).filter fun i => match m1[i]!, m2[i]! with
      | some a, some b => okLen a && okLen b
      | _, _ => false
    let r1 := idx.map fun i => m1[i]!.get!
    let r2 := idx.map fun i => m2[i]!.get!
    let rk := Array.range idx.size
    for (lab, pp) in pprof do
      say s!"pair profile {lab}"
      pp r1 r2
    say s!"set {name}: pairs {n}, trimmed away {trimmed.size}, both mates taken by the mapper {idx.size}; {← rss}"
    let plim ← envN "WG_PROF_LIM" rk.size
    for (lab, pr) in prof do
      let mut pf : Prof := {}
      for k in rk.extract 0 plim do
        pf ← pr r1[k]! pf
        pf ← pr r2[k]! pf
      say s!"profile {lab}"
      showProf pf
    let top ← envN "WG_TOP" 0
    if top > 0 then
      for (mode, f) in modes do
        let mut ts : Array (Nat × Nat) := #[]
        let mut tot := 0
        for k in rk.extract 0 plim do
          let u0 ← IO.monoNanosNow
          let o ← (← IO.mkRef (if u0 == 0 then none else f r1[k]! r2[k]!)).get
          let u1 ← IO.monoNanosNow
          ts := ts.push (u1 - u0, k)
          tot := tot + (u1 - u0)
          if o.isSome && u1 == 0 then say ""
        let srt := ts.qsort (fun a b => a.1 > b.1)
        let cum := (srt.extract 0 top).foldl (fun a x => a + x.1) 0
        say s!"top {top} of {ts.size} pairs ({mode}, 1 task): {secs 0 cum} s of {secs 0 tot} s"
        for (t, k) in srt.extract 0 top do
          let o := f r1[k]! r2[k]!
          let os := match o with
            | some (a, b) => s!"{showHit a} | {showHit b}"
            | none => "none"
          say s!"  pair {idx[k]! + 1}: {secs 0 t} s, mates {r1[k]!.size}/{r2[k]!.size}, {os}"
    let chunk ← envN "WG_CHUNK" 16
    -- per-pair text dumps (4 tasks): <WG_OUT>/<label>_<set>.tsv
    for (lab, xf) in xdump do
      let t0 ← IO.monoNanosNow
      let out ← parChunk 4 chunk (fun k => xf r1[k]! r2[k]!) rk
      let t1 ← IO.monoNanosNow
      say s!"dump {lab} {name}: {secs t0 t1} s (4 tasks)"
      if outDir != "" then
        let mut res : Array String := Array.replicate n "none\n"
        for (i, x) in idx.zip out do res := res.set! i (x ++ "\n")
        IO.FS.writeFile s!"{outDir}/{lab}_{name}.tsv" (String.join ((Array.range n).toList.map fun i => s!"p{i + 1}\t{res[i]!}"))
    for (mode, f) in modes do
      let g (k : Nat) : PairOut := f r1[k]! r2[k]!
      let mut first : Option (Array PairOut) := none
      for (tasks, ch) in taskL do
        let chunk := ch.getD chunk
        let c3 ← cpuTicks
        let t3 ← IO.monoNanosNow
        let out ← if t3 == 1 then pure #[] else
          if tasks > 1 && chunk > 0 then parChunk tasks chunk g rk
          else (← IO.mkRef (if tasks ≤ 1 then rk.map g else parStrided tasks g rk)).get
        let t4 ← IO.monoNanosNow
        let c4 ← cpuTicks
        say s!"RESULT set {name} mode {mode} tasks {tasks} chunk {chunk}: mapped {idx.size} pairs, kept {(out.filter (·.isSome)).size}, {secs t3 t4} s, pairs/s {Float.ofNat idx.size / secs t3 t4}, cpu {Float.ofNat (c4.1 - c3.1) / 100} s, host steal {Float.ofNat (c4.2 - c3.2) / 100} cpu-s; {← rss}"
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
          -- WG_MARGIN=k (bench only, NOT proved): per-mate margin of each kept pair, second-best
          -- penalty over placements not overlapping the best window on its strand, searched to
          -- L = min(P, best + k − 1) (k = 0: to P); margin = min(second, L + 1) − best.
          -- Columns: p<i> pen1 margin1 pen2 margin2 min(margin1, margin2) (`none` = pair not kept).
          match margF, (← IO.getEnv "WG_MARGIN") with
          | some mf, some ks =>
            let k := ks.toNat!
            let kp : Array (Nat × (Placement × Int) × (Placement × Int)) := (rk.zip out).filterMap fun (j, x) =>
              x.map fun (a, b) => (j, a, b)
            let gm := fun (i : Nat) => match kp[i]? with
              | some (j, a, b) => (mf r1[j]! a k, mf r2[j]! b k)
              | none => ((0, 0), (0, 0))
            let c5 ← cpuTicks
            let t5 ← IO.monoNanosNow
            let ms ← if tasks > 1 then parChunk tasks chunk gm (Array.range kp.size) else pure ((Array.range kp.size).map gm)
            let t6 ← IO.monoNanosNow
            let c6 ← cpuTicks
            say s!"MARGIN k {k} set {name} mode {mode} tasks {tasks}: {kp.size} kept pairs, {secs t5 t6} s, cpu {Float.ofNat (c6.1 - c5.1) / 100} s; {← rss}"
            if outDir != "" then
              let mut res : Array String := Array.replicate n "none\n"
              for ((j, a, b), (m1, m2)) in kp.zip ms do
                res := res.set! idx[j]! s!"{(-a.2).toNat}\t{m1.2}\t{(-b.2).toNat}\t{m2.2}\t{min m1.2 m2.2}\n"
              let path := s!"{outDir}/{mode}_{name}.margin_k{k}.tsv"
              IO.FS.writeFile path (String.join ((Array.range n).toList.map fun i => s!"p{i + 1}\t{res[i]!}"))
              say s!"margin dump {path}"
          | _, _ => pure ()
    -- tallies (e.g. router pass / reason per pair), 4 tasks, timed
    for (lab, t) in tally do
      let t3 ← IO.monoNanosNow
      let ys ← parChunk 4 chunk (fun k => t r1[k]! r2[k]!) rk
      let t4 ← IO.monoNanosNow
      let srt := ys.qsort (· < ·)
      let mut cnt : Array (String × Nat) := #[]
      for y in srt do
        match cnt.back? with
        | some (z, c) => if z == y then cnt := cnt.pop.push (z, c + 1) else cnt := cnt.push (y, 1)
        | none => cnt := cnt.push (y, 1)
      say s!"TALLY set {name} {lab} ({secs t3 t4} s, 4 tasks): {cnt.toList.map fun (z, c) => s!"{z}={c}"}"

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

/-- FASTA bytes from `i` without the header line and line ends. -/
def stripFa (raw : ByteArray) : ByteArray :=
  let rec skip (i : Nat) : Nat :=
    if h : i < raw.size then (if raw[i] == 10 then i + 1 else skip (i + 1)) else i
  termination_by raw.size - i
  let rec go (i : Nat) (out : ByteArray) : ByteArray :=
    if h : i < raw.size then
      let b := raw[i]
      go (i + 1) (if b == 10 || b == 13 then out else out.push b)
    else out
  termination_by raw.size - i
  go (skip 0) (.emptyWithCapacity raw.size)

/-- The sequence part `[b0, b1)` of a one-record FASTA (after the header line, before
trailing line ends). -/
def faBody (raw : ByteArray) : Nat × Nat :=
  let rec skip (i : Nat) : Nat :=
    if h : i < raw.size then (if raw[i] == 10 then i + 1 else skip (i + 1)) else i
  termination_by raw.size - i
  let rec back (j : Nat) : Nat :=
    match j with
    | 0 => 0
    | j + 1 => if raw[j]! == 10 || raw[j]! == 13 then back j else j + 1
  let b0 := skip 0
  (b0, max b0 (back raw.size))

/-- A line end in `raw[i, j)`. -/
def hasNL (raw : ByteArray) (i j : Nat) : Bool :=
  if h : i < j then (if raw[i]! == 10 || raw[i]! == 13 then true else hasNL raw (i + 1) j) else false
termination_by j - i

/-- All of `L[i, i + 64)` is ACGT. -/
def allAcgt (L : ByteArray) (i : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => acgt L[i]! && allAcgt L (i + 1) k

/-- 16 bytes of 2-bit codes of `L[i, i + 64)` pushed onto `w`. -/
def codes64 (L : ByteArray) (i : Nat) (w : ByteArray) : Nat → ByteArray
  | 0 => w
  | k + 1 =>
    let b := (c2 L[i]! ||| (c2 L[i + 1]! <<< 2) ||| (c2 L[i + 2]! <<< 4) ||| (c2 L[i + 3]! <<< 6)).toUInt8
    codes64 L (i + 4) (w.push b) k

/-- Push letters `L[i, j)` (a whole ACGT block at a block start at once: flag 1, 16 code bytes,
as 64 `PB.push` would). -/
def pushLoop (L : ByteArray) (i j : Nat) (s : PB) : PB :=
  if h : i < j then
    if s.n % 64 == 0 && i + 64 ≤ j && allAcgt L i 64 then
      match s with
      | ⟨n, w, _, _, _, ex, _⟩ =>
        let fp := w.size
        pushLoop L (i + 64) j ⟨n + 64, codes64 L i (w.push 1) 16, 0, 1, fp, ex, L[i + 63]!⟩
    else pushLoop L (i + 1) j (s.push L[i]!)
  else s
termination_by j - i

/-- Runs `ex1 ++ ex2`, the run of `ex1` ending at `a` joined with the one of `ex2` starting there
(same letter), as `PB.push` builds them. -/
def mergeEx (ex1 ex2 : Array UInt32) (a : Nat) : Array UInt32 :=
  if 3 ≤ ex1.size && 3 ≤ ex2.size && ex1[ex1.size - 2]!.toNat == a && ex2[0]!.toNat == a &&
      ex1[ex1.size - 1]! == ex2[2]! then
    (ex1.set! (ex1.size - 2) ex2[1]!) ++ ex2.extract 3 ex2.size
  else ex1 ++ ex2

/-- `s` (at a block start) followed by `t` (built from `s.n` on). -/
def appendPB (s t : PB) : PB :=
  -- taken apart so that `w` is unshared and grows in place
  match s, t with
  | ⟨n, w, _, _, _, ex, _⟩, ⟨n2, w2, cur2, f2, fpos2, ex2, prev2⟩ =>
    let sz := w.size
    ⟨n2, w ++ w2, cur2, f2, sz + fpos2, mergeEx ex ex2 n, prev2⟩

/-- `loadPacked` with each file read whole, stripped, and packed in `k` block-aligned pieces
on dedicated tasks (the same `PGen` as pushing every letter in order). -/
def loadPackedPar (files : List String) (k : Nat) : IO (PGen × Array Nat × Array Nat) := do
  let t0 ← IO.monoNanosNow
  let mut total := 0
  for f in files do total := total + (← System.FilePath.metadata f).byteSize.toNat
  let mut s := PB.init total
  let mut offs : Array Nat := #[]
  let mut tR := 0
  let mut tS := 0
  let mut tP := 0
  -- the next file is read while this one is packed
  let fa := files.toArray
  let mut next ← IO.asTask (IO.FS.readBinFile fa[0]!) .dedicated
  for fi in [0:fa.size] do
    offs := offs.push s.n
    let ta ← IO.monoNanosNow
    let raw ← IO.ofExcept next.get
    if fi + 1 < fa.size then next ← IO.asTask (IO.FS.readBinFile fa[fi + 1]!) .dedicated
    let tb ← IO.monoNanosNow
    let (b0, b1) := faBody raw
    let nlT := (List.range k).map fun t => Task.spawn (prio := .dedicated) fun _ =>
      hasNL raw (b0 + t * ((b1 - b0) / k + 1)) (min b1 (b0 + (t + 1) * ((b1 - b0) / k + 1)))
    let one := !(nlT.any (·.get))
    -- one-line record: pack straight from the file bytes; else strip first
    let L ← (← IO.mkRef (if one then raw else stripFa raw)).get
    let (b0, b1) := if one then (b0, b1) else (0, L.size)
    let tc ← IO.monoNanosNow
    tR := tR + (tb - ta)
    tS := tS + (tc - tb)
    -- letters up to the next block start, in order
    let a0 := min b1 (b0 + (64 - s.n % 64) % 64)
    s := pushLoop L b0 a0 s
    if a0 < b1 then
      let nb := (b1 - a0 + 63) / 64
      let per := (nb + k - 1) / k
      -- only the count goes into the tasks, so `s.w` stays unshared and grows in place
      let n0 := s.n
      let ts := (List.range k).filterMap fun t =>
        let i := a0 + t * per * 64
        let j := min b1 (a0 + (t + 1) * per * 64)
        if i < j then
          some (Task.spawn (prio := .dedicated) fun _ =>
            pushLoop L i j { n := n0 + (i - a0), w := .emptyWithCapacity (17 * (per + 1)) })
        else none
      for tk in ts do s := appendPB s tk.get
    let td ← IO.monoNanosNow
    tP := tP + (td - tc)
  say s!"  read {Float.ofNat tR / 1e9} s, strip {Float.ofNat tS / 1e9} s, pack {Float.ofNat tP / 1e9} s"
  let G := s.finish
  let ns := (Array.range offs.size).map fun c => (offs[c + 1]?.getD G.n) - offs[c]!
  let t1 ← IO.monoNanosNow
  say s!"genome packed ({k} tasks per file): {ns.size} chromosomes, {G.n} letters, {G.w.size + 4 * G.ex.size} bytes ({secs t0 t1} s); {← rss}"
  return (G, offs, ns)

set_option maxHeartbeats 800000 in
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
      let t0 ← IO.monoNanosNow
      -- the index is read while the genome is packed
      let ixT ← if (← IO.getEnv "WG_PACKONLY").isSome then pure (Task.pure (.error (IO.userError "pack only")))
        else IO.asTask (load pre) .dedicated
      let pk := ((← IO.getEnv "WG_PACK").getD "4").toNat!
      -- Default: the packed genome saved by an earlier run (<pre>.pgw/.pgx/.pgc, WG_PKSAVE; .pgw/.pgx as
      -- bench/pack_genome.py writes them) instead of packing the FASTA; trusted only through the index hash
      -- below, which covers G.w, G.ex, n, o and the cuts.  The FASTA is packed instead when WG_FASTA is set,
      -- when <pre>.pgc is missing, and always for WG_CHECK / WG_PACKONLY (the hash is then made from the FASTA).
      let useFa := (← IO.getEnv "WG_FASTA").isSome || (← IO.getEnv "WG_CHECK").isSome ||
        (← IO.getEnv "WG_PACKONLY").isSome || !(← System.FilePath.pathExists (pre ++ ".pgc"))
      let (G, offs, ns) ← if !useFa then do
          say s!"genome: loading the saved packed genome {pre}.pgw/.pgx/.pgc (WG_FASTA=1 packs the FASTA)"
          let m := ((← IO.FS.readFile (pre ++ ".pgc")).trimAscii.toString.splitOn ";").map
            fun (x : String) => ((x.splitOn ",").filter (· ≠ "")).toArray.map String.toNat!
          let [hd, offs, ns] := m | throw (IO.userError s!"{pre}.pgc: bad format")
          let G : PGen := ⟨hd[0]!, hd[1]!, ← readBin (pre ++ ".pgw"), ← readBin (pre ++ ".pgx")⟩
          pure (G, offs, ns)
        else if pk == 0 then loadPacked files else loadPackedPar files pk
      if !cutOk G offs ns then throw (IO.userError "cutOk failed")
      if (← IO.getEnv "WG_PACKONLY").isSome then
        say s!"packed genome hash {hashBytes G.w} {hashBytes G.ex} {G.n}; {← rss}"
        return 0
      let pgs := cutAll G offs ns
      let ix ← IO.ofExcept ixT.get
      let t1 ← IO.monoNanosNow
      say s!"genome packed + index loaded (overlapped) {secs t0 t1} s: {ix.sl.size / ix.sw} entries; {← rss}"
      -- index hash: index files + packed genome + chromosome cuts; stored next to the index once
      -- the full check (check3P) passed on them (WG_CHECK=1), verified on every other run
      let mt ← IO.FS.readFile (pre ++ ".meta")
      let hs := [hashBytes ix.offs, hashBytes ix.sl, hashBytes (← readBin (pre ++ ".runs")), hashBytes G.w,
        hashBytes G.ex, hashBytes mt.toUTF8, hashBytes (String.join ((offs.toList ++ ns.toList).map (s!"{·},"))).toUTF8,
        G.n.toUInt64, G.o.toUInt64]
      let hstr := String.intercalate " " (hs.map fun h => toString h.toNat)
      let t1h ← IO.monoNanosNow
      say s!"index hash ({secs t1 t1h} s): {hstr}"
      let hfile := pre ++ ".hash"
      if (← IO.getEnv "WG_NOCHECK").isSome then
        say "WARNING: index check and hash skipped (WG_NOCHECK): profiling only, not the proved setting"
      else if (← IO.getEnv "WG_CHECK").isSome then
        let ok ← (← IO.mkRef (if t1 == 1 then false else Mz.check3P ix G 4)).get
        let t2 ← IO.monoNanosNow
        say s!"index check (check3P = check2P, 4 tasks): {ok} ({secs t1h t2} s); {← rss}"
        if !ok then throw (IO.userError "index check failed")
        IO.FS.writeFile hfile (hstr ++ "\n")
        say s!"hash of the checked index written to {hfile}"
      else
        let stored ← if ← System.FilePath.pathExists hfile then IO.FS.readFile hfile else pure ""
        if stored.trim != hstr then
          throw (IO.userError s!"index hash differs from {hfile} (or none stored): run once with WG_CHECK=1")
        say s!"index hash = {hfile} (index checked by check3P when the hash was written)"
        if (← IO.getEnv "WG_PKSAVE").isSome then
          IO.FS.writeBinFile (pre ++ ".pgw") G.w
          IO.FS.writeBinFile (pre ++ ".pgx") G.ex
          IO.FS.writeFile (pre ++ ".pgc") s!"{G.n},{G.o};{String.join (offs.toList.map (s!"{·},"))};{String.join (ns.toList.map (s!"{·},"))}\n"
          say s!"packed genome saved to {pre}.pgw/.pgx/.pgc (hash-verified)"
      let pk : PkMz := (ix, G)
      -- pairDispatchP_mz_eq / pairFastGBP_mz_eq_pairSpec; pairDispatchKP_mz_eq / pairFastGBKP_mz_eq_pairSpec
      let fP : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchP lo hi pk offs pgs
        else pairFastGBP P lo hi pk offs pgs
      let fK : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchKP lo hi pk ByteArray.empty offs pgs
        else pairFastGBKP P lo hi pk ByteArray.empty offs pgs
      let ms := ((← IO.getEnv "WG_MODES").getD "P,PK").splitOn ","
      -- pairRegionKP_mz_eq: the cheaper mate first, the other near it first
      let fR : ByteArray → ByteArray → PairOut := pairRegionKP lo hi pk (fun a b => ((pk, a, b) : RgMz)) ByteArray.empty offs pgs
      -- routeKP_ok (codecs/PairRouter.lean): pass 1 = pairRegionKP's kernel with reasons; WG_SHORT (below): mates of
      -- 50–74 letters at −7, 75–99 at −11 (else < 100 too short); WG_PASS2=1: pairs left without a hit
      -- (noHit / noPartner / tooShort) get pass 2 at WG_T2 = "minLen:cap,…" (e.g. 150:20; first match wins)
      -- WG_SHORT: "75" (default) mates of 75–99 letters at −11; "50" (or "1") also 50–74 at −7; "0" off
      let shortE := (← IO.getEnv "WG_SHORT").getD "75"
      let short := shortE == "50" || shortE == "1"
      let short75 := short || shortE == "75"
      -- WG_CAP1="minLen:cap,…" overrides the pass-1 caps (first match wins; shorter mates: cap 12, too short)
      let c1s := ((← IO.getEnv "WG_CAP1").getD "").splitOn "," |>.filter (· ≠ "") |>.map fun x =>
        match x.splitOn ":" with
        | [a, b] => (a.toNat!, b.toNat!)
        | _ => (0, 0)
      let cap1F : Nat → Nat := fun n =>
        if !c1s.isEmpty then (match c1s.find? (fun x => x.1 ≤ n) with | some x => x.2 | none => 12) else
        if 150 ≤ n then 16 else if 100 ≤ n then 12 else if short75 && 75 ≤ n then 11 else if short then 7 else 12
      let t2s := ((← IO.getEnv "WG_T2").getD "150:20").splitOn "," |>.filter (· ≠ "") |>.map fun x =>
        match x.splitOn ":" with
        | [a, b] => (a.toNat!, b.toNat!)
        | _ => (0, 0)
      let cap2F : Nat → Nat := fun n => match t2s.find? (fun x => x.1 ≤ n) with
        | some x => x.2
        | none => 0
      -- WG_ORD=short: a mate under 100 letters (smaller cap) goes over the genome first, the
      -- long mate near it (region + hinted search); else (and by default `cost`) the cheaper lookups
      -- WG_ORD=long: the long mate first, the short one near it
      let ordE := (← IO.getEnv "WG_ORD").getD "cost"
      let ord1 : ByteArray → ByteArray → Option Bool := fun a b =>
        let sh := if ordE == "short" then true else false
        if ordE != "short" && ordE != "long" then none
        else if b.size < 100 && 100 ≤ a.size then some sh
        else if a.size < 100 && 100 ≤ b.size then some !sh
        else none
      let p2on := (← IO.getEnv "WG_PASS2").getD "0" == "1"
      -- WG_P2ORD=cost: pass 2 on noHit pairs orders the mates by lookup cost (default: the other mate first)
      let swap2 := (← IO.getEnv "WG_P2ORD").getD "cost" == "swap"
      -- WG_P2BUDGET=N: pass 2 only when both mates' lookup cost at the pass-2 cap (`costP`) is ≤ N
      let bud ← envN "WG_P2BUDGET" 0
      let cap2F' := cap2F
      -- WG_P2GATE=min: the budget applies to the cheaper mate only (default: both mates)
      let gMin := (← IO.getEnv "WG_P2GATE").getD "both" == "min"
      let gate2 : ByteArray → ByteArray → Bool := fun a b => bud == 0 ||
        (let ca := costP pk (cap2F' a.size) (prepMate pk a : PrepM MzP)
         let cb := costP pk (cap2F' b.size) (prepMate pk b : PrepM MzP)
         if gMin then min ca cb ≤ bud else ca ≤ bud && cb ≤ bud)
      let rcfg : RouteCfg := { cap1 := cap1F, pass2 := p2on, cap2 := cap2F, ord1 := ord1, swap2 := swap2, gate2 := gate2 }
      -- WG_HINT=0: mate B over the genome at its full cap (no region-hit hint; mateH_ok holds either way)
      let hint := (← IO.getEnv "WG_HINT").getD "1" == "1"
      -- WG_JOIN1 / WG_JOIN2 = 1: the pair-level anchor join (`noPairJ`, reason `noPair`) before the
      -- search in pass 1 / pass 2 (`routeKPB_ok`)
      let j1 := (← IO.getEnv "WG_JOIN1").getD "0" == "1"
      let j2 := (← IO.getEnv "WG_JOIN2").getD "0" == "1"
      let kK := kpKerB lo hi pk (fun a b => ((pk, a, b) : RgMz)) ByteArray.empty offs pgs j1 hint
      let kK2 := kpKerB lo hi pk (fun a b => ((pk, a, b) : RgMz)) ByteArray.empty offs pgs j2 hint
      let route (a b : ByteArray) : Routed := routeG rcfg kK kK2 lo hi (some a) (some b)
      let fRT : ByteArray → ByteArray → PairOut := fun a b => (route a b).out.toOpt
      let showR (r : Routed) : String :=
        let m (x : Mate) := match x with | .one => "1" | .two => "2"
        let rs := match r.out with
          | .mapped _ => "mapped"
          | .unmapped (.trimmedAway x) _ => s!"trimmed{m x}"
          | .unmapped (.tooShort x) _ => s!"short{m x}"
          | .unmapped (.noHit x) _ => s!"noHit{m x}"
          | .unmapped (.tie x) _ => s!"tie{m x}"
          | .unmapped (.noPartner x) _ => s!"noPartner{m x}"
          | .unmapped .notProper _ => "notProper"
          | .unmapped .noPair _ => "noPair"
        s!"p{r.pass}:{rs}"
      -- Proper-pair mode U (pairUKPF_mz_eq / pairUKPRF_tie, codecs/PairLadderF.lean): pairSpecUT at the
      -- caps penOf, sl = WG_USL (0), distance cost dcost0 (WG_UDC=1k: dcost1k); fast path, then rungs
      -- capsU, the mate with the cheaper lookups (costP) first
      let usl ← envN "WG_USL" 0
      let udc : Nat → Nat := if (← IO.getEnv "WG_UDC").getD "0" == "1k" then dcost1k else dcost0
      let uR : ByteArray → ByteArray → Option PairHit × Bool := fun a b =>
        let P1 := penOf a
        let P2 := penOf b
        let a1 := !decide (costP pk P2 (prepMate pk b : PrepM MzP) < costP pk P1 (prepMate pk a : PrepM MzP))
        pairUKPRF udc usl lo hi P1 P2 capsU a1 pk ByteArray.empty offs pgs a b
      let fU : ByteArray → ByteArray → PairOut := fun a b => (uR a b).1
      -- Mode H (pairUKH_mz_eq / pairUKH_tie, codecs/PairHybrid.lean): pairRegionKP (mode PR) first, kept when
      -- proper under properPairU at distance cost 0; else the ladder.  Same answers as mode U.
      let hR : ByteArray → ByteArray → Option PairHit × Bool := fun a b =>
        let a1 := !decide (costP pk (penOf b) (prepMate pk b : PrepM MzP) < costP pk (penOf a) (prepMate pk a : PrepM MzP))
        pairUKH udc usl lo hi capsU a1 pk (fun x y => ((pk, x, y) : RgMz)) ByteArray.empty offs pgs a b
      let fH : ByteArray → ByteArray → PairOut := fun a b => (hR a b).1
      -- Mode HN (pairUKHN_eq, codecs/PairNear.lean): mode H with the second-searched mate enumerated
      -- only on diagonals near the first mate's hits at each rung.  Same answers as mode H.
      let hnR : ByteArray → ByteArray → Option PairHit × Bool := fun a b =>
        let a1 := !decide (costP pk (penOf b) (prepMate pk b : PrepM MzP) < costP pk (penOf a) (prepMate pk a : PrepM MzP))
        pairUKHN udc usl lo hi capsU a1 pk (fun x y => ((pk, x, y) : RgMz)) ByteArray.empty offs pgs a b
      let fHN : ByteArray → ByteArray → PairOut := fun a b => (hnR a b).1
      -- WG_UKH=1: the kind tally and the profile below run mode H instead of mode U
      let uR0 := uR
      let ukh := (← IO.getEnv "WG_UKH").getD "0"
      let uR := if ukh == "1" then hR else if ukh == "N" then hnR else uR
      let uAnch : ByteArray → Nat := fun R =>
        let s : PrepM MzP := prepMate pk R
        s.ps.foldl (fun x p => x + LookG.size pk p) 0 + s.pr.foldl (fun x p => x + LookG.size pk p) 0
      let modes := ms.filterMap fun m => if m == "P" then some ("P", fP) else if m == "PK" then some ("PK", fK)
        else if m == "PR" then some ("PR", fR) else if m == "RT" then some ("RT", fRT)
        else if m == "U" then some ("U", fU) else if m == "H" then some ("H", fH)
        else if m == "HN" then some ("HN", fHN) else none
      -- Budget experiment (bench only, unproved, not the default): mode PRB<N> = mode PR, but a pair
      -- whose mates' lookup work after the rarest-seed choice (`costP` at the cap, anchors) exceeds N
      -- for either mate is given up (unmapped, reason gaveUp) before any search.  Every reported pair
      -- is still pairRegionKP's answer (= pairSpecT).  HB<N>: the same gate in front of mode H.
      let rlB := fun x y => ((pk, x, y) : RgMz)
      let fRB (N : Nat) : ByteArray → ByteArray → PairOut := fun a b =>
        let P1 := penOf a
        let P2 := penOf b
        let s1 : PrepM MzP := prepMate pk a
        let s2 : PrepM MzP := prepMate pk b
        let c1 := costP pk P1 s1
        let c2 := costP pk P2 s2
        if N < c1 || N < c2 then none
        else if c2 < c1 then
          (pairRegionStep lo hi (mapFastGBKPp P2 pk ByteArray.empty offs pgs b s2)
            (regionNoHitKP P1 lo hi rlB ByteArray.empty offs pgs a)
            (fun _ => mapFastGBKPp P1 pk ByteArray.empty offs pgs a s1)).map fun x => (x.2, x.1)
        else
          pairRegionStep lo hi (mapFastGBKPp P1 pk ByteArray.empty offs pgs a s1)
            (regionNoHitKP P2 lo hi rlB ByteArray.empty offs pgs b)
            (fun _ => mapFastGBKPp P2 pk ByteArray.empty offs pgs b s2)
      let gaveUp (N : Nat) (a b : ByteArray) : Bool :=
        N < costP pk (penOf a) (prepMate pk a : PrepM MzP) || N < costP pk (penOf b) (prepMate pk b : PrepM MzP)
      let fHB (N : Nat) : ByteArray → ByteArray → PairOut := fun a b => if gaveUp N a b then none else fH a b
      -- RTB<N>: the same gate (caps of pass 1, `cap1F`) in front of mode RT, the default
      let gaveUpR (N : Nat) (a b : ByteArray) : Bool :=
        N < costP pk (cap1F a.size) (prepMate pk a : PrepM MzP) || N < costP pk (cap1F b.size) (prepMate pk b : PrepM MzP)
      let fRTB (N : Nat) : ByteArray → ByteArray → PairOut := fun a b => if gaveUpR N a b then none else fRT a b
      -- RTL (bench only, exactness by `mapSpecBoth_mono` as in `mateH`): mode RT with each whole-genome
      -- mate search run as a cap ladder WG_LADDER (default 0,4,8,12): the first rung with any hit
      -- (unique or tie) gives the answer at the full cap; no hit at any rung: the full cap.
      -- WG_LORD=hi: mate A = the one with the larger lookup cost (default: as RT, the cheaper).
      let rungs := ((← IO.getEnv "WG_LADDER").getD "0,4,8,12").splitOn "," |>.filter (· ≠ "") |>.map String.toNat!
      let lord := (← IO.getEnv "WG_LORD").getD "lo"
      let ladM (P : Nat) (R : ByteArray) (s : kK.Prep) : MateR :=
        (rungs.foldr (fun c (k : Unit → MateR) => fun _ =>
          if c < P && fastT c R then
            let x := kK.mate c R s
            if x.1.isSome || x.2 then x else k ()
          else k ()) (fun _ => kK.mate P R s)) ()
      let kL : PassKer := { kK with mate := ladM }
      let ordL : ByteArray → ByteArray → Option Bool := fun a b =>
        if lord == "hi" then
          some (decide (costP pk (cap1F a.size) (prepMate pk a : PrepM MzP) < costP pk (cap1F b.size) (prepMate pk b : PrepM MzP)))
        else none
      let routeL (a b : ByteArray) : Routed := routeG { rcfg with ord1 := ordL } kL kL lo hi (some a) (some b)
      let fRTL : ByteArray → ByteArray → PairOut := fun a b => (routeL a b).out.toOpt
      -- Tiered certificate check (bench only, mode RTX; dump WG_TIEROUT=1 → <WG_OUT>/tiers_<set>.tsv).
      -- Pairs over the RTB gate (`gaveUpR` WG_XBUD; 0 = no gate) skip RT; else RT first (T1).  On the
      -- rest: WG_PG=G, the pair-level guarantee (T1g / T1gm multimapped within G).  G = 4 needs both
      -- mates ≥ 50 bp; otherwise (WG_XZ=1) the guarantee at 0 (mates ≥ 25 bp; suffix z), else
      -- suffix x (not applicable).  Then (default, WG_XBND=1) per mate a proved floor and a re-scored
      -- ceiling from what lean computed (`mateB`): T2 = both mates have a ceiling, else T3.
      -- Earlier designs (off by default): WG_XLAD=1 exact rungs (cap, 12, 8, 4) under the lookup
      -- budget WG_XBUD (`costP`), WG_XPERF=1 mates' perfect hits, WG_XFREE=1 free upper bounds from
      -- the seeds' anchors (buckets ≤ WG_XBK; steps ≤ WG_XG; WG_XTOP diagonals; WG_XDP / WG_XREG DP).
      let xBud ← envN "WG_XBUD" 60000
      let xBK ← envN "WG_XBK" 500
      let xG ← envN "WG_XG" 30
      let xTop ← envN "WG_XTOP" 16
      let xDP := (← IO.getEnv "WG_XDP").getD "1" == "1"
      let xReg := (← IO.getEnv "WG_XREG").getD "1" == "1"
      let xCap ← envN "WG_XCAP" 60
      let nc := pgs.size
      -- WG_PG=G (0 or 4; unset: off): the pair-level guarantee (`pairGX`) on RT's unmapped and gated
      -- pairs; WG_XLAD=1 (default off): budgeted exact rungs (cap, 12, 8, 4) per mate
      -- (else, and when no rung is affordable, the mate's perfect hits: best 0, or best > 0)
      let pgE := (← IO.getEnv "WG_PG").getD ""
      let pgOn := pgE != ""
      let pgG := pgE.toNat?.getD 0
      let xLad := (← IO.getEnv "WG_XLAD").getD "0" == "1"
      -- WG_XPERF=1: mate-level perfect-hit search (off: a mate without another bound gets st N)
      let xPerf := (← IO.getEnv "WG_XPERF").getD "0" == "1"
      -- WG_XFREE=1: the earlier free upper bounds (anchors, chains, DP)
      let xFree := (← IO.getEnv "WG_XFREE").getD "0" == "1"
      -- WG_XBND=1 (default, used when the three above are off): proved floors and a re-scored ceiling
      -- per mate (`mateB`); rarest seed's bucket ≤ WG_XCK, at most WG_XCT diagonals
      let xBnd := (← IO.getEnv "WG_XBND").getD "1" == "1"
      let xOld := xLad || xPerf || xFree
      let xCK ← envN "WG_XCK" 500
      let xCT ← envN "WG_XCT" 16
      let ladR (R : ByteArray) (s : PrepM MzP) (cap : Nat) : Option Nat :=
        if !xLad then none else
        ([cap, 12, 8, 4].filter (· ≤ cap)).find? fun c => fastT c R && (xBud == 0 || costP pk c s ≤ xBud)
      let upX (R : ByteArray) (s : PrepM MzP) (part : Option Placement) (x : MateX) : MateX := Id.run do
        let n := R.size
        let A := (anchorsX pk offs pgs R s xBK).qsort keyLt
        let (bU, bC, sp) := chainX n pgs A xG
        let mut x := { x with pU := bU, pC := bC }
        let mut best : Option (Nat × Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := none
        if let some (v, D, mm) := hamX R s.Rr pgs A xTop then
          x := { x with pH := 4 * mm }
          best := some (v, D - n, n, 4 * mm, [(AlignmentSpec.Step.diag, n)])
        if xDP && bC < 1000000 && sp.2.1 != sp.2.2 then
          let (v, d0, d1) := sp
          let Rx := if v < nc then R else s.Rr
          if let some (st, len, p, runs) := semiDP Rx pgs[v % nc]! (d0 - n - 8) (d1 + 8) then
            x := { x with pD := p }
            if best.all (fun b => p < b.2.2.2.1) then best := some (v, st, len, p, runs)
        if xReg then
          if let some pp := part then
            let w := regionB xCap lo hi n pp
            let v := if pp.2 == Strand.rev then pp.1.chr else nc + pp.1.chr
            let Rx := if v < nc then R else s.Rr
            if let some (st, len, p, runs) := regionX Rx pgs[pp.1.chr]! w.1 w.2 11 ((xCap - 6) / 2) 2 then
              x := { x with pR := p }
              if best.all (fun b => p < b.2.2.2.1) then best := some (v, st, len, p, runs)
        match best with
        | some (v, st, len, p, runs) =>
          let Rx := if v < nc then R else s.Rr
          let ok := rescoreRuns Rx pgs[v % nc]! st len runs == some (-(p : Int))
          return { x with pl := some (decB nc ⟨v, st, len⟩, -(p : Int)), rs := ok }
        | none => return x
      let ladM (R : ByteArray) (s : PrepM MzP) (known : Bool) (kn : Option (Placement × Int))
          (perf : Option (Array (Nat × Nat))) : MateX :=
        let cap := cap1F R.size
        if known then { st := "O", cap := cap, cd := cap } else
        if let some a := kn then { st := "U", cap := cap, cd := cap, pen := (-a.2).toNat, pl := some a } else
        if !fastT 0 R then { st := "S", cap := cap } else
        match ladR R s cap with
        | some rg =>
          let b := mapChromsGBFG (kerHKG R s.K1 (pgs ++ pgs) (pgs ++ pgs)) (kerHKG s.Rr s.K2 (pgs ++ pgs) (pgs ++ pgs))
            rg pk ByteArray.empty offs pgs R s.Rr s.ps s.pr
          if b.pen ≤ rg then { st := (if b.amb then "T" else "U"), cap := cap, cd := rg, pen := b.pen, pl := some (decB nc ⟨b.chr, b.st, b.len⟩, -(b.pen : Int)) }
          else { st := "O", cap := cap, cd := rg }
        | none =>
          match perf with
          | none => { st := "N", cap := cap }
          | some perf =>
          if perf.isEmpty then { st := "O", cap := cap, cd := 0 }
          else { st := (if perf.size ≥ 2 then "T" else "U"), cap := cap, cd := 0, pen := 0, pl := some (decB nc ⟨perf[0]!.1, perf[0]!.2, R.size⟩, 0) }
      -- the rest of the tiered check, from RT's reason (none: RT given up by the budget gate)
      let rtxU (a b : ByteArray) (s1 s2 : PrepM MzP) (rk : Option (Reason × Option (Placement × Int)))
          (p1 p2 : Option (Array (Nat × Nat))) : String × MateX × MateX :=
        let nh1 := match rk with | some (.noHit .one, _) => true | _ => false
        let nh2 := match rk with | some (.noHit .two, _) => true | _ => false
        -- noPartner: RT's unique best of the other mate (at its cap) is kept
        let k1 := match rk with | some (.noPartner .two, k) => k | _ => none
        let k2 := match rk with | some (.noPartner .one, k) => k | _ => none
        let m1 := ladM a s1 nh1 k1 p1
        let m2 := ladM b s2 nh2 k2 p2
        let part (m : MateX) : Option Placement := if m.st == "U" || m.st == "T" then m.pl.map (·.1) else none
        let m1' := if xFree && (m1.st == "O" || m1.st == "N") then upX a s1 (part m2) m1 else m1
        let m2' := if xFree && (m2.st == "O" || m2.st == "N") then upX b s2 (part m1) m2 else m2
        let ov := [m1', m2'].filter (·.st == "O")
        let tier :=
          if m1'.st == "S" || m2'.st == "S" || m1'.st == "N" || m2'.st == "N" then "T3"
          else if ov.isEmpty then
            (if m1'.st == "T" || m2'.st == "T" then "T1t"
             else match m1'.pl, m2'.pl with
               | some x, some y => if properPair lo hi x.1 y.1 then "T1" else "T1d"
               | _, _ => "T1d")
          else if ov.all (fun m => m.cd == m.cap && m.pl.isSome && m.rs) then "T2" else "T3"
        (tier, m1', m2')
      -- Bounds per mate from what lean computes (WG_XBND=1).  Floor `cd` = the largest of: pU = 4·empty
      -- blocks on the weaker strand (`floor_look`); pD = RT's cap + 1 when RT found no hit for the mate;
      -- pC = the guarantee's completed enumeration of this mate (`floor_enum`: G = 4: no hit with ≤ 1
      -- mismatch → 8, best 1 mismatch → 4; G = 0: no perfect hit → 4).  Ceiling pH (1000000 = none), source
      -- pR: 1 RT's unique best (exact), 2 RT's cap (tie / notProper: a hit within the cap), 3 the
      -- enumeration's best verified hit, 4 (WG_XCEIL=1, default; 0 = off) gapless on ≤ WG_XCT diagonals of the rarest seed;
      -- `pl` its alignment when concrete, re-scored by `checkRuns` (`rs`).  st: U (exact), B, S.
      let xCeil := (← IO.getEnv "WG_XCEIL").getD "1" == "1"
      -- WG_XZ=0: no fallback to the guarantee at 0 when G does not apply
      let xZ := (← IO.getEnv "WG_XZ").getD "1" == "1"
      let alnX (R Rr : ByteArray) (v st mm : Nat) : Option (Placement × Int) × Bool :=
        let n := R.size
        let Rx := if v < nc then R else Rr
        (some (decB nc ⟨v, st, n⟩, -((4 * mm : Nat) : Int)),
          rescoreRuns Rx pgs[v % nc]! st n [(AlignmentSpec.Step.diag, n)] == some (-((4 * mm : Nat) : Int)))
      let mateB (R : ByteArray) (s : PrepM MzP) (nh capC : Bool) (kn : Option (Placement × Int))
          (gx : Option (Nat × Option (Nat × Nat × Nat))) : MateX :=
        let cap := cap1F R.size
        if let some a := kn then
          { st := "U", cap := cap, cd := (-a.2).toNat, pen := (-a.2).toNat, pl := some a, pH := (-a.2).toNat, pR := 1 } else
        let fC := if nh then cap + 1 else 0
        let fX := match gx with | some (f, _) => f | none => 0
        let (e0, e1, cb) := if fastT 0 R then boundX pk offs pgs R s xCK (if xCeil then xCT else 0) else (0, 0, none)
        let fE := 4 * min e0 e1
        let st0 := if fastT 0 R then "B" else "S"
        let x : MateX := { st := st0, cap := cap, cd := max (max fE fC) fX, pU := fE, pC := fX, pD := fC, pR := 0 }
        let x := if capC then { x with pH := cap, pR := 2 } else x
        let x := match gx with
          | some (_, some (v, st, mm)) =>
            if 4 * mm < x.pH then let (pl, ok) := alnX R s.Rr v st mm; { x with pH := 4 * mm, pR := 3, pl := pl, rs := ok } else x
          | _ => x
        match cb with
        | some (v, D, mm) =>
          if 4 * mm < x.pH then let (pl, ok) := alnX R s.Rr v (D - R.size) mm; { x with pH := 4 * mm, pR := 4, pl := pl, rs := ok } else x
        | none => x
      -- T2: both mates have a ceiling besides their floors; else T3
      let rtxB (a b : ByteArray) (s1 s2 : PrepM MzP) (rk : Option (Reason × Option (Placement × Int)))
          (g1 g2 : Option (Nat × Option (Nat × Nat × Nat))) : String × MateX × MateX :=
        let nh1 := match rk with | some (.noHit .one, _) => true | _ => false
        let nh2 := match rk with | some (.noHit .two, _) => true | _ => false
        let c1 := match rk with | some (.tie .one, _) => true | some (.notProper, _) => true | _ => false
        let c2 := match rk with | some (.tie .two, _) => true | some (.notProper, _) => true | _ => false
        let k1 := match rk with | some (.noPartner .two, k) => k | _ => none
        let k2 := match rk with | some (.noPartner .one, k) => k | _ => none
        let m1 := mateB a s1 nh1 c1 k1 g1
        let m2 := mateB b s2 nh2 c2 k2 g2
        let ok := fun (m : MateX) => m.pH < 1000000 && m.rs
        (if ok m1 && ok m2 then "T2" else "T3", m1, m2)
      let rtxP (a b : ByteArray) : String × MateX × MateX :=
        let gated := xBud != 0 && gaveUpR xBud a b
        let o := if gated then none else some (route a b)
        match (o.map (·.out) : Option Out) with
        | some (.mapped (x, y)) => ("T1", { st := "U", cap := cap1F a.size, cd := cap1F a.size, pen := (-x.2).toNat, pl := some x },
            { st := "U", cap := cap1F b.size, cd := cap1F b.size, pen := (-y.2).toNat, pl := some y })
        | o' =>
          let rk := match o' with
            | some (.unmapped rs k) => some (rs, k)
            | _ => none
          let s1 : PrepM MzP := prepMate pk a
          let s2 : PrepM MzP := prepMate pk b
          let rest := fun (g1 g2 : Option (Nat × Option (Nat × Nat × Nat))) =>
            if xBnd && !xOld then rtxB a b s1 s2 rk g1 g2 else
            rtxU a b s1 s2 rk (if xPerf then some (perfX pk offs pgs a s1 1).1 else none)
              (if xPerf then some (perfX pk offs pgs b s2 1).1 else none)
          if pgOn then
            let (_, _, res, (swap, done, bx)) := pairGX pk offs pgs usl lo hi a b s1 s2 pgG
            -- the enumerated mate's floor and best hit (`floor_enum`), when its enumeration completed
            let gx : Option (Nat × Option (Nat × Nat × Nat)) :=
              if done then some ((match bx with | some h => 4 * h.2.2 | none => if pgG / 4 == 0 then 4 else 8), bx) else none
            let (g1, g2) := if swap then (none, gx) else (gx, none)
            match res with
            | some (some (x, y, tie)) =>
              (if tie then "T1gm" else "T1g", { st := "P", cap := cap1F a.size, pen := x.2, pl := some (x.1, -(x.2 : Int)) },
                { st := "P", cap := cap1F b.size, pen := y.2, pl := some (y.1, -(y.2 : Int)) })
            | some none => rest g1 g2
            | none =>
              -- G not applicable (a mate under 50 bp): the guarantee at 0 (mates ≥ 25 bp), suffix z
              if pgG > 0 && xZ then
                let (_, _, res0, (swap0, done0, bx0)) := pairGX pk offs pgs usl lo hi a b s1 s2 0
                let gx0 : Option (Nat × Option (Nat × Nat × Nat)) :=
                  if done0 then some ((match bx0 with | some h => 4 * h.2.2 | none => 4), bx0) else none
                let (h1, h2) := if swap0 then (none, gx0) else (gx0, none)
                match res0 with
                | some (some (x, y, tie)) =>
                  (if tie then "T1gmz" else "T1gz", { st := "P", cap := cap1F a.size, pen := x.2, pl := some (x.1, -(x.2 : Int)) },
                    { st := "P", cap := cap1F b.size, pen := y.2, pl := some (y.1, -(y.2 : Int)) })
                | some none => let (t, m1, m2) := rest h1 h2; (t ++ "z", m1, m2)
                | none => let (t, m1, m2) := rest none none; (t ++ "x", m1, m2)
              else let (t, m1, m2) := rest none none; (t ++ "x", m1, m2)
          else rest none none
      -- mode RTX reports the proved pairs only (T1, T1g)
      let fRTX : ByteArray → ByteArray → PairOut := fun a b =>
        let (t, m1, m2) := rtxP a b
        if t != "T1" && t != "T1g" && t != "T1gz" then none else
        match m1.pl, m2.pl with
        | some x, some y => some (x, y)
        | _, _ => none
      let xdump : List (String × (ByteArray → ByteArray → String)) :=
        if (← IO.getEnv "WG_TIEROUT").getD "0" == "1" then
          [("tiers", fun a b => let (t, m1, m2) := rtxP a b; s!"{t}\t{m1.show}\t{m2.show}")] else []
      let modes := modes ++ ms.filterMap fun m =>
        if m == "RTL" then some (m, fRTL) else
        if m == "RTX" then some ("RTX", fRTX) else
        if m.startsWith "RTB" then some (m, fRTB (m.drop 3).toString.toNat!)
        else if m.startsWith "PRB" then some (m, fRB (m.drop 3).toString.toNat!)
        else if m.startsWith "HB" then some (m, fHB (m.drop 2).toString.toNat!) else none
      -- WG_BUDT=N1,N2,…: per pair, given up at N (RTB gate) or not, and what mode RT gave (mapped / tie / other)
      let budT := ((← IO.getEnv "WG_BUDT").getD "").splitOn "," |>.filter (· ≠ "") |>.map String.toNat!
      let okLen : ByteArray → Bool := if ms.all (fun m => m == "RT" || m == "RTL" || m.startsWith "RTB" || m == "RTX") then (fun _ => true) else okLen
      let tally := if (← IO.getEnv "WG_REASONS").getD "0" == "1" then [("router", fun a b => showR (route a b))] else []
      -- WG_UKIND=1: answer kinds of mode U (mapped / pairTie / none)
      let tally := if (← IO.getEnv "WG_UKIND").getD "0" == "1" then tally ++ [("ukind", fun a b =>
        match uR a b with
        | (some _, _) => "mapped"
        | (none, true) => "pairTie"
        | (none, false) => "none")] else tally
      let tally := tally ++ budT.map fun N => (s!"budget{N}", fun a b =>
        if gaveUpR N a b then
          (match (route a b).out with
            | .mapped _ => "lost:mapped"
            | .unmapped (.tie _) _ => "lost:tie"
            | _ => "lost:other")
        else "in")
      -- WG_HUCHK=1: mode H's answer and flag against mode U's
      let tally := if (← IO.getEnv "WG_HUCHK").getD "0" == "1" then tally ++ [("h=u", fun a b =>
        if decide (hR a b = uR0 a b) then "same" else "diff")] else tally
      let tally := if (← IO.getEnv "WG_HUCHK").getD "0" == "N" then tally ++ [("hn=h", fun a b =>
        if decide (hnR a b = hR a b) then "same" else "diff")] else tally
      -- WG_PROF=A:X,A:X,…: profile with X extra lookups once a strand holds A anchors (0:0 = as proved)
      let cfgs := ((← IO.getEnv "WG_PROF").getD "").splitOn "," |>.filter (· ≠ "")
      let prof : List (String × (ByteArray → Prof → IO Prof)) := cfgs.map fun (cf : String) =>
        let ax := cf.splitOn ":"
        let XA := ax[0]!.toNat!
        let XN := (ax[1]?.getD "0").toNat!
        let XF := (ax[2]?.getD "0") == "1"
        let XK := (ax[3]?.getD "0").toNat!
        let XL := (ax[4]?.getD "0").toNat!
        (cf, fun (R : ByteArray) (pf : Prof) => profRead XA XN XF XK XL pk offs pgs (if P == 0 then penOf R else P) R pf)
      -- WG_MARGIN (bench only, NOT proved): second-best over placements not overlapping the best,
      -- by the same search with the window kernels returning "no hit" (cap + 1) on the excluded
      -- windows; exact only while stage B does not run (P ≤ 16: stage B ignores the kernel)
      let margF : ByteArray → (Placement × Int) → Nat → Nat × Nat := fun R a k =>
        let Pm := if P == 0 then penOf R else P
        let bp := (-a.2).toNat
        let L := if k == 0 then Pm else min Pm (bp + k - 1)
        let n := pgs.size
        let bc := if a.1.2 == Strand.fwd then a.1.1.chr else n + a.1.1.chr
        let bst := a.1.1.start
        let bl := a.1.1.len
        let sp := prepMate pk R
        let ex : Ker → Ker := fun kf c st len l =>
          if c == bc && st < bst + bl && bst < st + len then l + 1 else kf c st len l
        let gb := pgs ++ pgs
        let b := mapChromsGBFG (ex (kerHKG R sp.K1 gb gb)) (ex (kerHKG sp.Rr sp.K2 gb gb)) L pk ByteArray.empty
          offs pgs R sp.Rr sp.ps sp.pr
        let sec := min b.pen (L + 1)
        (sec, sec - bp)
      -- WG_RPROF=N: pass-1 cost split of the first N pairs, one thread (bench only): prep + order,
      -- mate A over the genome, region of B, mate B (hinted); by A's cap and outcome
      let rpN ← envN "WG_RPROF" 0
      let rprofL : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := if rpN == 0 then [] else
        [("pass1 split", fun r1 r2 => do
          let mut tab : Std.HashMap String (Array Nat) := {}
          let mut hA : Array Nat := Array.replicate 18 0
          let mut hR : Array Nat := Array.replicate 18 0
          for k in [0:min rpN r1.size] do
            let R1 := r1[k]!
            let R2 := r2[k]!
            let P1 := rcfg.cap1 R1.size
            let P2 := rcfg.cap1 R2.size
            if !fastT P1 R1 || !fastT P2 R2 then continue
            let t0 ← IO.monoNanosNow
            let s1 ← (← IO.mkRef (kK.prep R1)).get
            let s2 ← (← IO.mkRef (kK.prep R2)).get
            let t1 ← IO.monoNanosNow
            let sw ← (← IO.mkRef (decide (kK.cost P2 s2 < kK.cost P1 s1))).get
            let t2 ← IO.monoNanosNow
            let (RA, sA, PA, RB, sB, PB) := if sw then (R2, s2, P2, R1, s1, P1) else (R1, s1, P1, R2, s2, P2)
            let mA ← (← IO.mkRef (kK.mate PA RA sA)).get
            let t3 ← IO.monoNanosNow
            let (rp, t4) ← match mA.1 with
              | some a => do
                let rp ← (← IO.mkRef (kK.region PB RB a.1)).get
                pure (rp, ← IO.monoNanosNow)
              | none => pure (PB + 1, t3)
            let mB ← if mA.1.isSome && rp ≤ PB then (← IO.mkRef (mateH kK PB RB sB rp)).get else pure (none, false)
            let t5 ← IO.monoNanosNow
            let pa := match mA.1 with | some a => (-a.2).toNat | none => 17
            hA := hA.modify (min pa 17) (· + 1)
            if mA.1.isSome then hR := hR.modify (min rp 17) (· + 1)
            let oc := if mA.1.isNone then (if mA.2 then "A tie" else "A none")
              else if rp > PB then "B no region hit" else if mB.1.isSome then "B mapped" else "B none/tie"
            let key := s!"caps {PA}/{PB} {oc}"
            let v := #[1, t1 - t0, t2 - t1, t3 - t2, t4 - t3, t5 - t4]
            tab := tab.insert key (((tab.getD key #[0, 0, 0, 0, 0, 0]).zip v).map fun (a, b) => a + b)
          let rows := tab.toArray.qsort (fun a b => a.2[3]! + a.2[5]! > b.2[3]! + b.2[5]!)
          say "  columns: pairs, prep s, order s, mate A s, region s, mate B s (1 thread)"
          let mut tot : Array Nat := #[0, 0, 0, 0, 0, 0]
          for (key, v) in rows do
            say s!"  {key}: {v[0]!}, {secs 0 v[1]!}, {secs 0 v[2]!}, {secs 0 v[3]!}, {secs 0 v[4]!}, {secs 0 v[5]!}"
            tot := (tot.zip v).map fun (a, b) => a + b
          say s!"  TOTAL: {tot[0]!}, {secs 0 tot[1]!}, {secs 0 tot[2]!}, {secs 0 tot[3]!}, {secs 0 tot[4]!}, {secs 0 tot[5]!}"
          say s!"  mate A best penalty histogram (0..16, 17 = none): {hA}"
          say s!"  region best penalty histogram (0..16, 17 = no hit): {hR}")]
      -- WG_MPROF=N: pass-1 (RT, default) cost of the first N pairs, one thread, by the pair's penalty
      -- (larger of the two mates' answers; unmapped separately): prep, order, mate A and mate B each split
      -- into lookups / phase 1 (without the lookups) / stage K (stage B: caps > 16 only), region search
      let mpN ← envN "WG_MPROF" 0
      let rprofL : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := if mpN == 0 then rprofL else rprofL ++
        [("mason split", fun (r1 r2 : Array ByteArray) => do
          let gb := pgs ++ pgs
          -- one mate over the genome at cap P, timed by part: (lookups, phase 1 incl. lookups, stages K/B, best)
          let split (P : Nat) (R : ByteArray) (s : PrepM MzP) : IO (Array Nat × Nat) := do
            let m := R.size / 25
            let Ls := R.size / m
            let n := pgs.size
            let kf1 := kerHKG R s.K1 gb gb
            let kf2 := kerHKG s.Rr s.K2 gb gb
            let a0 ← IO.monoNanosNow
            let x ← (← IO.mkRef (ilGFG kf1 kf2 pk ByteArray.empty R s.Rr (gb : Array PGen) offs n P Ls s.ps s.pr (2 * m + 1)
              ⟨ordG (s.ps.map (LookG.size pk)) m, [], Array.replicate n []⟩
              ⟨ordG (s.pr.map (LookG.size pk)) m, [], Array.replicate n []⟩ (initP P))).get
            let a1 ← IO.monoNanosNow
            let b := (List.range n).foldl (fun b c => chromKBFG kf1 R (gb : Array PGen) c P x.1.acc[c]! x.1.J b) x.2.2
            let b := (List.range n).foldl (fun b c => chromKBFG kf2 s.Rr (gb : Array PGen) (n + c) P x.2.1.acc[c]! x.2.1.J b) b
            let b ← (← IO.mkRef b).get
            let a2 ← IO.monoNanosNow
            let lk ← (← IO.mkRef ((x.1.J.map fun j => (LookG.look pk ByteArray.empty R (j * Ls) (R.size - j * Ls) s.ps[j]!).size).foldl (· + ·) 0 +
              (x.2.1.J.map fun j => (LookG.look pk ByteArray.empty s.Rr (j * Ls) (s.Rr.size - j * Ls) s.pr[j]!).size).foldl (· + ·) 0)).get
            let a3 ← IO.monoNanosNow
            pure (#[a3 - a2, a1 - a0, a2 - a1, x.1.J.length + x.2.1.J.length + 0 * lk], b.pen)
          -- columns: pairs, RT total, prep, order, lookups, phase 1 (incl. lookups), stage K, region, seeds looked up
          let mut tab : Std.HashMap String (Array Nat) := {}
          for k in [0:min mpN r1.size] do
            let R1 := r1[k]!
            let R2 := r2[k]!
            let P1 := rcfg.cap1 R1.size
            let P2 := rcfg.cap1 R2.size
            if !fastT P1 R1 || !fastT P2 R2 then continue
            let r0 ← IO.monoNanosNow
            let o ← (← IO.mkRef (route R1 R2)).get
            let r1t ← IO.monoNanosNow
            let key := match o.out with
              | .mapped (a, b) =>
                let q := max (-a.2).toNat (-b.2).toNat
                if q == 0 then "0" else if q ≤ 4 then "1-4" else if q ≤ 8 then "5-8" else if q ≤ 12 then "9-12" else "13-16"
              | _ => "unmapped"
            let t0 ← IO.monoNanosNow
            let s1 : PrepM MzP ← (← IO.mkRef (prepMate pk R1)).get
            let s2 : PrepM MzP ← (← IO.mkRef (prepMate pk R2)).get
            let t1 ← IO.monoNanosNow
            let sw ← (← IO.mkRef (decide (costP pk P2 s2 < costP pk P1 s1))).get
            let t2 ← IO.monoNanosNow
            let (RA, sA, PA, RB, sB, PB) := if sw then (R2, s2, P2, R1, s1, P1) else (R1, s1, P1, R2, s2, P2)
            let (vA, penA) ← split PA RA sA
            let mA := mateKP PA pk ByteArray.empty offs pgs RA sA
            let mut v : Array Nat := #[0, r1t - r0, t1 - t0, t2 - t1, vA[0]!, vA[1]!, vA[2]!, 0, vA[3]!]
            if penA ≤ PA then
              match mA.1 with
              | some a =>
                let u0 ← IO.monoNanosNow
                let rp ← (← IO.mkRef (regionPenKP PB lo hi rlB ByteArray.empty offs pgs RB a.1)).get
                let u1 ← IO.monoNanosNow
                v := v.set! 7 (u1 - u0)
                if rp ≤ PB then
                  let h := if rp < PB && fastT rp RB then rp else PB
                  let (vB, penB) ← split h RB sB
                  v := #[v[0]!, v[1]!, v[2]!, v[3]!, v[4]! + vB[0]!, v[5]! + vB[1]!, v[6]! + vB[2]!, v[7]!, v[8]! + vB[3]!]
                  if h < PB && penB > h then
                    let (vC, _) ← split PB RB sB
                    v := #[v[0]!, v[1]!, v[2]!, v[3]!, v[4]! + vC[0]!, v[5]! + vC[1]!, v[6]! + vC[2]!, v[7]!, v[8]! + vC[3]!]
              | none => pure ()
            v := v.set! 0 1
            tab := tab.insert key (((tab.getD key #[0, 0, 0, 0, 0, 0, 0, 0, 0]).zip v).map fun (a, b) => a + b)
          say "  per pair, us (1 thread): RT total | prep, order, lookups, phase 1 w/o lookups, stage K, region | seeds looked up"
          for key in ["0", "1-4", "5-8", "9-12", "13-16", "unmapped"] do
            let v := tab.getD key #[0, 0, 0, 0, 0, 0, 0, 0, 0]
            let c := Float.ofNat (max v[0]! 1)
            let us := fun (x : Nat) => Float.ofNat x / c / 1000
            say s!"  MPROF {key}: pairs {v[0]!}, total {secs 0 v[1]!} s | RT {us v[1]!} | prep {us v[2]!}, order {us v[3]!}, lookups {us v[4]!}, phase1 {us (v[5]! - v[4]!)}, stageK {us v[6]!}, region {us v[7]!} | sum {us (v[2]! + v[3]! + v[5]! + v[6]! + v[7]!)} | seeds {Float.ofNat v[8]! / c}")]
      -- WG_SLOW=N: the first N pairs, one thread; pairs whose RT time exceeds WG_SLOWUS (1000) us are
      -- classified by each mate's whole-genome answer at its pass-1 cap (unique / tie at the best
      -- penalty, none), which mate RT searched first, and RT's answer; times of RT and of RTL
      let slN ← envN "WG_SLOW" 0
      let slUs ← envN "WG_SLOWUS" 1000
      let rprofL : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := if slN == 0 then rprofL else rprofL ++
        [("slow pairs", fun (r1 r2 : Array ByteArray) => do
          let gb := pgs ++ pgs
          let info (P : Nat) (R : ByteArray) (s : PrepM MzP) : String :=
            let b := mapChromsGBFG (kerHKG R s.K1 gb gb) (kerHKG s.Rr s.K2 gb gb) P pk ByteArray.empty offs pgs R s.Rr s.ps s.pr
            if b.pen > P then "none" else
            match decodeP pgs.size P b with
            | some _ => s!"u{b.pen}"
            | none => s!"t{b.pen}"
          let mut tab : Std.HashMap String (Array Nat) := {}
          let mut all : Array Nat := #[0, 0, 0, 0]
          for k in [0:min slN r1.size] do
            let R1 := r1[k]!
            let R2 := r2[k]!
            let t0 ← IO.monoNanosNow
            let o ← (← IO.mkRef (route R1 R2)).get
            let t1 ← IO.monoNanosNow
            let oL ← (← IO.mkRef (routeL R1 R2)).get
            let t2 ← IO.monoNanosNow
            if !(o.out == oL.out) then say s!"  RTL MISMATCH pair {k}"
            all := #[all[0]! + 1, all[1]! + (t1 - t0), all[2]! + (t2 - t1), all[3]!]
            if t1 - t0 ≤ slUs * 1000 then continue
            all := all.set! 3 (all[3]! + 1)
            let P1 := rcfg.cap1 R1.size
            let P2 := rcfg.cap1 R2.size
            let mut ex : Array Nat := #[0, 0, 0, 0, 0, 0]
            let key ← if !fastT P1 R1 || !fastT P2 R2 then pure s!"short | {showR o}" else do
              let s1 : PrepM MzP := prepMate pk R1
              let s2 : PrepM MzP := prepMate pk R2
              let sw := decide (costP pk P2 s2 < costP pk P1 s1)
              let (iA, iB) := if sw then (info P2 R2 s2, info P1 R1 s1) else (info P1 R1 s1, info P2 R2 s2)
              let (RA, sA, PA, RB, sB, PB) := if sw then (R2, s2, P2, R1, s1, P1) else (R1, s1, P1, R2, s2, P2)
              -- times: A at its cap, A at cap 0, B at its cap, B at cap 0 (genome-wide); lookup costs
              let u0 ← IO.monoNanosNow
              let _ ← (← IO.mkRef (kK.mate PA RA sA)).get
              let u1 ← IO.monoNanosNow
              let _ ← (← IO.mkRef (kK.mate 0 RA sA)).get
              let u2 ← IO.monoNanosNow
              let _ ← (← IO.mkRef (kK.mate PB RB sB)).get
              let u3 ← IO.monoNanosNow
              let _ ← (← IO.mkRef (kK.mate 0 RB sB)).get
              let u4 ← IO.monoNanosNow
              ex := #[u1 - u0, u2 - u1, u3 - u2, u4 - u3, costP pk PA sA, costP pk PB sB]
              pure s!"A {iA} B {iB} | {showR o}"
            tab := tab.insert key (((tab.getD key #[0, 0, 0, 0, 0, 0, 0, 0, 0]).zip (#[1, t1 - t0, t2 - t1] ++ ex)).map fun (a, b) => a + b)
          say s!"  SLOW all pairs {all[0]!}: RT {secs 0 all[1]!} s, RTL {secs 0 all[2]!} s; slow (> {slUs} us in RT) {all[3]!}"
          let rows := tab.toArray.qsort (fun a b => a.2[1]! > b.2[1]!)
          for (key, v) in rows do
            say s!"  SLOW {key}: pairs {v[0]!}, RT {secs 0 v[1]!} s, RTL {secs 0 v[2]!} s; A {secs 0 v[3]!} A0 {secs 0 v[4]!} B {secs 0 v[5]!} B0 {secs 0 v[6]!} costA {v[7]!} costB {v[8]!}")]
      -- WG_PPROF=N: pass-2 cost of the first N pairs, one thread, by pass-1 reason: whole pass 2,
      -- and its parts (genome mate at the pass-2 cap and at the pass-1 cap, region, hinted mate B)
      let ppN ← envN "WG_PPROF" 0
      let rcfg1 : RouteCfg := { rcfg with pass2 := false }
      let pprof : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := if ppN == 0 then [] else
        [("pass2", fun r1 r2 => do
          let mut tab : Std.HashMap String (Array Nat) := {}
          let mut dead : Array (ByteArray × Nat × Nat) := #[]
          for k in [0:min ppN r1.size] do
            let R1 := r1[k]!
            let R2 := r2[k]!
            let o ← (← IO.mkRef (routeG rcfg1 kK kK lo hi (some R1) (some R2))).get
            match o.out with
            | .mapped _ => pure ()
            | .unmapped r kn =>
              let A1 := o.c1
              let A2 := o.c2
              let B1 := cap2Of rcfg R1
              let B2 := cap2Of rcfg R2
              if !(rcfg.goOn r && rcfg.gate2 R1 R2 && !(B1 == A1 && B2 == A2)) then pure () else
              let t0 ← IO.monoNanosNow
              let o2 ← (← IO.mkRef (pass2G kK2 rcfg.swap2 A1 A2 B1 B2 r lo hi R1 R2 kn)).get
              let t1 ← IO.monoNanosNow
              -- parts: genome mate `g` (cap Bg, pass-1 cap Ag), region mate `x` (cap Bx)
              let parts : Option (ByteArray × Nat × Nat × ByteArray × Nat × Option (Placement × Int)) := match r, kn with
                | .noHit .one, _ => some (R2, B2, A2, R1, B1, none)
                | .noHit .two, _ => some (R1, B1, A1, R2, B2, none)
                | .noPartner .two, some a => some (R1, B1, A1, R2, B2, some a)
                | .noPartner .one, some a => some (R2, B2, A2, R1, B1, some a)
                | _, _ => none
              let mut v : Array Nat := #[1, t1 - t0, 0, 0, 0, 0, 0, 0]
              if let some (Rg, Bg, Ag, Rx, Bx, kn') := parts then
                let sg := kK.prep Rg
                let sx := kK.prep Rx
                let u0 ← IO.monoNanosNow
                let mg ← if kn'.isSome then pure ((kn'.map fun a => (some a, true)).getD (none, false))
                  else (← IO.mkRef (kK.mate Bg Rg sg)).get
                let u1 ← IO.monoNanosNow
                let _ ← if kn'.isSome || !fastT Ag Rg then pure (none, false) else (← IO.mkRef (kK.mate Ag Rg sg)).get
                let u2 ← IO.monoNanosNow
                let (rp, u3) ← match mg.1 with
                  | some a => do
                    let rp ← (← IO.mkRef (kK.region Bx Rx a.1)).get
                    pure (rp, ← IO.monoNanosNow)
                  | none => pure (Bx + 1, u2)
                let _ ← if rp ≤ Bx then (← IO.mkRef (mateH kK Bx Rx sx rp)).get else pure (none, false)
                let u4 ← IO.monoNanosNow
                v := #[1, t1 - t0, u1 - u0, u2 - u1, u3 - u2, u4 - u3, if mg.1.isSome then 1 else 0,
                  if mg.1.isSome && rp ≤ Bx then 1 else 0]
                if kn'.isNone && mg.1.isNone && !mg.2 && fastT Ag Rg then dead := dead.push (Rg, Bg, Ag)
              -- prototype pair-level absence: all anchors of both mates, joined within the fragment
              let j0 ← IO.monoNanosNow
              let emp ← (← IO.mkRef (noPairJ B1 B2 hi pk ByteArray.empty R1 R2)).get
              let j1 ← IO.monoNanosNow
              let c1 := costP pk B1 (kK.prep R1)
              let c2 := costP pk B2 (kK.prep R2)
              let slow := decide (1000 < max c1 c2)
              v := v ++ #[if emp then 1 else 0, j1 - j0, if slow then 1 else 0, if slow && emp then 1 else 0,
                if slow then t1 - t0 else 0, if emp then t1 - t0 else 0]
              let key := s!"{showR ⟨o.out, 1, A1, A2⟩} -> {showR ⟨o2, 2, B1, B2⟩}"
              tab := tab.insert key (((tab.getD key (Array.replicate 14 0)).zip v).map fun (a, b) => a + b)
          let rows := tab.toArray.qsort (fun a b => a.2[1]! > b.2[1]!)
          let tot := rows.foldl (fun a r => a + r.2[1]!) 0
          say s!"  pass-2 total {secs 0 tot} s over {min ppN r1.size} pairs (1 thread); columns: pairs, pass 2 s, genome mate at cap 2 s, same at cap 1 s, region s, hinted B s, genome mate mapped, region hit"
          for (key, v) in rows do
            say s!"  {key}: {v[0]!}, {secs 0 v[1]!}, {secs 0 v[2]!}, {secs 0 v[3]!}, {secs 0 v[4]!}, {secs 0 v[5]!}, {v[6]!}, {v[7]!} | noPairJ {v[8]!}, join {secs 0 v[9]!} s, slow {v[10]!} ({secs 0 v[12]!} s), slow+noPair {v[11]!}, pass-2 s of noPair {secs 0 v[13]!}"
          let sum := rows.foldl (fun a r => (a.zip r.2).map fun (x, y) => x + y) (Array.replicate 14 0)
          say s!"  ALL: pairs {sum[0]!}, pass 2 {secs 0 sum[1]!} s | noPairJ true {sum[8]!} (pass-2 time of those {secs 0 sum[13]!} s), join time {secs 0 sum[9]!} s, slow (max cost > 1000) {sum[10]!} ({secs 0 sum[12]!} s), slow+noPair {sum[11]!}"
          -- read profile of the genome mates without any hit at the pass-2 cap, at both caps
          let dl := dead.extract 0 (← envN "WG_PPROF_DEAD" 300)
          for hi2 in [true, false] do
            let mut pf : Prof := {}
            for (Rg, Bg, Ag) in dl do
              pf ← profRead 0 0 false 0 0 pk offs pgs (if hi2 then Bg else Ag) Rg pf
            say s!"  no-hit genome mates ({dl.size} of {dead.size}) at the pass-{if hi2 then 2 else 1} cap:"
            showProf pf)]
      -- WG_UPROF=N: `uprofRun` (bench estimate for the draft pairSpecU), TSV to WG_UOUT
      let upN ← envN "WG_UPROF" 0
      let uout := (← IO.getEnv "WG_UOUT").getD "/dev/null"
      let pprof : List (String × (Array ByteArray → Array ByteArray → IO Unit)) :=
        if upN == 0 then pprof else pprof ++ [("uprof", uprofRun rcfg kK pk upN uout)]
      -- WG_UKPROF=N: mode U per pair on one thread, time by class (both-repeat pairs separately)
      let ukN ← envN "WG_UKPROF" 0
      let pprof := if ukN == 0 then pprof else pprof ++ [("ukprof", ukProf uR uAnch ukN)]
      -- WG_UKDET=N: both-repeat pairs of mode U traced (hit lists vs pairing, stages of the hit lists)
      let udN ← envN "WG_UKDET" 0
      let a1f : ByteArray → ByteArray → Bool := fun a b =>
        !decide (costP pk (penOf b) (prepMate pk b : PrepM MzP) < costP pk (penOf a) (prepMate pk a : PrepM MzP))
      let pprof := if udN == 0 then pprof else pprof ++ [("ukdet", ukDet pk offs pgs udc usl lo hi penOf a1f uAnch udN)]
      -- WG_XPROF=N: the tiered check's cost on the first N pairs, one thread: RT on all pairs; on RT's
      -- unmapped pairs prep, ladder search, anchors, chain/U bounds, gapless diagonals, chain DP, region DP
      let xpN ← envN "WG_XPROF" 0
      let pprof := if xpN == 0 then pprof else pprof ++ [("tier split", fun (r1 r2 : Array ByteArray) => do
        -- columns (ns): gate + RT, pair guarantee, mates' perfect hits, ladder, free bounds
        let mut t : Array Nat := Array.replicate 5 0
        let mut cnt := 0
        let mut nG := 0
        let mut nX := 0
        let mut scans : Array Nat := #[]
        let mut gMax := 0
        let mut gWorst := ""
        let mut gBig := 0
        let mut gBigT := 0
        let mut nO := 0
        let tick (i : Nat) (u0 u1 : Nat) (t : Array Nat) : Array Nat := t.set! i (t[i]! + (u1 - u0))
        for k in [0:min xpN r1.size] do
          let a := r1[k]!
          let b := r2[k]!
          let u0 ← IO.monoNanosNow
          let gated ← (← IO.mkRef (xBud != 0 && gaveUpR xBud a b)).get
          let o ← (← IO.mkRef (if gated then none else some (route a b))).get
          let u1 ← IO.monoNanosNow
          t := tick 0 u0 u1 t
          let rk : Option (Option (Reason × Option (Placement × Int))) := match o with
            | none => some none
            | some r => match r.out with
              | .mapped _ => none
              | .unmapped rs k => some (some (rs, k))
          match rk with
          | none => pure ()
          | some rk =>
            cnt := cnt + 1
            if gated then nG := nG + 1
            let s1 : PrepM MzP := prepMate pk a
            let s2 : PrepM MzP := prepMate pk b
            let v0 ← IO.monoNanosNow
            let g ← (← IO.mkRef (if pgOn then some (pairGX pk offs pgs usl lo hi a b s1 s2 pgG) else none)).get
            let v1 ← IO.monoNanosNow
            t := tick 1 v0 v1 t
            let (g1, g2) : Option (Nat × Option (Nat × Nat × Nat)) × Option (Nat × Option (Nat × Nat × Nat)) :=
              match g with
              | some (_, _, _, (swap, done, bx)) =>
                let gx := if done then some ((match bx with | some h => 4 * h.2.2 | none => if pgG / 4 == 0 then 4 else 8), bx) else none
                if swap then (none, gx) else (gx, none)
              | none => (none, none)
            if let some ((ca, cb), ns, res, _) := g then
              scans := scans.push ns
              if res.isNone then nX := nX + 1
              if v1 - v0 > 5000000 then
                gBig := gBig + 1
                gBigT := gBigT + (v1 - v0)
              if v1 - v0 > gMax then
                gMax := v1 - v0
                gWorst := s!"mates {a.size}/{b.size} bp, candidates {ca}/{cb}, checked {ns}, {match res with
                  | some (some (_, _, true)) => "multimapped" | some (some _) => "pair found" | some none => "none ≤ G" | none => "n/a"}"
              if let some (some _) := res then continue
            for (R, s, nh, kn, gx) in [(a, s1, (match rk with | some (.noHit .one, _) => true | _ => false), (match rk with | some (.noPartner .two, k) => k | _ => none), g1),
                (b, s2, (match rk with | some (.noHit .two, _) => true | _ => false), (match rk with | some (.noPartner .one, k) => k | _ => none), g2)] do
              let w0 ← IO.monoNanosNow
              let pf ← (← IO.mkRef (if xPerf then some (perfX pk offs pgs R s 1).1 else none)).get
              let w1 ← IO.monoNanosNow
              let m ← (← IO.mkRef (ladM R s nh kn pf)).get
              let w2 ← IO.monoNanosNow
              t := tick 2 w0 w1 (tick 3 w1 w2 t)
              if xBnd && !xOld then
                let x ← (← IO.mkRef (mateB R s nh false kn gx)).get
                let w3 ← IO.monoNanosNow
                t := tick 4 w2 w3 t
                if x.pl.isSome && w3 == 0 then IO.println ""
              if xFree && (m.st == "O" || m.st == "N") then
                nO := nO + 1
                let x ← (← IO.mkRef (upX R s none m)).get
                let w3 ← IO.monoNanosNow
                t := tick 4 w2 w3 t
                if x.pl.isSome && w3 == 0 then IO.println ""
        let srt := scans.qsort (· < ·)
        let pct (q : Nat) : Nat := if srt.isEmpty then 0 else srt[min (srt.size - 1) (srt.size * q / 100)]!
        say s!"TIERPROF pairs {min xpN r1.size}, RT-unmapped or gated {cnt} (gated {nG}); µs: gate+RT {t[0]! / 1000}, pair guarantee G={pgG} {t[1]! / 1000} (worst {gMax / 1000}: {gWorst}; over 5 ms {gBig} pairs, {gBigT / 1000} µs; not applicable {nX}), candidates checked p50 {pct 50} p99 {pct 99} max {pct 100}; mates' perfect hits {t[2]! / 1000}, ladder {t[3]! / 1000}, {if xBnd && !xOld then "floor/ceiling (mateB)" else "free bounds"} {t[4]! / 1000} ({nO} over mates)"
        let tl := (List.range scans.size).foldl (fun (h : Std.HashMap Nat Nat) i =>
          let v := scans[i]!
          let key := if v ≤ 2 then v else if v ≤ 10 then 10 else if v ≤ 100 then 100 else if v ≤ 1000 then 1000 else 10000
          h.insert key (h.getD key 0 + 1)) {}
        say s!"TIERSCAN candidates checked per pair (bins ≤0,1,2,10,100,1000,more): {[0, 1, 2, 10, 100, 1000, 10000].map fun k => tl.getD k 0}")]
      runSets modes okLen prof (some margF) tally (rprofL ++ pprof) xdump
      return 0
    else throw (IO.userError "mode: build | bytes | map | pmap")
  | _ => throw (IO.userError "usage: whole_genome build|bytes|map|pmap <index_prefix> ...")
