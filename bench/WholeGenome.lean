import MzView
import ParMap
import WgPacked
import PairRegion
import ReadTrim
import PairRouter
import PairNear

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
    (pprof : List (String × (Array ByteArray → Array ByteArray → IO Unit)) := []) : IO Unit := do
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
      let modes := modes ++ ms.filterMap fun m =>
        if m.startsWith "RTB" then some (m, fRTB (m.drop 3).toString.toNat!)
        else if m.startsWith "PRB" then some (m, fRB (m.drop 3).toString.toNat!)
        else if m.startsWith "HB" then some (m, fHB (m.drop 2).toString.toNat!) else none
      -- WG_BUDT=N1,N2,…: per pair, given up at N (RTB gate) or not, and what mode RT gave (mapped / tie / other)
      let budT := ((← IO.getEnv "WG_BUDT").getD "").splitOn "," |>.filter (· ≠ "") |>.map String.toNat!
      let okLen : ByteArray → Bool := if ms.all (fun m => m == "RT" || m.startsWith "RTB") then (fun _ => true) else okLen
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
      runSets modes okLen prof (some margF) tally (rprofL ++ pprof)
      return 0
    else throw (IO.userError "mode: build | bytes | map | pmap")
  | _ => throw (IO.userError "usage: whole_genome build|bytes|map|pmap <index_prefix> ...")
