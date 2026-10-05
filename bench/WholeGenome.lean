import MzView
import ParMap
import WgPacked
import PairRegion
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
    return (Array.range (ls.size / 2)).map fun r => some ls[2 * r + 1]!

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

/-- Map every read set with each mode and task count; dumps and timings. -/
def runSets (modes : List (String × (ByteArray → ByteArray → PairOut))) (okLen : ByteArray → Bool)
    (prof : List (String × (ByteArray → Prof → IO Prof))) : IO Unit := do
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
      let (G, offs, ns) ← if pk == 0 then loadPacked files else loadPackedPar files pk
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
      let pk : PkMz := (ix, G)
      -- pairDispatchP_mz_eq / pairFastGBP_mz_eq_pairSpec; pairDispatchKP_mz_eq / pairFastGBKP_mz_eq_pairSpec
      let fP : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchP lo hi pk offs pgs
        else pairFastGBP P lo hi pk offs pgs
      let fK : ByteArray → ByteArray → PairOut := if P == 0 then pairDispatchKP lo hi pk ByteArray.empty offs pgs
        else pairFastGBKP P lo hi pk ByteArray.empty offs pgs
      let ms := ((← IO.getEnv "WG_MODES").getD "P,PK").splitOn ","
      -- pairRegionKP_mz_eq: the cheaper mate first, the other near it first
      let fR : ByteArray → ByteArray → PairOut := pairRegionKP lo hi pk (fun a b => ((pk, a, b) : RgMz)) ByteArray.empty offs pgs
      let modes := ms.filterMap fun m => if m == "P" then some ("P", fP) else if m == "PK" then some ("PK", fK)
        else if m == "PR" then some ("PR", fR) else none
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
      runSets modes okLen prof
      return 0
    else throw (IO.userError "mode: build | bytes | map | pmap")
  | _ => throw (IO.userError "usage: whole_genome build|bytes|map|pmap <index_prefix> ...")
