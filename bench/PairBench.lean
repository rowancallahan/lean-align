import PairMapper
import PairJoint
import PairInterleave
import PairConcat
import PairUnique
import ParMap

/-!
Benchmark only (unproved IO).  Runs the PROVED pair mapper `Fast.pairFast`
(codecs/PairMapper.lean, `pairFast_eq_pairSpec`) over mate files.

    lake exe pair_bench <genome.fa> <mate1.reads.txt> <mate2.reads.txt> [dump.tsv]
    env: PAIR_MIN (100), PAIR_MAX (1000), PAIR_TASKS (1), PAIR_JOINT (shared-best strand search, pairFastJ),
    PAIR_INTERLEAVE (strands interleaved one lookup at a time, pairFastI),
    PAIR_MZ=k [PAIR_MZ_B=B] [PAIR_MZ_C=c] [PAIR_MZ_W=bytes] [PAIR_MZ_T=t] (minimizer index, with PAIR_JOINT / PAIR_INTERLEAVE: pairFastJ/I_mz_eq_pairSpec),
    PAIR_CONCAT (with PAIR_INTERLEAVE: one index over the concatenated chromosomes, pairFastC),
    PAIR_UNIQ (with PAIR_CONCAT: pair-level uniqueness, pairFastU_eq_pairSpecU against the DRAFT pairSpecU),
    PAIR_HITS=<file> (with PAIR_UNIQ: every hit of every mate, for bench/pair_uniq_ref.py),
    PAIR_DIAG (per-read counts of lookups, anchors, windows scored; pairFastI only)
    With several chromosomes the dump has the chromosome index before each hit.

Dump format = `bench/pair_ref.py` / `PROTO_PAIR` (name, then both hits or none).
-/

open MapSpec

def nextNL (raw : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < raw.size && raw.get! j != 10 do j := j + 1
  return j

def lines (raw : ByteArray) : Array ByteArray := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < raw.size do
    let j := nextNL raw i
    out := out.push (raw.extract i j)
    i := j + 1
  return out

/-- The sequences of a FASTA file, read in 16 MB chunks (peak memory: the genome plus a
chunk, not the file and its lines as well). -/
def readFasta (path : String) : IO (Array ByteArray) := do
  let total := (← System.FilePath.metadata path).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let mut seqs : Array ByteArray := #[]
  let mut cur := ByteArray.empty
  let mut started := false
  let mut header := false
  let mut seen := 0
  repeat
    let chunk ← h.read 16777216
    if chunk.isEmpty then break
    for b in chunk do
      seen := seen + 1
      if header then
        if b == 10 then header := false
      else if b == 62 then  -- '>'
        if started then
          seqs := seqs.push cur
        -- untouched capacity is not resident
        cur := ByteArray.emptyWithCapacity (total - seen)
        started := true
        header := true
      else if b != 10 && b != 13 then
        cur := cur.push b
  assert! started
  return seqs.push cur

def readReads (path : String) : IO (Array String × Array ByteArray) := do
  let rl := (lines (← IO.FS.readBinFile path)).filter (·.size > 0)
  assert! rl.size % 2 == 0
  return ((Array.range (rl.size / 2)).map fun i => String.fromUTF8! (rl[2 * i]!.extract 1 rl[2 * i]!.size),
          (Array.range (rl.size / 2)).map fun i => rl[2 * i + 1]!)

def showHit (multi : Bool) (h : Placement × Int) : String :=
  (if multi then s!"{h.1.1.chr}\t" else "") ++ s!"{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

/-! Diagnostics (PAIR_DIAG=1): `ilLoop` re-run with counters; its answer is
asserted equal to the proved `mapFastI`. -/
namespace Diag
open MapSpec.Fast

structure St where
  reads : Nat := 0
  lookups : Nat := 0
  anchors : Nat := 0
  fresh : Nat := 0       -- same-length windows scored (new anchors)
  gapRuns : Nat := 0     -- gap-stage passes
  gapAnchors : Nat := 0  -- anchors walked by the gap stage
  zeroLk : Nat := 0      -- lookups returning no anchor
  bigLk : Nat := 0       -- lookups returning > 64 anchors
  maxLk : Nat := 0
  loops : Nat := 0       -- (chromosome, strand) loops entered
  idle : Nat := 0        -- chromosomes whose loop left the best unchanged
  bigAnc : Nat := 0      -- anchors from lookups returning > 64
  doneLk : Nat := 0      -- lookups made when the best was already two penalty-0 hits
  doneAnc : Nat := 0     -- their anchors
  redo : Nat := 0        -- gap-stage anchors re-walked in a later pass (not new this lookup)
  mode : Nat := 0        -- 0: assert = proved mapper; 1: no assert; 2: no assert, gap stage off (unsound)
deriving Inhabited

def St.add (a b : St) : St :=
  ⟨a.reads + b.reads, a.lookups + b.lookups, a.anchors + b.anchors, a.fresh + b.fresh, a.gapRuns + b.gapRuns,
   a.gapAnchors + b.gapAnchors, a.zeroLk + b.zeroLk, a.bigLk + b.bigLk, max a.maxLk b.maxLk,
   a.loops + b.loops, a.idle + b.idle, a.bigAnc + b.bigAnc, a.doneLk + b.doneLk, a.doneAnc + b.doneAnc, a.redo + b.redo, a.mode⟩

def adv {L P : Type} [Inhabited P] (R G : ByteArray) (c : Nat) (lk : Look L P) (ix : L) (ps : Array P)
    (s : LzS) (b : Best) (st : St) : LzS × Best × St :=
  match s.ord with
  | [] => (s, b, st)
  | j :: rest =>
    let lj := lk.look ix G R j ps[j]!
    let fresh := newOnly s.as lj 0 0 #[]
    let as := merge s.as lj 0 0 #[]
    let looked := s.looked + pow2 j
    let b1 := fresh.foldl (sameStep2 R G c) b
    let g := 2 ≤ s.k && 8 ≤ b1.pen && st.mode != 2
    let b2 := if g then gapAll2 R G c as looked as.size 0 b1 else b1
    (⟨rest, s.k + 1, as, looked⟩, b2, { st with
      lookups := st.lookups + 1, anchors := st.anchors + lj.size,
      fresh := st.fresh + fresh.size, gapRuns := st.gapRuns + (if g then 1 else 0),
      gapAnchors := st.gapAnchors + (if g then as.size else 0),
      redo := st.redo + (if g && 3 ≤ s.k then as.size - fresh.size else 0),
      zeroLk := st.zeroLk + (if lj.size == 0 then 1 else 0), bigLk := st.bigLk + (if lj.size > 64 then 1 else 0),
      maxLk := max st.maxLk lj.size, bigAnc := st.bigAnc + (if lj.size > 64 then lj.size else 0),
      doneLk := st.doneLk + (if b.pen == 0 && b.amb then 1 else 0),
      doneAnc := st.doneAnc + (if b.pen == 0 && b.amb then lj.size else 0) })

def il {L P : Type} [Inhabited P] (lk : Look L P) (G : ByteArray) (ix : L)
    (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) : Nat → LzS → LzS → Best → St → Best × St
  | 0, _, _, b, st => (b, st)
  | f + 1, s1, s2, b, st =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := adv R1 G c1 lk ix ps1 s1 b st
      il lk G ix R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2.1 r.2.2
    else if l2 then
      let r := adv R2 G c2 lk ix ps2 s2 b st
      il lk G ix R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2.1 r.2.2
    else (b, st)

def mapI {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray) (idxs : Array L)
    (R : ByteArray) (rf : Bool) (mode : Nat) : Best × St :=
  let n := gbs.size
  let Rr := revCompB R
  let hs := seedHashes R
  let hr := seedHashes Rr
  (List.range n).foldl (fun (b, st) c =>
    let (A, B, ca, cb, ha, hb) := if rf then (Rr, R, n + c, c, hr, hs) else (R, Rr, c, n + c, hs, hr)
    let ix := idxs[c]!
    let ps1 := prepAll lk ix ha
    let ps2 := prepAll lk ix hb
    let (b', st') := il lk gbs[c]! ix A B ca cb ps1 ps2 8 (LzS.init lk ix ps1) (LzS.init lk ix ps2) b
      { st with loops := st.loops + 2 }
    (b', { st' with idle := st'.idle + (if b'.pen == b.pen && b'.amb == b.amb && b'.chr == b.chr then 1 else 0) }))
    ({}, { reads := 1, mode })

def pair {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray)
    (idxs : Array L) (R1 R2 : ByteArray) (mode : Nat := 0) : St :=
  let (b1, s1) := mapI lk gbs idxs R1 false mode
  assert! mode != 0 || decodeJ gbs.size b1 == mapFastI lk gbs idxs R1 false
  match decodeJ gbs.size b1 with
  | none => s1
  | some a =>
    let (b2, s2) := mapI lk gbs idxs R2 (a.1.2 == Strand.fwd) mode
    assert! mode != 0 || decodeJ gbs.size b2 == mapFastI lk gbs idxs R2 (a.1.2 == Strand.fwd)
    s1.add s2

/-- Time the counting loop with (mode 1) and without (mode 2) the gap stage. -/
def timeGap {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray) (idxs : Array L)
    (ps : Array (ByteArray × ByteArray)) : IO Unit := do
  for mode in [1, 2] do
    let t0 ← IO.monoNanosNow
    let st := ps.foldl (fun (st : St) p => st.add (pair lk gbs idxs p.1 p.2 mode)) {}
    let t1 ← IO.monoNanosNow
    IO.println s!"diag: mode {mode} ({if mode == 1 then "as proved" else "gap stage off, unsound"}): {Float.ofNat (t1 - t0) / 1e9} s, {st.reads} reads"

def report (st : St) (pairs : Nat) : IO Unit := do
  let f (x : Nat) := Float.ofNat x
  let r := f st.reads
  IO.println s!"diag: pairs {pairs}, reads mapped {st.reads}"
  IO.println s!"diag: per read: lookups {f st.lookups / r}  anchors {f st.anchors / r}  same-len scored {f st.fresh / r}  gap passes {f st.gapRuns / r}  gap anchors {f st.gapAnchors / r}  (chrom,strand) loops {f st.loops / r}  chroms leaving best unchanged {f st.idle / r}"
  IO.println s!"diag: per lookup: anchors {f st.anchors / f st.lookups}  empty {f st.zeroLk / f st.lookups}  >64 {f st.bigLk / f st.lookups}  max {st.maxLk}  anchors from >64 lookups {f st.bigAnc / f st.anchors}"
  IO.println s!"diag: gap-stage anchors re-walked in a later pass: {f st.redo / r} per read"
  IO.println s!"diag: lookups made after two penalty-0 hits: {f st.doneLk / r} per read, {f st.doneAnc / f st.anchors} of anchors"

end Diag

/-- Every hit of each mate (`hitsL … 12`, proved = all placements of penalty ≤ 12):
`name  mate  chr:start:len:pen:strand ...`. -/
def dumpHits {L P : Type} [Inhabited P] (lk : Fast.Look L P) (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)
    (names : Array String) (ps : Array (ByteArray × ByteArray)) (path : String) : IO Unit := do
  let one (nm : String) (m : Nat) (R : ByteArray) : String :=
    s!"{nm}\t{m}" ++ String.join ((Fast.hitsL lk ix G offs gbs R 12).map fun (p, k) =>
      s!"\t{p.1.chr}:{p.1.start}:{p.1.len}:{k}:{if p.2 == Strand.rev then "-" else "+"}") ++ "\n"
  IO.FS.writeFile path (String.join ((names.zip ps).toList.map fun (nm, p) => one nm 1 p.1 ++ one nm 2 p.2))

/-- Pairs that reach the fallback of `pairFastU` (same tests, untimed). -/
def slowCount {L P : Type} [Inhabited P] (lk : Fast.Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (ps : Array (ByteArray × ByteArray)) : Nat :=
  ps.foldl (fun n p => Id.run do
    let b1 := Fast.mapChromsC lk ix G offs gbs p.1 false
    if 12 < b1.pen then return n
    let b2 := Fast.mapChromsC lk ix G offs gbs p.2 (decide (b1.chr < gbs.size))
    if 12 < b2.pen then return n
    match Fast.decodeJ gbs.size b1, Fast.decodeJ gbs.size b2 with
    | some a, some b => return if properPair lo hi a.1 b.1 then n else n + 1
    | _, _ => return n + 1) 0

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def main (args : List String) : IO UInt32 := do
  let gpath :: p1 :: p2 :: rest := args | throw (IO.userError "usage: pair_bench <genome.fa> <mate1> <mate2> [dump]")
  let gbs ← readFasta gpath
  let (names, r1) ← readReads p1
  let (_, r2) ← readReads p2
  assert! r1.size == r2.size
  assert! (r1 ++ r2).all Fast.fastOk
  let lo := ((← IO.getEnv "PAIR_MIN").getD "100").toNat!
  let hi := ((← IO.getEnv "PAIR_MAX").getD "1000").toNat!
  let tasks := ((← IO.getEnv "PAIR_TASKS").getD "1").toNat!
  let ps := (Array.range r1.size).map fun i => (r1[i]!, r2[i]!)
  let joint := (← IO.getEnv "PAIR_JOINT").isSome
  let inter := (← IO.getEnv "PAIR_INTERLEAVE").isSome
  let mz := ((← IO.getEnv "PAIR_MZ").getD "0").toNat!
  let diag := (← IO.getEnv "PAIR_DIAG").isSome
  let cat := (← IO.getEnv "PAIR_CONCAT").isSome
  let uniq := (← IO.getEnv "PAIR_UNIQ").isSome
  let hitsPath := (← IO.getEnv "PAIR_HITS")
  assert! cat || !uniq
  let f : ByteArray × ByteArray → Option ((Placement × Int) × (Placement × Int)) ← if cat then do
      assert! inter
      let G := gbs.foldl (· ++ ·) ByteArray.empty
      let offs := (gbs.foldl (fun (o, n) g => (o.push n, n + g.size)) ((#[] : Array Nat), 0)).1
      assert! Fast.catOk G offs gbs
      IO.println s!"concatenated genome: {gbs.size} chromosomes, {G.size} letters, catOk"
      if mz == 0 then
        let ix := Fast.buildIdx G
        let ok := Fast.checkIdx ix G
        IO.println s!"index check: {ok}  index_bytes: {ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0}"
        assert! ok
        if uniq then
          IO.println s!"fallback pairs: {slowCount Fast.hLook lo hi ix G offs gbs ps}"
          if let some hp := hitsPath then dumpHits Fast.hLook ix G offs gbs names ps hp
          pure fun p => Fast.pairFastU Fast.hLook lo hi ix G offs gbs p.1 p.2
        else pure fun p => Fast.pairFastC Fast.hLook lo hi ix G offs gbs p.1 p.2
      else
        let B := ((← IO.getEnv "PAIR_MZ_B").getD "24").toNat!
        let C := ((← IO.getEnv "PAIR_MZ_C").getD (toString (25 - mz))).toNat!
        let W := ((← IO.getEnv "PAIR_MZ_W").getD "8").toNat!
        let T := ((← IO.getEnv "PAIR_MZ_T").getD (toString mz)).toNat!
        let ix := Mz.buildW G mz B C W T
        let ok := Mz.check2 ix G
        IO.println s!"index check: {ok}  minimizer k={mz} B={B} C={C} W={W} T={T} kf={ix.kf} index_bytes: {ix.offs.size + ix.sl.size + 8 * ix.runs.size}"
        assert! ok
        if uniq then
          IO.println s!"fallback pairs: {slowCount Fast.mzL lo hi ix G offs gbs ps}"
          if let some hp := hitsPath then dumpHits Fast.mzL ix G offs gbs names ps hp
          pure fun p => Fast.pairFastU Fast.mzL lo hi ix G offs gbs p.1 p.2
        else pure fun p => Fast.pairFastC Fast.mzL lo hi ix G offs gbs p.1 p.2
    else if mz == 0 then do
      let idxs := gbs.map Fast.buildIdx
      let ok := Fast.checkAll idxs gbs
      IO.println s!"index check: {ok}  index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0) 0}"
      assert! ok
      if diag then
        Diag.report (ps.foldl (fun st p => st.add (Diag.pair Fast.hLook gbs idxs p.1 p.2)) {}) ps.size
        Diag.timeGap Fast.hLook gbs idxs ps
      pure fun p => if inter then Fast.pairFastI Fast.hLook lo hi gbs idxs p.1 p.2
        else if joint then Fast.pairFastJ Fast.hLook lo hi gbs idxs p.1 p.2
        else Fast.pairFast Fast.hLook lo hi gbs idxs p.1 p.2
    else do
      assert! joint || inter
      let B := ((← IO.getEnv "PAIR_MZ_B").getD "24").toNat!
      let C := ((← IO.getEnv "PAIR_MZ_C").getD (toString (25 - mz))).toNat!   -- context letters per side
      let W := ((← IO.getEnv "PAIR_MZ_W").getD "8").toNat!   -- bytes per slot (4, 5, 6, 8)
      let T := ((← IO.getEnv "PAIR_MZ_T").getD (toString mz)).toNat!   -- t-words pick the minimizer
      let idxs := gbs.map fun g => Mz.buildW g mz B C W T
      let ok := Fast.checkAllMz idxs gbs
      IO.println s!"index check: {ok}  minimizer k={mz} B={B} C={C} W={W} T={T} kf={idxs.toList.map (·.kf)} index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.sl.size + 8 * ix.runs.size) 0}"
      assert! ok
      if diag then
        Diag.report (ps.foldl (fun st p => st.add (Diag.pair Fast.mzL gbs idxs p.1 p.2)) {}) ps.size
        Diag.timeGap Fast.mzL gbs idxs ps
      pure fun p => if inter then Fast.pairFastI Fast.mzL lo hi gbs idxs p.1 p.2
        else Fast.pairFastJ Fast.mzL lo hi gbs idxs p.1 p.2
  let t0 ← IO.monoNanosNow
  let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 then ps.map f else ParMap.parMap tasks f ps)).get
  let t1 ← IO.monoNanosNow
  let kept := (out.filter (·.isSome)).size
  IO.println s!"pairs: {ps.size}  kept: {kept}"
  IO.println s!"map_seconds: {secs t0 t1}  pairs/s: {Float.ofNat ps.size / secs t0 t1}  reads/s: {Float.ofNat (2 * ps.size) / secs t0 t1}"
  if let dp :: _ := rest then
    IO.FS.writeFile dp (String.join ((names.zip out).toList.map fun (nm, x) => match x with
      | some (a, b) => s!"{nm}\t{showHit (gbs.size > 1) a}\t{showHit (gbs.size > 1) b}\n"
      | none => s!"{nm}\tnone\n"))
  return 0
