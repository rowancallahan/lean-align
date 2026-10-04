import PairMapper
import PairJoint
import PairInterleave
import ParMap
import PairPacked

/-!
Benchmark only (unproved IO).  Runs the PROVED pair mapper `Fast.pairFast`
(codecs/PairMapper.lean, `pairFast_eq_pairSpec`) over mate files.

    lake exe pair_bench <genome.fa> <mate1.reads.txt> <mate2.reads.txt> [dump.tsv]
    env: PAIR_MIN (100), PAIR_MAX (1000), PAIR_TASKS (1), PAIR_JOINT (shared-best strand search, pairFastJ),
    PAIR_INTERLEAVE (strands interleaved one lookup at a time, pairFastI),
    PAIR_MZ=k [PAIR_MZ_B=B] [PAIR_MZ_C=c] [PAIR_MZ_W=bytes] [PAIR_MZ_T=t] (minimizer index, with PAIR_JOINT / PAIR_INTERLEAVE: pairFastJ/I_mz_eq_pairSpec)
    PAIR_PACKED=1 with PAIR_INTERLEAVE and PAIR_MZ (2-bit genome, pairFastIP_mzP_eq_pairSpec): the FASTA is
      packed as it is read, the indexes are built and checked on the packed genome

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

/-- A field (kB) of /proc/self/status: `VmHWM` peak resident set, `VmRSS` current. -/
def statusKB (key : String) : IO Nat := do
  let l := ((← IO.FS.readFile "/proc/self/status").splitOn "\n").find? (·.startsWith key)
  return ((l.getD "").toList.filter Char.isDigit |> String.ofList).toNat!

/-- The sequences of a FASTA file packed as they are read (no byte genome in memory). -/
def readFastaPacked (path : String) : IO (Array Fast.PGen) := do
  let total := (← System.FilePath.metadata path).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let mut out : Array Fast.PGen := #[]
  let mut cur : Option Fast.PB := none
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
        if let some s := cur then out := out.push s.finish
        cur := some (Fast.PB.init (total - seen))
        header := true
      else if b != 10 && b != 13 then
        cur := cur.map (·.push b)
  let some s := cur | throw (IO.userError "no sequence")
  return out.push s.finish

def readReads (path : String) : IO (Array String × Array ByteArray) := do
  let rl := (lines (← IO.FS.readBinFile path)).filter (·.size > 0)
  assert! rl.size % 2 == 0
  return ((Array.range (rl.size / 2)).map fun i => String.fromUTF8! (rl[2 * i]!.extract 1 rl[2 * i]!.size),
          (Array.range (rl.size / 2)).map fun i => rl[2 * i + 1]!)

def showHit (h : Placement × Int) : String :=
  s!"{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def main (args : List String) : IO UInt32 := do
  let gpath :: p1 :: p2 :: rest := args | throw (IO.userError "usage: pair_bench <genome.fa> <mate1> <mate2> [dump]")
  let packed := (← IO.getEnv "PAIR_PACKED").isSome
  let gbs ← if packed then pure #[] else readFasta gpath
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
  let f : ByteArray × ByteArray → Option ((Placement × Int) × (Placement × Int)) ← if packed then do
      assert! inter && mz > 0
      let B := ((← IO.getEnv "PAIR_MZ_B").getD "24").toNat!
      let C := ((← IO.getEnv "PAIR_MZ_C").getD (toString (25 - mz))).toNat!
      let W := ((← IO.getEnv "PAIR_MZ_W").getD "8").toNat!
      let T := ((← IO.getEnv "PAIR_MZ_T").getD (toString mz)).toNat!
      -- no byte genome: the indexes are built and checked on the packed genome (pairFastIP_mzP_eq_pairSpec)
      let pgs ← readFastaPacked gpath
      IO.println s!"genome packed; rss_MB: {(← statusKB "VmRSS:") / 1024}"
      let idxs := pgs.map fun P => Mz.buildWP P mz B C W T
      assert! Fast.checkAllMzP idxs pgs
      IO.println s!"packed genome + index checks: ok  minimizer k={mz} B={B} C={C} W={W} T={T} index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.sl.size + 8 * ix.runs.size) 0}  genome_bytes: {pgs.foldl (fun n P => n + P.w.size + P.ex.size) 0}"
      pure fun p => Fast.pairFastIP Fast.mzL Fast.mzLookP lo hi pgs idxs p.1 p.2
    else if mz == 0 then do
      let idxs := gbs.map Fast.buildIdx
      let ok := Fast.checkAll idxs gbs
      IO.println s!"index check: {ok}  index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0) 0}"
      assert! ok
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
      pure fun p => if inter then Fast.pairFastI Fast.mzL lo hi gbs idxs p.1 p.2
        else Fast.pairFastJ Fast.mzL lo hi gbs idxs p.1 p.2
  let t0 ← IO.monoNanosNow
  let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 then ps.map f else ParMap.parMap tasks f ps)).get
  let t1 ← IO.monoNanosNow
  let kept := (out.filter (·.isSome)).size
  IO.println s!"pairs: {ps.size}  kept: {kept}  peak_rss_MB: {(← statusKB "VmHWM:") / 1024}  rss_MB: {(← statusKB "VmRSS:") / 1024}"
  IO.println s!"map_seconds: {secs t0 t1}  pairs/s: {Float.ofNat ps.size / secs t0 t1}  reads/s: {Float.ofNat (2 * ps.size) / secs t0 t1}"
  if let dp :: _ := rest then
    IO.FS.writeFile dp (String.join ((names.zip out).toList.map fun (nm, x) => match x with
      | some (a, b) => s!"{nm}\t{showHit a}\t{showHit b}\n"
      | none => s!"{nm}\tnone\n"))
  return 0
