import PairMapper
import PairJoint
import PairInterleave
import PairSched
import ParMap

/-!
Benchmark only (unproved IO).  Runs the PROVED pair mapper `Fast.pairFast`
(codecs/PairMapper.lean, `pairFast_eq_pairSpec`) over mate files.

    lake exe pair_bench <genome.fa> <mate1.reads.txt> <mate2.reads.txt> [dump.tsv]
    env: PAIR_MIN (100), PAIR_MAX (1000), PAIR_TASKS (1), PAIR_JOINT (shared-best strand search, pairFastJ),
    PAIR_INTERLEAVE (strands interleaved one lookup at a time, pairFastI),
    PAIR_MODES=I,S1,S2 (several mappers on one index; dumps <dump>.<mode>; RSS is the peak over all),
    PAIR_STATS (lookups and anchors per read of the S modes), PAIR_SCHED=m (one lookup scheduler over all chromosomes and strands, pairFastS; m = 1: key (k, size),
    2: (size, k); mate 2 searches mate 1's chromosome on the other strand first),
    PAIR_MZ=k [PAIR_MZ_B=B] (minimizer index, with PAIR_JOINT / PAIR_INTERLEAVE: pairFastJ/I_mz_eq_pairSpec)

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

def readFasta (path : String) : IO (Array ByteArray) := do
  let mut seqs : Array ByteArray := #[]
  for l in lines (← IO.FS.readBinFile path) do
    if l.size > 0 && l.get! 0 == 62 then seqs := seqs.push ByteArray.empty
    else
      assert! seqs.size > 0
      seqs := seqs.modify (seqs.size - 1) (· ++ l)
  assert! seqs.size > 0
  return seqs

def readReads (path : String) : IO (Array String × Array ByteArray) := do
  let rl := (lines (← IO.FS.readBinFile path)).filter (·.size > 0)
  assert! rl.size % 2 == 0
  return ((Array.range (rl.size / 2)).map fun i => String.fromUTF8! (rl[2 * i]!.extract 1 rl[2 * i]!.size),
          (Array.range (rl.size / 2)).map fun i => rl[2 * i + 1]!)

def showHit (h : Placement × Int) : String :=
  s!"{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

/-- Lookups and anchors of the scheduled search of one read (same code as `mapChromsS`). -/
def schedStats {L P : Type} [Inhabited L] [Inhabited P] (lk : Fast.Look L P) (key : Nat → Nat → Nat → Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) : Nat × Nat :=
  let n := gbs.size
  let Rr := Fast.revCompB R
  let pss := (Array.range (2 * n)).map fun i => Fast.prepAll lk idxs[Fast.sChr n i]! (Fast.seedHashes (Fast.sRead n R Rr i))
  let ss0 := (Array.range (2 * n)).map fun i => Fast.LzS.init lk idxs[Fast.sChr n i]! pss[i]!
  let r := Fast.schedLoop lk key gbs idxs R Rr pss (8 * n) ss0 {}
  r.1.foldl (fun (a, b) s => (a + s.k, b + s.as.size)) (0, 0)

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
  let sched := ((← IO.getEnv "PAIR_SCHED").getD "0").toNat!
  let mode0 := if sched != 0 then s!"S{sched}" else if inter then "I" else if joint then "J" else "F"
  -- PAIR_MODES=I,S1,S2: several mappers on one index, dumps `<dump>.<mode>`
  let modes := ((← IO.getEnv "PAIR_MODES").getD mode0).splitOn ","
  let key1 (m : String) : Nat → Nat → Nat → Nat :=
    if m == "S2" then fun _ k sz => sz * 8 + k else fun _ k sz => k * 2 ^ 40 + sz
  -- mate 2: the slot of mate 1's chromosome on the other strand goes first while live
  let key2 (m : String) (a : Placement) : Nat → Nat → Nat → Nat := fun i k sz =>
    if i == (if a.2 == Strand.fwd then gbs.size + a.1.chr else a.1.chr) then 0 else key1 m i k sz + 1
  let mz := ((← IO.getEnv "PAIR_MZ").getD "0").toNat!
  let f : String → ByteArray × ByteArray → Option ((Placement × Int) × (Placement × Int)) ← if mz == 0 then do
      let idxs := gbs.map Fast.buildIdx
      let ok := Fast.checkAll idxs gbs
      IO.println s!"index check: {ok}  index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0) 0}"
      assert! ok
      pure fun m p => if m.startsWith "S" then Fast.pairFastS Fast.hLook (key1 m) (key2 m) lo hi gbs idxs p.1 p.2
        else if m == "I" then Fast.pairFastI Fast.hLook lo hi gbs idxs p.1 p.2
        else if m == "J" then Fast.pairFastJ Fast.hLook lo hi gbs idxs p.1 p.2
        else Fast.pairFast Fast.hLook lo hi gbs idxs p.1 p.2
    else do
      let B := ((← IO.getEnv "PAIR_MZ_B").getD "24").toNat!
      let idxs := gbs.map fun g => Mz.build g mz B
      let ok := Fast.checkAllMz idxs gbs
      IO.println s!"index check: {ok}  minimizer k={mz} B={B} index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + 8 * ix.sl.size + 8 * ix.runs.size) 0}"
      assert! ok
      if (← IO.getEnv "PAIR_STATS").isSome then
        for m in modes.filter (·.startsWith "S") do
          let st := ps.map fun p => match Fast.mapFastS Fast.mzL (key1 m) gbs idxs p.1 with
            | some a => let x := schedStats Fast.mzL (key1 m) gbs idxs p.1
              let y := schedStats Fast.mzL (key2 m a.1) gbs idxs p.2
              (2, x.1 + y.1, x.2 + y.2)
            | none => let x := schedStats Fast.mzL (key1 m) gbs idxs p.1; (1, x.1, x.2)
          let t := st.foldl (fun (a, b, c) (x, y, z) => (a + x, b + y, c + z)) (0, 0, 0)
          IO.println s!"stats {m}: reads {t.1}  lookups/read {Float.ofNat t.2.1 / Float.ofNat t.1}  anchors/read {Float.ofNat t.2.2 / Float.ofNat t.1}"
      if (← IO.getEnv "PAIR_PROF").isSome then
        -- time per mate-1 read by class: anchors ≤ 64 / > 64, mapped or not
        let mut acc : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0), (0, 0)]
        for p in ps do
          let t0 ← IO.monoNanosNow
          let st ← pure (schedStats Fast.mzL (key1 "S2") gbs idxs p.1)
          let t1 ← IO.monoNanosNow
          let r := Fast.mapFastS Fast.mzL (key1 "S2") gbs idxs p.1
          let c := (if st.2 > 64 then 2 else 0) + (if r.isSome then 1 else 0)
          acc := acc.modify c fun (n, t) => (n + 1, t + (t1 - t0))
        IO.println s!"prof (count, ns) [≤64 unmapped, ≤64 mapped, >64 unmapped, >64 mapped]: {acc}"
      pure fun m p => if m.startsWith "S" then Fast.pairFastS Fast.mzL (key1 m) (key2 m) lo hi gbs idxs p.1 p.2
        else if m == "I" then Fast.pairFastI Fast.mzL lo hi gbs idxs p.1 p.2
        else Fast.pairFastJ Fast.mzL lo hi gbs idxs p.1 p.2
  for m in modes do
    let t0 ← IO.monoNanosNow
    let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 then ps.map (f m) else ParMap.parMap tasks (f m) ps)).get
    let t1 ← IO.monoNanosNow
    let kept := (out.filter (·.isSome)).size
    IO.println s!"mode {m}  pairs: {ps.size}  kept: {kept}"
    IO.println s!"mode {m}  map_seconds: {secs t0 t1}  pairs/s: {Float.ofNat ps.size / secs t0 t1}  reads/s: {Float.ofNat (2 * ps.size) / secs t0 t1}"
    if let dp :: _ := rest then
      IO.FS.writeFile (if modes.length == 1 then dp else s!"{dp}.{m}") (String.join ((names.zip out).toList.map fun (nm, x) => match x with
        | some (a, b) => s!"{nm}\t{showHit a}\t{showHit b}\n"
        | none => s!"{nm}\tnone\n"))
  let hwm := ((← IO.FS.readFile "/proc/self/status").splitOn "\n").filter (·.startsWith "VmHWM")
  IO.println s!"rss: {hwm}"
  return 0
