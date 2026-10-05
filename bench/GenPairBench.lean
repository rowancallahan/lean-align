import FastGenBatch
import ParMap
import FastGenPairPacked

/-!
Benchmark only (unproved IO).  The PROVED general-path both-strand / proper-pair
mapper over one index of the concatenated genome (codecs/FastGenPair.lean:
`mapFastGB_eq_mapSpecBoth`, `pairFastGB_hashed_eq_pairSpec`, `pairFastGB_mz_eq_pairSpec`).

    lake exe gen_pair_bench <genome.fa> <mate1.reads.txt> [mate2.reads.txt [dump.tsv]]
    env: GP_T=P (16), GP_MIN (100), GP_MAX (1000), GP_TASKS (1), GP_MZ=k [GP_MZ_B=B] (minimizer index),
    GP_CHECK=n (reads of 100–103 letters at P = 12: compare with the proved `mapFastC` on n reads)
One mate file: single reads on both strands (`mapFastGS`, short reads by the proved genome scan); two: proper pairs.
GP_SHORTCHECK=n: the short-read path against the indexed path on n reads (both proved = mapSpecBoth).
GP_CHUNK=c: chunks of c reads (mapChunkGS: short reads of a chunk in one genome pass; pairs as pairChunkGS);
GP_CHUNKCHECK=n: chunked against read by read on n reads.
GP_PACKED=1 with GP_MZ=k [GP_MZ_B GP_MZ_C GP_MZ_W GP_MZ_T] and two mate files: no byte genome; the FASTA is packed
as it is read (one PGen, chromosomes are views), the index is built and checked on it, pairs by `pairFastGBP`
(`pairFastGBP_mz_eq_pairSpec`).  Prints peak and current RSS.
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


def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

/-- A field (kB) of /proc/self/status: `VmHWM` peak resident set, `VmRSS` current. -/
def statusKB (key : String) : IO Nat := do
  let l := ((← IO.FS.readFile "/proc/self/status").splitOn "\n").find? (·.startsWith key)
  return ((l.getD "").toList.filter Char.isDigit |> String.ofList).toNat!

/-- All sequences of a FASTA file packed into one genome as they are read, with
each sequence's offset and length. -/
def readFastaPackedCat (path : String) : IO (Fast.PGen × Array Nat × Array Nat) := do
  let total := (← System.FilePath.metadata path).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let mut s := Fast.PB.init total
  let mut offs : Array Nat := #[]
  let mut header := false
  repeat
    let chunk ← h.read 16777216
    if chunk.isEmpty then break
    for b in chunk do
      if header then
        if b == 10 then header := false
      else if b == 62 then  -- '>'
        offs := offs.push s.n
        header := true
      else if b != 10 && b != 13 then
        s := s.push b
  assert! offs.size > 0
  let G := s.finish
  return (G, offs, (Array.range offs.size).map fun c => (offs[c + 1]?.getD G.n) - offs[c]!)

/-- `GP_PACKED=1`: packed genome, one minimizer index, proper pairs (`pairFastGBP`). -/
def mainPacked (gpath p1 p2 : String) (dump : Option String) : IO UInt32 := do
  let P := ((← IO.getEnv "GP_T").getD "16").toNat!
  let lo := ((← IO.getEnv "GP_MIN").getD "100").toNat!
  let hi := ((← IO.getEnv "GP_MAX").getD "1000").toNat!
  let tasks := ((← IO.getEnv "GP_TASKS").getD "1").toNat!
  let mz := ((← IO.getEnv "GP_MZ").getD "0").toNat!
  assert! mz > 0
  let B := ((← IO.getEnv "GP_MZ_B").getD "24").toNat!
  let C := ((← IO.getEnv "GP_MZ_C").getD (toString (25 - mz))).toNat!
  let W := ((← IO.getEnv "GP_MZ_W").getD "8").toNat!
  let T := ((← IO.getEnv "GP_MZ_T").getD (toString mz)).toNat!
  let t0 ← IO.monoNanosNow
  let (G, offs, ns) ← readFastaPackedCat gpath
  assert! Fast.cutOk G offs ns
  let t1 ← IO.monoNanosNow
  IO.println s!"genome packed: {ns.size} chromosomes, {G.n} letters, genome_bytes: {G.w.size + G.ex.size} ({secs t0 t1} s); rss_MB: {(← statusKB "VmRSS:") / 1024}"
  let ix ← (← IO.mkRef (if t1 == 1 then default else Mz.buildWP G mz B C W T)).get
  let t2 ← IO.monoNanosNow
  IO.println s!"index built: k={mz} B={B} C={C} W={W} T={T} kf={ix.kf} index_bytes: {ix.offs.size + ix.sl.size + 8 * ix.runs.size} ({secs t1 t2} s); rss_MB: {(← statusKB "VmRSS:") / 1024}"
  assert! Mz.check2P ix G
  let t3 ← IO.monoNanosNow
  IO.println s!"index check: ok ({secs t2 t3} s)"
  let (names, r1) ← readReads p1
  let (_, r2) ← readReads p2
  assert! r1.size == r2.size
  let pgs := Fast.cutAll G offs ns
  let ps := (Array.range r1.size).map fun i => (r1[i]!, r2[i]!)
  let f (p : ByteArray × ByteArray) := Fast.pairFastGBP P lo hi (ix, G) offs pgs p.1 p.2
  let t0 ← IO.monoNanosNow
  let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 then ps.map f else ParMap.parMap tasks f ps)).get
  let t1 ← IO.monoNanosNow
  IO.println s!"pairs: {ps.size}  kept: {(out.filter (·.isSome)).size}  peak_rss_MB: {(← statusKB "VmHWM:") / 1024}  rss_MB: {(← statusKB "VmRSS:") / 1024}"
  IO.println s!"map_seconds: {secs t0 t1}  pairs/s: {Float.ofNat ps.size / secs t0 t1}  reads/s: {Float.ofNat (2 * ps.size) / secs t0 t1}"
  if let some dp := dump then
    IO.FS.writeFile dp (String.join ((names.zip out).toList.map fun (nm, x) => match x with
      | some (a, b) => s!"{nm}\t{showHit (ns.size > 1) a}\t{showHit (ns.size > 1) b}\n"
      | none => s!"{nm}\tnone\n"))
  return 0

def main (args : List String) : IO UInt32 := do
  let gpath :: p1 :: rest := args | throw (IO.userError "usage: gen_pair_bench <genome.fa> <mate1> [mate2 [dump]]")
  if (← IO.getEnv "GP_PACKED").isSome then
    let p2 :: rest2 := rest | throw (IO.userError "GP_PACKED needs two mate files")
    return ← mainPacked gpath p1 p2 rest2.head?
  let gbs ← readFasta gpath
  let (names, r1) ← readReads p1
  let P := ((← IO.getEnv "GP_T").getD "16").toNat!
  let lo := ((← IO.getEnv "GP_MIN").getD "100").toNat!
  let hi := ((← IO.getEnv "GP_MAX").getD "1000").toNat!
  let tasks := ((← IO.getEnv "GP_TASKS").getD "1").toNat!
  let mz := ((← IO.getEnv "GP_MZ").getD "0").toNat!
  let G := gbs.foldl (· ++ ·) ByteArray.empty
  let offs := (gbs.foldl (fun (o, n) g => (o.push n, n + g.size)) ((#[] : Array Nat), 0)).1
  assert! Fast.catOk G offs gbs
  IO.println s!"concatenated genome: {gbs.size} chromosomes, {G.size} letters, catOk; T = -{P}"
  let (mapOne, mapChunk) : (ByteArray → Option (Placement × Int)) × (Array ByteArray → Array (Option (Placement × Int))) ← if mz == 0 then do
      let ix := Fast.buildIdx G
      let ok := Fast.checkAll #[ix] #[G]
      IO.println s!"index check: {ok}"
      assert! ok
      if let some k := (← IO.getEnv "GP_CHECK") then
        let rs := (r1.extract 0 k.toNat!).filter Fast.fastOk
        let bad := rs.foldl (fun n R => if Fast.mapFastGB 12 ix G offs gbs R == Fast.mapFastC Fast.hLook ix G offs gbs R
          then n else n + 1) 0
        IO.println s!"check vs mapFastC (T = -12) on {rs.size} reads: {bad} differ"
        assert! bad == 0
      if let some k := (← IO.getEnv "GP_SHORTCHECK") then
        -- both proved = mapSpecBoth: the short-read scan against the indexed path
        let rs := r1.extract 0 k.toNat!
        let t0 ← IO.monoNanosNow
        let bad := rs.foldl (fun n R => if Fast.decodeP gbs.size P (Fast.mapChromsShort P gbs R) ==
          Fast.mapFastGB P ix G offs gbs R then n else n + 1) 0
        IO.println s!"short-path check on {rs.size} reads: {bad} differ ({secs t0 (← IO.monoNanosNow)} s)"
        assert! bad == 0
      if (← IO.getEnv "GP_TWO").isSome then
        -- estimate only (not the proved path): -12 first, -P for reads without a hit <= 12
        pure (fun R => if Fast.fastT 12 R then
            let b := Fast.mapChromsGB 12 ix G offs gbs R
            if b.pen ≤ 12 then Fast.decodeP gbs.size 12 b else Fast.mapFastGB P ix G offs gbs R
          else Fast.mapFastGB P ix G offs gbs R, fun rs => Fast.mapChunkGS P ix G offs gbs rs)
      else
      pure (fun R => Fast.mapFastGS P ix G offs gbs R, fun rs => Fast.mapChunkGS P ix G offs gbs rs)
    else do
      let B := ((← IO.getEnv "GP_MZ_B").getD "24").toNat!
      let ix := Mz.buildW G mz B (25 - mz) 8 mz
      let ok := Fast.checkAllMz #[ix] #[G]
      IO.println s!"index check: {ok}  minimizer k={mz} B={B}"
      assert! ok
      pure (fun R => Fast.mapFastGS P ix G offs gbs R, fun rs => Fast.mapChunkGS P ix G offs gbs rs)
  if (← IO.getEnv "GP_TBLTEST").isSome then
    let t0 ← IO.monoNanosNow
    let tb ← (← IO.mkRef (Fast.batchTbl #[] (if t0 == 1 then 2 else 1))).get
    let t1 ← IO.monoNanosNow
    let sc ← (← IO.mkRef (Fast.batchScan gbs[0]! (if t0 == 1 then #[] else #[⟨r1[0]!, 0, 20, 0⟩]))).get
    let t2 ← IO.monoNanosNow
    IO.println s!"batchTbl {secs t0 t1} s ({tb.size}); batchScan 1 seed {secs t1 t2} s ({sc.size})"
  let chunk := ((← IO.getEnv "GP_CHUNK").getD "0").toNat!
  let mapAll (rs : Array ByteArray) : Array (Option (Placement × Int)) :=
    if chunk == 0 then rs.map mapOne
    else ((Array.range ((rs.size + chunk - 1) / chunk)).map fun k => mapChunk (rs.extract (k * chunk) (k * chunk + chunk))).flatten
  if let some k := (← IO.getEnv "GP_CHUNKCHECK") then
    -- both proved = mapSpecBoth: chunked (short reads batched) against read by read
    let rs := r1.extract 0 k.toNat!
    let a := mapAll rs
    let bad := (Array.range rs.size).foldl (fun n i => if a[i]! == mapOne rs[i]! then n else n + 1) 0
    IO.println s!"chunk check on {rs.size} reads: {bad} differ"
    assert! bad == 0
  match rest with
  | [] =>
    let t0 ← IO.monoNanosNow
    let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 || chunk > 0 then mapAll r1 else ParMap.parMap tasks mapOne r1)).get
    let t1 ← IO.monoNanosNow
    IO.println s!"reads: {r1.size}  mapped: {(out.filter (·.isSome)).size}"
    IO.println s!"map_seconds: {secs t0 t1}  reads/s: {Float.ofNat r1.size / secs t0 t1}"
  | p2 :: rest2 =>
    let (_, r2) ← readReads p2
    assert! r1.size == r2.size
    let ps := (Array.range r1.size).map fun i => (r1[i]!, r2[i]!)
    let f (p : ByteArray × ByteArray) : Option ((Placement × Int) × (Placement × Int)) :=
      match mapOne p.1, mapOne p.2 with
      | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
      | _, _ => none
    let pairAll : Array (Option ((Placement × Int) × (Placement × Int))) :=
      let a1 := mapAll r1
      let a2 := mapAll r2
      (Array.range r1.size).map fun i => match a1[i]!, a2[i]! with
        | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
        | _, _ => none
    let t0 ← IO.monoNanosNow
    let out ← (← IO.mkRef (if t0 == 1 then #[] else if chunk > 0 then pairAll
      else if tasks ≤ 1 then ps.map f else ParMap.parMap tasks f ps)).get
    let t1 ← IO.monoNanosNow
    IO.println s!"pairs: {ps.size}  kept: {(out.filter (·.isSome)).size}"
    IO.println s!"map_seconds: {secs t0 t1}  pairs/s: {Float.ofNat ps.size / secs t0 t1}  reads/s: {Float.ofNat (2 * ps.size) / secs t0 t1}"
    if let dp :: _ := rest2 then
      IO.FS.writeFile dp (String.join ((names.zip out).toList.map fun (nm, x) => match x with
        | some (a, b) => s!"{nm}\t{showHit (gbs.size > 1) a}\t{showHit (gbs.size > 1) b}\n"
        | none => s!"{nm}\tnone\n"))
  return 0
