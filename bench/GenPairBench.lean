import FastGenBatch
import FastGenTier
import ParMap
import FastGenPairPacked
import FastGenTierPacked
import FastGenTierK

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
(`pairFastGBP_mz_eq_pairSpec`; with GP_TIER1 `pairTier1P`, `pairTier1P_mz_eq`).  Prints peak and current RSS.
GP_TIER1=1: the tier-1 mapper (cap from the length: >= 150 -> -16, 100-149 -> -12, shorter unmapped; pairTier1_eq).
GP_K=1: word kernels on packed chromosome copies (checkPGs asserted): mapTier1K (pairTier1K_eq) with GP_TIER1,
else mapFastGBK (pairFastGBK_eq).  GP_KCHECK=k: the first k reads, word kernels vs bytes, asserted equal.
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

/-- Prototype (unproved): stage B with the cap lowered to the current best, end shifts nearest first. -/
def stageBDyn (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (shs : List (Int × Int))
    (bs : List Int) (ds : List Nat) (b : Fast.Best) : Fast.Best :=
  ds.foldl (fun b D => bs.foldl (fun b bb =>
    let Pc := min b.pen P
    Fast.stageBD Pc R gbs c shs D b bb) b) b

def chromKBDyn (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat)) (b1 : Fast.Best) : Fast.Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      (if 16 ≤ min lim Q1 then Fast.stageKP else Fast.stageK) R gbs c lim (Fast.shapesKT Q1)
        (Fast.diagsB acc (acc.length - Fast.sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    let d := gapBound sc0 (-(Q2 : Int))
    stageBDyn P R gbs c (Fast.shapesT Q2)
      ((Fast.shifts d).mergeSort fun u v => decide (u.natAbs ≤ v.natAbs))
      (Fast.diagsB acc (acc.length - Fast.sbound P) (2 * d)) b2
  else b2

/-- Prototype (unproved): banded rows with a per-row death threshold `T + h i`. -/
def bandRowsH (T : Int) (B : Nat) (rb : ByteArray) (gb : ByteArray) (e : Nat) (h : Nat → Int) :
    Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      match MapSpec.bandLoop sc0 (T + h i) (T + h i - sc0.gapOpen) rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRowsH T B rb gb e h i N X Y
        else none
    else none

/-- Rows a pruned pass processes before dying (or `rb.size + 1` if it reaches row 0). -/
def rowsH (T : Int) (B : Nat) (rb : ByteArray) (gb : ByteArray) (e : Nat) (h : Nat → Int) :
    Nat → Array Int → Array Int → Array Int → Nat → Nat
  | i, N, X, Y, r =>
    if rb.size ≤ e + i + B then
      match MapSpec.bandLoop sc0 (T + h i) (T + h i - sc0.gapOpen) rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => r + 2
          | i + 1 => rowsH T B rb gb e h i N X Y (r + 1)
        else r + 1
    else r

/-- (passes, rows, passes reaching row 0) of the pruned stage B, at the final cap `Pc`. -/
def statsBH (P Pc : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (bs : List Int) (ds : List Nat)
    (seeds : List (Nat × Array Nat)) (Ls : Nat) : Nat × Nat × Nat :=
  ds.foldl (fun a (D : Nat) => bs.foldl (fun a bb =>
    if 0 ≤ (D : Int) + bb then
      let Bc := bandOf sc0 (-(Pc : Int))
      let e := ((D : Int) + bb).toNat
      let spoiled := seeds.filterMap fun (j, arr) => if Fast.anyNear arr (e - (Bc + 1)) (e + Bc + 1) then none else some (j * Ls + 25)
      let h : Nat → Int := fun i => 4 * (spoiled.filter (· ≤ i)).length
      let r := rowsH (-(Pc : Int)) Bc R gbs[c]! e h R.size (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1))
        (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1)) (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1)) 0
      (a.1 + 1, a.2.1 + r, a.2.2 + (if r > R.size then 1 else 0))
    else a) a) (0, 0, 0)

/-- Prototype: stage B with the seed lower bound (`h i` = 4 · seeds wholly before row `i`
without an anchor within `W` diagonals of `D`), dynamic cap, nearest end shifts first. -/
def stageBH (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (shs : List (Int × Int))
    (bs : List Int) (ds : List Nat) (seeds : List (Nat × Array Nat)) (Ls : Nat) (b : Fast.Best) (rowPrune : Bool := true) (seedCharge : Int := 4) : Fast.Best :=
  ds.foldl (fun b (D : Nat) =>
    bs.foldl (fun b bb =>
      let Pc := min b.pen P
      if 0 ≤ (D : Int) + bb then
        let Bc := bandOf sc0 (-(Pc : Int))
        let e := ((D : Int) + bb).toNat
        let W := Bc + 1
        let spoiled := (seeds.filterMap fun (j, arr) => if Fast.anyNear arr (e - W) (e + W) then none else some (j * Ls + 25)).toArray
        let h : Nat → Int := fun i => if rowPrune then seedCharge * (spoiled.foldl (fun a t => if t ≤ i then a + 1 else a) 0 : Nat) else
          if i = R.size then 4 * spoiled.size else 0
        if (Pc : Int) < h R.size then b else
        let opt := bandRowsH (-(Pc : Int)) Bc R gbs[c]! ((D : Int) + bb).toNat h R.size
          (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1)) (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1))
          (Array.replicate (2 * Bc + 3) (-(Pc : Int) - 1))
        (shs.filter (·.2 == bb)).foldl (Fast.addBS Pc R gbs c D opt) b
      else b) b) b

def chromKBH (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat)) (seeds : List (Nat × Array Nat))
    (Ls : Nat) (b1 : Fast.Best) (skipOnly : Bool := false) (charge : Int := 4) : Fast.Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let K := min lim Q1
  let b2 := if 0 < gapBound sc0 (-(K : Int)) then
      (if 16 ≤ K then Fast.stageKP else Fast.stageK) R gbs c lim (Fast.shapesKT K)
        (Fast.diagsB acc (acc.length - Fast.sbound K) (2 * gapBound sc0 (-(K : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    let d := gapBound sc0 (-(Q2 : Int))
    stageBH P R gbs c (Fast.shapesT Q2) ((Fast.shifts d).mergeSort fun u v => decide (u.natAbs ≤ v.natAbs))
      (Fast.diagsB acc (acc.length - Fast.sbound P) (2 * d)) seeds Ls b2 (rowPrune := !skipOnly) (seedCharge := charge)
  else b2

/-- Prototype of the provable rule: thresholds `tN i = T + 4 H i`, `tG i = tN i + (6 or 4)`,
`H i` = spoiled 25-letter blocks ending by row `i` (no exact copy at any position in the band of
any end `D ± d`); fixed cap `P`. -/
def bandRowsP (T : Int) (B : Nat) (rb : ByteArray) (gb : ByteArray) (e : Nat) (H : Nat → Nat) :
    Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      let tN := T + 4 * (H i : Int)
      let tG := tN + (if H i = 0 then 6 else 4)
      match MapSpec.bandLoop sc0 tN tG rb gb e i (i == rb.size) (min (2 * B) (e + i + B - rb.size))
          (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRowsP T B rb gb e H i N X Y
        else none
    else none

def stageBP (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (shs : List (Int × Int))
    (d : Nat) (ds : List Nat) (b : Fast.Best) : Fast.Best :=
  let B := bandOf sc0 (-(P : Int))
  let n := R.size
  let G := gbs[c]!
  ds.foldl (fun b (D : Nat) =>
    -- block j (rows [25j, 25j+25)) spoiled: no exact copy at p ∈ [D - d - n + 25j - B, D + d - n + 25j + B]
    let sp := (List.range (n / 25)).filter fun (j : Nat) =>
      let lo : Int := (D : Int) - d - n + (25 * j : Nat) - B
      let hi : Int := (D : Int) + d - n + (25 * j : Nat) + B
      ((List.range (hi - lo + 1).toNat).all fun t =>
        let p := lo + t
        !(0 ≤ p && p + 25 ≤ (G.size : Int) && (List.range 25).all fun u => R.get! (25 * j + u) == G.get! (p.toNat + u)))
    let ends : List Nat := sp.map fun j => 25 * j + 25
    let H : Nat → Nat := fun i => ends.foldl (fun a t => if t ≤ i then a + 1 else a) 0
    (Fast.shifts d).foldl (fun b bb =>
      if 0 ≤ (D : Int) + bb then
        let opt := bandRowsP (-(P : Int)) B R G ((D : Int) + bb).toNat H n
          (Array.replicate (2 * B + 3) (-(P : Int) - 1)) (Array.replicate (2 * B + 3) (-(P : Int) - 1))
          (Array.replicate (2 * B + 3) (-(P : Int) - 1))
        (shs.filter (·.2 == bb)).foldl (Fast.addBS P R gbs c D opt) b
      else b) b) b

def chromKBP (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat)) (b1 : Fast.Best) : Fast.Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      (if 16 ≤ min lim Q1 then Fast.stageKP else Fast.stageK) R gbs c lim (Fast.shapesKT Q1)
        (Fast.diagsB acc (acc.length - Fast.sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    let d := gapBound sc0 (-(Q2 : Int))
    stageBP P R gbs c (Fast.shapesT Q2) d (Fast.diagsB acc (acc.length - Fast.sbound P) (2 * d)) b2
  else b2

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
  let tier1 := (← IO.getEnv "GP_TIER1").isSome
  let f (p : ByteArray × ByteArray) := if tier1 then Fast.pairTier1P lo hi (ix, G) offs pgs p.1 p.2
    else Fast.pairFastGBP P lo hi (ix, G) offs pgs p.1 p.2
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
  let tier1 := (← IO.getEnv "GP_TIER1").isSome   -- cap from the read length (mapTier1 / pairTier1_eq)
  let useK := (← IO.getEnv "GP_K").isSome
  let pvs := if useK then gbs.map Fast.pack else #[]
  assert! !useK || Fast.checkPGs pvs gbs
  let kcheck := ((← IO.getEnv "GP_KCHECK").getD "0").toNat!
  if kcheck > 0 then assert! useK
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
      if (← IO.getEnv "GP_PROF").isSome then
        -- timing only: mapChromsGB's interleaved lookups (ilG) vs stages K/B (chromKB)
        let n := gbs.size
        let gbs2 := gbs ++ gbs
        let t0 ← IO.monoNanosNow
        let xs ← (← IO.mkRef (r1.map fun R =>
          let Rr := Fast.revCompB2 R
          let m := R.size / 25
          let Ls := R.size / m
          let ps := Fast.prepG ix R m Ls
          let pr := Fast.prepG ix Rr m Ls
          (R, Rr, Fast.ilG ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
            ⟨Fast.ordG (ps.map (Fast.LookG.size ix)) m, [], Array.replicate n []⟩
            ⟨Fast.ordG (pr.map (Fast.LookG.size ix)) m, [], Array.replicate n []⟩ (Fast.initP P)))).get
        let t1 ← IO.monoNanosNow
        let bs ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let b := (List.range n).foldl (fun b c => Fast.chromKB R gbs2 c P x.1.acc[c]! b) x.2.2
          (List.range n).foldl (fun b c => Fast.chromKB Rr gbs2 (n + c) P x.2.1.acc[c]! b) b)).get
        let t2 ← IO.monoNanosNow
        let looks := xs.foldl (fun a (_, _, x) => a + x.1.J.length + x.2.1.J.length) 0
        let anc := xs.foldl (fun a (_, _, x) => a + x.1.acc.foldl (fun a l => a + l.foldl (· + ·.size) 0) 0
          + x.2.1.acc.foldl (fun a l => a + l.foldl (· + ·.size) 0) 0) 0
        let dK := xs.foldl (fun a (R, _, x) =>
          let Q1 := min x.2.2.pen P
          a + x.1.acc.foldl (fun a acc => a + (Fast.diagsB acc (acc.length - Fast.sbound (min (min P 16) Q1))
            (2 * gapBound sc0 (-(Q1 : Int)))).length) 0 + x.2.1.acc.foldl (fun a acc => a + (Fast.diagsB acc
            (acc.length - Fast.sbound (min (min P 16) Q1)) (2 * gapBound sc0 (-(Q1 : Int)))).length) 0) 0
        let t3 ← IO.monoNanosNow
        let lk ← (← IO.mkRef (xs.foldl (fun a (R, Rr, x) =>
          let m := R.size / 25
          let Ls := R.size / m
          let ps := Fast.prepG ix R m Ls
          let pr := Fast.prepG ix Rr m Ls
          let a := x.1.J.foldl (fun a j => a + (Fast.LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!).size) a
          x.2.1.J.foldl (fun a j => a + (Fast.LookG.look ix G Rr (j * Ls) (Rr.size - j * Ls) pr[j]!).size) a) 0)).get
        let t4 ← IO.monoNanosNow
        let hsh ← (← IO.mkRef (xs.foldl (fun a (R, Rr, _) =>
          let m := R.size / 25
          let Ls := R.size / m
          a + (Fast.prepG ix R m Ls).size + (Fast.prepG ix Rr m Ls).size + (Fast.revCompB2 R).size) 0)).get
        let t5 ← IO.monoNanosNow
        let hist := xs.foldl (fun (h : Array (Nat × Nat)) (R, _, x) =>
          let Q1 := min x.2.2.pen P
          let shs := ((Fast.shapesAt Q1).filter (· != (0, 0))).length
          let nd := x.1.acc.foldl (fun a acc => a + (Fast.diagsB acc (acc.length - Fast.sbound (min (min P 16) Q1))
            (2 * gapBound sc0 (-(Q1 : Int)))).length) 0 + x.2.1.acc.foldl (fun a acc => a + (Fast.diagsB acc
            (acc.length - Fast.sbound (min (min P 16) Q1)) (2 * gapBound sc0 (-(Q1 : Int)))).length) 0
          let k := if 0 < gapBound sc0 (-(Q1 : Int)) then nd * shs else 0
          h.modify Q1 fun (c, w) => (c + 1, w + k)) (Array.replicate (P + 2) (0, 0))
        IO.println s!"prof: by phase-1 best Q1: (reads, stage-K kernel calls) {(Array.range (P + 2)).toList.filterMap fun q => if hist[q]!.1 > 0 then some (q, hist[q]!) else none}"
        let fin := (xs.zip bs).foldl (fun (h : Array Nat) ((_, _, x), b) =>
          if min x.2.2.pen P == P then h.modify (min b.pen (P + 1)) (· + 1) else h) (Array.replicate (P + 2) 0)
        IO.println s!"prof: final best of the reads with phase-1 best {P}: {(Array.range (P + 2)).toList.filterMap fun q => if fin[q]! > 0 then some (q, fin[q]!) else none}"
        let t6 ← IO.monoNanosNow
        let ords ← (← IO.mkRef (xs.foldl (fun a (R, Rr, _) =>
          let m := R.size / 25
          let Ls := R.size / m
          let ps := Fast.prepG ix R m Ls
          let pr := Fast.prepG ix Rr m Ls
          a + (Fast.ordG (ps.map (Fast.LookG.size ix)) m).length + (Fast.ordG (pr.map (Fast.LookG.size ix)) m).length) 0)).get
        let t7 ← IO.monoNanosNow
        let hashes ← (← IO.mkRef (xs.foldl (fun a (R, Rr, _) =>
          let m := R.size / 25
          let Ls := R.size / m
          (List.range m).foldl (fun a j => a + ((Fast.seedHashAt R (j * Ls)).getD 0).toNat % 2 + ((Fast.seedHashAt Rr (j * Ls)).getD 0).toNat % 2) a) 0)).get
        let t8 ← IO.monoNanosNow
        IO.println s!"prof: lookups alone {secs t3 t4} s ({lk}); prep+revcomp {secs t4 t5} s ({hsh}); prep+ordG {secs t6 t7} s ({ords}); hashes only {secs t7 t8} s ({hashes})"
        let ddup := xs.foldl (fun a (_, _, x) =>
          a + x.1.acc.foldl (fun a acc => a + (Fast.diags acc).length) 0 + x.2.1.acc.foldl (fun a acc => a + (Fast.diags acc).length) 0) 0
        let ta ← IO.monoNanosNow
        let ak ← (← IO.mkRef (xs.foldl (fun a (R, Rr, x) =>
          let f := fun (R : ByteArray) (t : Nat) (accs : Array (List (Array Nat))) (b : MapSpec.Fast.Best) =>
            (List.range n).foldl (fun b c => accs[c]!.foldl (fun b arr => arr.foldl (fun b e =>
              Fast.addK R gbs2 (t + c) (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b) b) b) b
          a + (f Rr n x.2.1.acc (f R 0 x.1.acc (Fast.initP P))).pen) 0)).get
        let tb ← IO.monoNanosNow
        IO.println s!"prof: distinct anchor diagonals {ddup} of {anc} anchors; anchor kernels from initP {secs ta tb} s ({ak})"
        let allSeeds := (← IO.getEnv "GP_ALLSEEDS").isSome
        let th0 ← IO.monoNanosNow
        let bsH ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let m := R.size / 25
          let Ls := R.size / m
          -- all seeds (n = 1 here: chromosome 0 starts at 0)
          let all := fun (R : ByteArray) => let ps := Fast.prepG ix R m Ls
            (List.range m).map fun j => (j, Fast.sliceG (Fast.LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!) (R.size - j * Ls) 0 gbs2[0]!.size)
          let sa := if allSeeds then all R else x.1.J.zip x.1.acc[0]!
          let sr := if allSeeds then all Rr else x.2.1.J.zip x.2.1.acc[0]!
          let b := (List.range n).foldl (fun b c => chromKBH R gbs2 c P x.1.acc[c]! sa Ls b) x.2.2
          (List.range n).foldl (fun b c => chromKBH Rr gbs2 (n + c) P x.2.1.acc[c]! sr Ls b) b)).get
        let th1 ← IO.monoNanosNow
        let bsP ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let b := (List.range n).foldl (fun b c => chromKBP R gbs2 c P x.1.acc[c]! b) x.2.2
          (List.range n).foldl (fun b c => chromKBP Rr gbs2 (n + c) P x.2.1.acc[c]! b) b)).get
        let th1p ← IO.monoNanosNow
        let difP := (bs.zip bsP).foldl (fun a (u, v) => if Fast.resultP P u == Fast.resultP P v then a else a + 1) 0
        IO.println s!"prof: chromKB, provable pruning (fixed cap, blocks checked directly) {secs th1 th1p} s, results differ on {difP}"
        let bs2c ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let m := R.size / 25
          let Ls := R.size / m
          let b := (List.range n).foldl (fun b c => chromKBH R gbs2 c P x.1.acc[c]! (x.1.J.zip x.1.acc[c]!) Ls b false 2) x.2.2
          (List.range n).foldl (fun b c => chromKBH Rr gbs2 (n + c) P x.2.1.acc[c]! (x.2.1.J.zip x.2.1.acc[c]!) Ls b false 2) b)).get
        let th1c ← IO.monoNanosNow
        let dif2 := (bs.zip bs2c).foldl (fun a (u, v) => if Fast.resultP P u == Fast.resultP P v then a else a + 1) 0
        IO.println s!"prof: chromKB with seed lower bound, 2 per seed {secs th1 th1c} s, results differ on {dif2}"
        let bsS ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let m := R.size / 25
          let Ls := R.size / m
          let b := (List.range n).foldl (fun b c => chromKBH R gbs2 c P x.1.acc[c]! (x.1.J.zip x.1.acc[c]!) Ls b true) x.2.2
          (List.range n).foldl (fun b c => chromKBH Rr gbs2 (n + c) P x.2.1.acc[c]! (x.2.1.J.zip x.2.1.acc[c]!) Ls b true) b)).get
        let th1b ← IO.monoNanosNow
        let difS := (bs.zip bsS).foldl (fun a (u, v) => if Fast.resultP P u == Fast.resultP P v then a else a + 1) 0
        IO.println s!"prof: chromKB with pass skip only {secs th1 th1b} s, results differ on {difS}"
        let bsK ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let m := R.size / 25
          let Ls := R.size / m
          let b := (List.range n).foldl (fun b c => chromKBH R gbs2 c 16 x.1.acc[c]! [] Ls b) x.2.2
          (List.range n).foldl (fun b c => chromKBH Rr gbs2 (n + c) 16 x.2.1.acc[c]! [] Ls b) b)).get
        let th2 ← IO.monoNanosNow
        IO.println s!"prof: stage K only (P = 16 on these phase-1 states) {secs th1 th2} s ({bsK.size})"
        let st := (xs.zip bsH).foldl (fun (a : Nat × Nat × Nat) ((R, Rr, x), bf) =>
          if bf.pen ≤ min P 16 then a else
          let m := R.size / 25
          let Ls := R.size / m
          let Pc := min bf.pen P
          let d := gapBound sc0 (-(P : Int))
          let f := fun (R : ByteArray) (c : Nat) (s : Fast.GS) =>
            statsBH P Pc R gbs2 c (Fast.shifts d) (Fast.diagsB s.acc[0]! (s.acc[0]!.length - Fast.sbound P) (2 * d)) (s.J.zip s.acc[0]!) Ls
          let u := f R 0 x.1
          let v := f Rr n x.2.1
          (a.1 + u.1 + v.1, a.2.1 + u.2.1 + v.2.1, a.2.2 + u.2.2 + v.2.2)) (0, 0, 0)
        IO.println s!"prof: pruned passes at the final cap: {st.1}, rows {st.2.1}, full passes {st.2.2}"
        let difH := (bs.zip bsH).foldl (fun a (u, v) => if Fast.resultP P u == Fast.resultP P v then a else a + 1) 0
        IO.println s!"prof: chromKB with seed lower bound {secs th0 th1} s, results differ on {difH}"
        let tq ← IO.monoNanosNow
        let bsD ← (← IO.mkRef (xs.map fun (R, Rr, x) =>
          let b := (List.range n).foldl (fun b c => chromKBDyn R gbs2 c P x.1.acc[c]! b) x.2.2
          (List.range n).foldl (fun b c => chromKBDyn Rr gbs2 (n + c) P x.2.1.acc[c]! b) b)).get
        let tr ← IO.monoNanosNow
        let difD := (bs.zip bsD).foldl (fun a (u, v) => if Fast.resultP P u == Fast.resultP P v then a else a + 1) 0
        IO.println s!"prof: chromKB with dynamic stage-B cap {secs tq tr} s, results differ on {difD}"
        let hitIdx := (Array.range xs.size).filter fun i => bs[i]!.pen ≤ P && bs[i]!.pen > min P 16
        let noIdx := (Array.range xs.size).filter fun i => bs[i]!.pen > P
        let runKB (ix : Array Nat) : Nat := ix.foldl (fun a i =>
          let (R, Rr, x) := xs[i]!
          let b := (List.range n).foldl (fun b c => Fast.chromKB R gbs2 c P x.1.acc[c]! b) x.2.2
          a + ((List.range n).foldl (fun b c => Fast.chromKB Rr gbs2 (n + c) P x.2.1.acc[c]! b) b).pen) 0
        let u0 ← IO.monoNanosNow
        let v1 ← (← IO.mkRef (runKB hitIdx)).get
        let u1 ← IO.monoNanosNow
        let v2 ← (← IO.mkRef (runKB noIdx)).get
        let u2 ← IO.monoNanosNow
        IO.println s!"prof: chromKB on {hitIdx.size} reads with best in (16, P]: {secs u0 u1} s; on {noIdx.size} reads without hit: {secs u1 u2} s ({v1 + v2})"
        -- stage B: reads whose final best stays above 16, their diagonals and banded passes
        let sB := (xs.zip bs).foldl (fun (a : Nat × Nat × Nat) ((_, _, x), b) =>
          if b.pen ≤ min P 16 then a else
          let Q2 := min b.pen P
          let r := 2 * gapBound sc0 (-(Q2 : Int))
          let nd := x.1.acc.foldl (fun a acc => a + (Fast.diagsB acc (acc.length - Fast.sbound P) r).length) 0 +
            x.2.1.acc.foldl (fun a acc => a + (Fast.diagsB acc (acc.length - Fast.sbound P) r).length) 0
          (a.1 + 1, a.2.1 + nd, a.2.2 + nd * (2 * gapBound sc0 (-(Q2 : Int)) + 1))) (0, 0, 0)
        IO.println s!"prof: stage B reads {sB.1}, diagonals {sB.2.1}, banded passes {sB.2.2}; final pens {(xs.zip bs).foldl (fun (h : Array Nat) (_, b) => h.modify (min b.pen (P + 1)) (· + 1)) (Array.replicate (P + 2) 0)}"
        IO.println s!"prof: ilG {secs t0 t1} s, chromKB {secs t1 t2} s ({bs.size}); lookups {looks}, anchors {anc}, stage-K diagonals (at phase-1 best) {dK}"
      if (← IO.getEnv "GP_TWO").isSome then
        -- estimate only (not the proved path): -12 first, -P for reads without a hit <= 12
        pure (fun R => if Fast.fastT 12 R then
            let b := Fast.mapChromsGB 12 ix G offs gbs R
            if b.pen ≤ 12 then Fast.decodeP gbs.size 12 b else Fast.mapFastGB P ix G offs gbs R
          else Fast.mapFastGB P ix G offs gbs R, fun rs => Fast.mapChunkGS P ix G offs gbs rs)
      else if useK then do
        let fK := fun R => if tier1 then Fast.mapTier1K ix G offs gbs pvs R else Fast.mapFastGBK P ix G offs gbs pvs R
        let fB := fun R => if tier1 then Fast.mapTier1 ix G offs gbs R else Fast.mapFastGB P ix G offs gbs R
        let rs := r1.extract 0 kcheck
        let bad := rs.foldl (fun n R => if fK R == fB R then n else n + 1) 0
        if kcheck > 0 then IO.println s!"word-kernel check on {rs.size} reads: {bad} differ"
        assert! bad == 0
        pure (fK, fun rs => rs.map fK)
      else if tier1 then
        pure (fun R => Fast.mapTier1 ix G offs gbs R, fun rs => rs.map (Fast.mapTier1 ix G offs gbs))
      else
      pure (fun R => Fast.mapFastGS P ix G offs gbs R, fun rs => Fast.mapChunkGS P ix G offs gbs rs)
    else do
      let B := ((← IO.getEnv "GP_MZ_B").getD "24").toNat!
      let ix := Mz.buildW G mz B (25 - mz) 8 mz
      let ok := Fast.checkAllMz #[ix] #[G]
      IO.println s!"index check: {ok}  minimizer k={mz} B={B}"
      assert! ok
      if useK then do
        let fK := fun R => if tier1 then Fast.mapTier1K ix G offs gbs pvs R else Fast.mapFastGBK P ix G offs gbs pvs R
        let fB := fun R => if tier1 then Fast.mapTier1 ix G offs gbs R else Fast.mapFastGB P ix G offs gbs R
        let rs := r1.extract 0 kcheck
        let bad := rs.foldl (fun n R => if fK R == fB R then n else n + 1) 0
        if kcheck > 0 then IO.println s!"word-kernel check on {rs.size} reads: {bad} differ"
        assert! bad == 0
        pure (fK, fun rs => rs.map fK)
      else if tier1 then
        pure (fun R => Fast.mapTier1 ix G offs gbs R, fun rs => rs.map (Fast.mapTier1 ix G offs gbs))
      else
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
