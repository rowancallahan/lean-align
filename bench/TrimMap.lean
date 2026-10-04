import PairGen
import ReadTrim

/-!
Trimmed paired FASTQ → proved trimmer → proved pair mapper → ordered TSV (unproved IO).

    lake exe trim_map <genome.fa> <R1.fq> <R2.fq> [out.tsv]
    env: TM_TASKS (1) mapping tasks, TM_CHUNK (4096) pairs per chunk, TM_MZ=k (minimizer index,
    else hashed), TM_MIN/TM_MAX (100/1000) insert range, TM_T (12) penalty bound, TM_MINLEN (30),
    TM_FQ=prefix (also write the trimmed, non-empty pairs as prefix_1.fq / prefix_2.fq),
    TM_MODE = pipe (default) | prep (read + prep only) | map (prep everything first, then time mapping alone)

Stages, pipelined (prep of chunk i+1 and writing of chunk i−1 overlap mapping of chunk i):
  read  (main thread): exactly TM_CHUNK records from each file;
  prep  (one task per chunk): parse, pair, `ReadTrim.trimRead` both mates (trimRead_acgt: kept
        windows are A/C/G/T only), flag pairs trimmed away (`unmapped: trimmed`) or not taken by the
        mapper (`unmapped: length`);
  map   (≤ TM_TASKS tasks at once): the per-pair mapper, a parameter (`PairMapper`); here
        `pairFastGJ` (pairFastGJ_hashed/mz_eq_pairSpec, any length with `fastT`);
  write (one task chain, in chunk order).
The written text is `formatAll fmt (pairs.map (map ∘ prep))` (ParMap.chunks_text, stages_text).
-/

open MapSpec MapSpec.Fast

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
      else if b == 62 then
        if started then seqs := seqs.push cur
        cur := ByteArray.emptyWithCapacity (total - seen)
        started := true
        header := true
      else if b != 10 && b != 13 then
        cur := cur.push b
  assert! started
  return seqs.push cur

abbrev Hit := Placement × Int

/-- A per-pair mapper: which mates it takes, and the mapping. -/
structure PairMapper where
  ok : ByteArray → Bool
  map : ByteArray → ByteArray → Option (Hit × Hit)

/-- A prepared pair: name, trimmed mates (and qualities), state 0 trimmed / 1 length / 2 ready. -/
structure Prep where
  name : String
  r1 : ByteArray
  q1 : ByteArray
  r2 : ByteArray
  q2 : ByteArray
  st : UInt8
deriving Inhabited

inductive Out where
  | trimmed | length | mapped (r : Option (Hit × Hit))

def showHit (multi : Bool) (h : Hit) : String :=
  (if multi then s!"{h.1.1.chr}\t" else "") ++
    s!"{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

def fmt (multi : Bool) (np : String × Out) : String :=
  match np.2 with
  | .trimmed => s!"{np.1}\tunmapped: trimmed\n"
  | .length => s!"{np.1}\tunmapped: length\n"
  | .mapped none => s!"{np.1}\tnone\n"
  | .mapped (some (a, b)) => s!"{np.1}\t{showHit multi a}\t{showHit multi b}\n"

/-- The map stage. -/
@[inline] def mapStage (m : PairMapper) (p : Prep) : String × Out :=
  (p.name, if p.st == 0 then .trimmed else if p.st == 1 then .length else .mapped (m.map p.r1 p.r2))

/-! ## Parsing -/

/-- From `i`: the position after the `need`-th newline (or the end), and the newlines found. -/
def scanNL (b : ByteArray) (i need found : Nat) : Nat × Nat :=
  if h : i < b.size then
    if found < need then scanNL b (i + 1) need (if b[i] == 10 then found + 1 else found) else (i, found)
  else (i, found)
termination_by b.size - i

/-- Start of each line, and one past the end of the last. -/
def lineStarts (b : ByteArray) (i : Nat) (out : Array Nat) : Array Nat :=
  if h : i < b.size then lineStarts b (i + 1) (if b[i] == 10 then out.push (i + 1) else out)
  else if b.size > 0 && b[b.size - 1]! != 10 then out.push (b.size + 1) else out
termination_by b.size - i

/-- Read name: header without `@`, up to the first blank, a trailing `/1` or `/2` dropped. -/
def nameOf (b : ByteArray) (s e : Nat) : ByteArray := Id.run do
  let mut j := s + 1
  while j < e && b[j]! != 32 && b[j]! != 9 do j := j + 1
  if j ≥ s + 3 && b[j - 2]! == 47 then j := j - 2
  return b.extract (s + 1) j

/-- Exactly `n` records (4 lines each) from the file buffered in `buf[pos ..]`, or fewer at the end. -/
def takeRecs (h : IO.FS.Handle) (buf : ByteArray) (pos n : Nat) : IO (ByteArray × ByteArray × Nat) := do
  let mut buf := buf
  let mut pos := pos
  let mut (i, found) := scanNL buf pos (4 * n) 0
  while found < 4 * n do
    let more ← h.read 16777216
    if more.isEmpty then break
    buf := buf.extract pos buf.size ++ more
    pos := 0
    (i, found) := scanNL buf 0 (4 * n) 0
  return (buf.extract pos i, buf, i)

/-- The prep stage: parse both chunks, pair, trim. -/
def prepChunk (minLen : Nat) (ok : ByteArray → Bool) (c1 c2 : ByteArray) : Array Prep := Id.run do
  let l1 := lineStarts c1 0 #[0]
  let l2 := lineStarts c2 0 #[0]
  let n := (l1.size - 1) / 4
  assert! (l1.size - 1) % 4 == 0 && l2.size == l1.size
  let mut out := Array.mkEmpty n
  for k in [0:n] do
    let a := 4 * k
    let nm := nameOf c1 l1[a]! (l1[a + 1]! - 1)
    assert! nm == nameOf c2 l2[a]! (l2[a + 1]! - 1)
    let s1 := c1.extract l1[a + 1]! (l1[a + 2]! - 1)
    let q1 := c1.extract l1[a + 3]! (l1[a + 4]! - 1)
    let s2 := c2.extract l2[a + 1]! (l2[a + 2]! - 1)
    let q2 := c2.extract l2[a + 3]! (l2[a + 4]! - 1)
    assert! s1.size == q1.size && s2.size == q2.size
    let name := String.fromUTF8! nm
    let w1 := ReadTrim.trimRead s1 q1
    let w2 := ReadTrim.trimRead s2 q2
    match w1, w2 with
    | some (b1, e1), some (b2, e2) =>
      let r1 := s1.extract b1 e1
      let r2 := s2.extract b2 e2
      let st : UInt8 := if r1.size < minLen || r2.size < minLen then 0 else if ok r1 && ok r2 then 2 else 1
      out := out.push ⟨name, r1, q1.extract b1 e1, r2, q2.extract b2 e2, st⟩
    | _, _ => out := out.push ⟨name, .empty, .empty, .empty, .empty, 0⟩
  return out

def fastqOf (ps : Array Prep) : ByteArray × ByteArray := Id.run do
  let mut a := ByteArray.empty
  let mut b := ByteArray.empty
  for p in ps do
    if p.st != 0 then
      let n := ("@" ++ p.name ++ "\n").toUTF8
      a := a ++ n ++ p.r1 ++ "\n+\n".toUTF8 ++ p.q1 ++ "\n".toUTF8
      b := b ++ n ++ p.r2 ++ "\n+\n".toUTF8 ++ p.q2 ++ "\n".toUTF8
  return (a, b)

/-! ## Pipeline -/

structure Stats where
  pairs : Nat := 0
  trimmed : Nat := 0
  length : Nat := 0
  sent : Nat := 0
  mapped : Nat := 0
  readNs : Nat := 0
  prepNs : Nat := 0
  mapNs : Nat := 0
  writeNs : Nat := 0

def count (outs : Array (String × Out)) (s : Stats) : Stats :=
  outs.foldl (fun s o => match o.2 with
    | .trimmed => { s with trimmed := s.trimmed + 1 }
    | .length => { s with length := s.length + 1 }
    | .mapped r => { s with sent := s.sent + 1, mapped := s.mapped + (if r.isSome then 1 else 0) })
    { s with pairs := s.pairs + outs.size }

def secs (ns : Nat) : Float := Float.ofNat ns / 1e9

/-- Prep result of one chunk, timed. -/
def prepTask (minLen : Nat) (ok : ByteArray → Bool) (fq : Bool) (c1 c2 : ByteArray) :
    IO (Array Prep × Option (ByteArray × ByteArray) × Nat) := do
  let t0 ← IO.monoNanosNow
  let ps ← IO.lazyPure fun _ => prepChunk minLen ok c1 c2
  let f ← IO.lazyPure fun _ => if fq then some (fastqOf ps) else none
  let t1 ← IO.monoNanosNow
  return (ps, f, t1 - t0)

/-- Map stage of one chunk, timed; the chunk's text. -/
def mapTask (m : PairMapper) (multi : Bool) (ps : Array Prep) : IO (ByteArray × Array (String × Out) × Nat) := do
  let t0 ← IO.monoNanosNow
  let outs ← IO.lazyPure fun _ => ps.map (mapStage m)
  let txt ← IO.lazyPure fun _ => (ParMap.formatAll (fmt multi) outs).toUTF8
  let t1 ← IO.monoNanosNow
  return (txt, outs, t1 - t0)

def getEnvNat (k : String) (d : Nat) : IO Nat := do
  return ((← IO.getEnv k).getD (toString d)).toNat!

def main (args : List String) : IO UInt32 := do
  let gpath :: p1 :: p2 :: rest := args
    | throw (IO.userError "usage: trim_map <genome.fa> <R1.fq> <R2.fq> [out.tsv]")
  let tasks ← getEnvNat "TM_TASKS" 1
  let chunk ← getEnvNat "TM_CHUNK" 4096
  let mz ← getEnvNat "TM_MZ" 0
  let lo ← getEnvNat "TM_MIN" 100
  let hi ← getEnvNat "TM_MAX" 1000
  let P ← getEnvNat "TM_T" 12
  let minLen ← getEnvNat "TM_MINLEN" 30
  let mode := (← IO.getEnv "TM_MODE").getD "pipe"
  let fqp ← IO.getEnv "TM_FQ"
  assert! tasks ≥ 1 && chunk ≥ 1
  let t0 ← IO.monoNanosNow
  let gbs ← readFasta gpath
  let multi := gbs.size > 1
  let m : PairMapper ← if mz == 0 then do
      let idxs := gbs.map buildIdx
      assert! checkAll idxs gbs
      IO.eprintln s!"hashed indexes: checkAll ok"
      pure ⟨fastT P, pairFastGJ P lo hi gbs idxs⟩
    else do
      let idxs := gbs.map fun g => Mz.buildW g mz 24 (25 - mz) 8 mz
      assert! checkAllMz idxs gbs
      IO.eprintln s!"minimizer indexes k={mz}: checkAllMz ok"
      pure ⟨fastT P, pairFastGJ P lo hi gbs idxs⟩
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"startup (genome {gbs.size} chromosomes, index build + check): {secs (t1 - t0)} s"
  let h1 ← IO.FS.Handle.mk p1 .read
  let h2 ← IO.FS.Handle.mk p2 .read
  let out ← IO.FS.Handle.mk (rest.headD "/dev/null") .write
  let fqh ← match fqp with
    | some p => pure (some (← IO.FS.Handle.mk (p ++ "_1.fq") .write, ← IO.FS.Handle.mk (p ++ "_2.fq") .write))
    | none => pure none
  let st ← IO.mkRef ({} : Stats)
  let tStart ← IO.monoNanosNow
  -- reader
  let mut b1 := ByteArray.empty
  let mut b2 := ByteArray.empty
  let mut o1 := 0
  let mut o2 := 0
  let mut writes : Array (Task (Except IO.Error Unit)) := #[]
  let mut maps : Array (Task (Except IO.Error (ByteArray × Array (String × Out) × Nat))) := #[]
  let mut preps : Array (Array Prep) := #[]
  repeat
    let r0 ← IO.monoNanosNow
    let (c1, nb1, no1) ← takeRecs h1 b1 o1 chunk
    let (c2, nb2, no2) ← takeRecs h2 b2 o2 chunk
    b1 := nb1; b2 := nb2; o1 := no1; o2 := no2
    let r1 ← IO.monoNanosNow
    st.modify fun s => { s with readNs := s.readNs + (r1 - r0) }
    if c1.isEmpty then
      assert! c2.isEmpty
      break
    let t := writes.size + preps.size
    -- bound the chunks in flight
    if writes.size ≥ tasks + 2 then
      let _ ← IO.ofExcept (← IO.wait writes[writes.size - (tasks + 2)]!)
    let pt ← IO.asTask (prio := .dedicated) (prepTask minLen m.ok fqh.isSome c1 c2)
    let prevW : Task (Except IO.Error Unit) ← if t == 0 then IO.asTask (pure ()) else pure writes[t - 1]!
    if mode == "prep" then
      let w ← IO.bindTask prevW fun pw => IO.mapTask (prio := .dedicated) (fun r => do
        let _ ← IO.ofExcept pw
        let (ps, f, ns) ← IO.ofExcept r
        if let (some (a, b), some (fa, fb)) := (f, fqh) then fa.write a; fb.write b
        st.modify fun s => count (ps.map fun p =>
          (p.name, if p.st == 0 then Out.trimmed else if p.st == 1 then .length else .mapped none))
          { s with prepNs := s.prepNs + ns }) pt
      writes := writes.push w
    else if mode == "map" then
      let (ps, f, ns) ← IO.ofExcept (← IO.wait pt)
      if let (some (a, b), some (fa, fb)) := (f, fqh) then fa.write a; fb.write b
      st.modify fun s => { s with prepNs := s.prepNs + ns }
      preps := preps.push ps
    else
      -- map: after the prep of this chunk and the map of chunk t - tasks
      let prev : Task (Except IO.Error Unit) ←
        if t ≥ tasks then IO.mapTask (fun _ => pure ()) maps[t - tasks]! else IO.asTask (pure ())
      let mt ← IO.bindTask pt fun r => IO.bindTask prev fun _ => IO.asTask (prio := .dedicated) do
        let (ps, f, ns) ← IO.ofExcept r
        st.modify fun s => { s with prepNs := s.prepNs + ns }
        if let (some (a, b), some (fa, fb)) := (f, fqh) then fa.write a; fb.write b
        mapTask m multi ps
      maps := maps.push mt
      let w ← IO.bindTask prevW fun pw => IO.mapTask (prio := .dedicated) (fun r => do
        let _ ← IO.ofExcept pw
        let (txt, outs, ns) ← IO.ofExcept r
        let w0 ← IO.monoNanosNow
        out.write txt
        let w1 ← IO.monoNanosNow
        st.modify fun s => count outs { s with mapNs := s.mapNs + ns, writeNs := s.writeNs + (w1 - w0) }) mt
      writes := writes.push w
  if mode == "map" then
    -- mapping alone: everything prepped, same tasks, no reading or prep in the way
    let a0 ← IO.monoNanosNow
    let mut ts : Array (Task (Except IO.Error (ByteArray × Array (String × Out) × Nat))) := #[]
    for i in [0:preps.size] do
      let prev : Task (Except IO.Error Unit) ←
        if i ≥ tasks then IO.mapTask (fun _ => pure ()) ts[i - tasks]! else IO.asTask (pure ())
      ts := ts.push (← IO.bindTask prev fun _ => IO.asTask (prio := .dedicated) (mapTask m multi preps[i]!))
    let mut outsAll := #[]
    for t in ts do outsAll := outsAll.push (← IO.ofExcept (← IO.wait t))
    let a1 ← IO.monoNanosNow
    for (txt, outs, ns) in outsAll do
      out.write txt
      st.modify fun s => count outs { s with mapNs := s.mapNs + ns }
    IO.println s!"mapping alone: {secs (a1 - a0)} s wall, {Float.ofNat (← st.get).pairs / secs (a1 - a0)} pairs/s"
  for w in writes do let _ ← IO.ofExcept (← IO.wait w)
  out.flush
  if let some (fa, fb) := fqh then fa.flush; fb.flush
  let tEnd ← IO.monoNanosNow
  let s ← st.get
  let n := Float.ofNat s.pairs
  IO.println s!"mode {mode}  tasks {tasks}  chunk {chunk}  T -{P}  pairs {s.pairs}"
  IO.println s!"counts: trimmed-away {s.trimmed}  length-skipped {s.length}  sent to mapper {s.sent}  mapped (proper pair) {s.mapped}"
  IO.println s!"read (main thread): {secs s.readNs} s  ({n / secs s.readNs} pairs/s)"
  IO.println s!"prep (task time):   {secs s.prepNs} s  ({n / secs s.prepNs} pairs/s per core)"
  IO.println s!"map (task time):    {secs s.mapNs} s  ({n / secs s.mapNs} pairs/s per core)"
  IO.println s!"write (task time):  {secs s.writeNs} s"
  IO.println s!"overall: {secs (tEnd - tStart)} s wall  {n / secs (tEnd - tStart)} pairs/s (startup {secs (t1 - t0)} s excluded)"
  return 0
