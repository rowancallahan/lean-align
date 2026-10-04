import FastMapperPar
import FastMapperMz
import FastGenAlgo
import MzCheckPar

/-!
Fast mapper benchmark (IO only, unproved).

    lake exe fast_bench <genome.fa> <reads.txt> [dump.tsv]

`FAST_BOTH=1`: map each read and its reverse complement and keep the unique best
over the two strands (a tie between strands: none), as `proto`'s `PROTO_BOTH`.
The strands are combined here, in bench code, from each strand's `Best`
(`mapChroms`, whose penalty and ambiguity `mapFast_eq_mapSpec` rests on); there is
no strand theorem yet.  `FAST_SYM=1` also maps all reverse complements and checks
the answers are the same windows with the strand flipped.  `FAST_TRUTH=truth.tsv`
counts reads at the true position (and strand, with `FAST_BOTH`).

Reads the FASTA (one or more chromosomes) and the reads, builds the hashed
index of every chromosome, runs the proved checker on it, maps every read with
the proved `mapFast` (`FAST_TASKS=n`: `mapFastPar` over n tasks; `FAST_MZ=k`
[`FAST_MZ_B=B`, `FAST_MZ_C=c`, `FAST_MZ_W=bytes`, `FAST_MZ_T=t`]: minimizer index, `mapFastMz`/`mapFastMzPar`), prints times and reads/s, and optionally writes
`name \t start \t len \t score` (or `name \t none`) per read, the format of
`proto`'s dump.
-/

open MapSpec

def nextNL (raw : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < raw.size && raw.get! j != 10 do j := j + 1
  return j

/-- Lines of a file as byte strings. -/
def lines (raw : ByteArray) : Array ByteArray := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < raw.size do
    let j := nextNL raw i
    out := out.push (raw.extract i j)
    i := j + 1
  return out

def readFasta (path : String) : IO (Array String × Array ByteArray) := do
  let ls := lines (← IO.FS.readBinFile path)
  let mut names := #[]
  let mut seqs : Array ByteArray := #[]
  for l in ls do
    if l.size > 0 && l.get! 0 == 62 then
      names := names.push (String.fromUTF8! (l.extract 1 l.size))
      seqs := seqs.push ByteArray.empty
    else
      assert! seqs.size > 0
      seqs := seqs.modify (seqs.size - 1) (· ++ l)
  assert! seqs.size > 0
  return (names, seqs)

/-- Reverse complement (letters other than ACGT kept). -/
def revComp (r : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.emptyWithCapacity r.size
  for i in [0:r.size] do
    let c := r.get! (r.size - 1 - i)
    o := o.push (if c == 65 then 84 else if c == 84 then 65 else if c == 67 then 71 else if c == 71 then 67 else c)
  return o

/-- Unique best over both strands (`true` = reverse); a tie between strands: none. -/
def bothOf (f r : Fast.Best) : Option (Window × Int × Bool) :=
  let one (b : Fast.Best) (rv : Bool) := if b.pen ≤ 12 && !b.amb then some (⟨b.chr, b.st, b.len⟩, -(b.pen : Int), rv) else none
  if f.pen < r.pen then one f false else if r.pen < f.pen then one r true else none

def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

/-- Runs `f` after reading the clock; `f` gets the time so it cannot be hoisted. -/
def timed (label : String) (f : Nat → α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← IO.mkRef (f t0)
  let t1 ← IO.monoNanosNow
  say s!"{label}_s: {secs t0 t1}"
  r.get

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: rest := args | throw (IO.userError "usage: fast_bench <genome.fa> <reads.txt> [dump.tsv]")
  let (_, gbs) ← readFasta gpath
  let rl := (lines (← IO.FS.readBinFile rpath)).filter (·.size > 0)
  assert! rl.size % 2 == 0
  let names := (Array.range (rl.size / 2)).map fun i => String.fromUTF8! (rl[2 * i]!.extract 1 rl[2 * i]!.size)
  let reads := (Array.range (rl.size / 2)).map fun i => rl[2 * i + 1]!
  IO.println s!"chromosomes: {gbs.size}  letters: {gbs.foldl (· + ·.size) 0}  reads: {reads.size}"
  let tasks := ((← IO.getEnv "FAST_TASKS").getD "1").toNat!   -- 1 = no tasks
  let mz := ((← IO.getEnv "FAST_MZ").getD "0").toNat!          -- 0 = hashed index
  let both := (← IO.getEnv "FAST_BOTH").isSome
  let par (f : ByteArray → Option (Window × Int × Bool)) (rs : Array ByteArray) :=
    if tasks ≤ 1 then rs.map f else ParMap.parMap tasks f rs
  let mapAll : Array ByteArray → Array (Option (Window × Int × Bool)) ← if mz == 0 then do
      let idxs ← timed "index" fun t => gbs.map fun g => Fast.buildIdx (if t == 1 then g.push 0 else g)
      IO.println s!"index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0) 0}"
      let ok ← timed "check" fun t => Fast.checkAll (if t == 1 then #[] else idxs) gbs
      IO.println s!"index check: {ok}"
      assert! ok
      let best R := Fast.mapChroms Fast.hLook R gbs idxs
      let tP : Option Nat := (← IO.getEnv "FAST_T").map String.toNat!
      if let some P := tP then
        if let some k := (← IO.getEnv "FAST_SLOWCHECK") then
          let k := k.toNat!
          -- reference: the proved banded mapper over a CSR index certified by checkIndex
          -- (bandMapper_eq_mapSpec, checkIndex_complete); any 0 < l0 ≤ seed length works
          let T : Int := -(P : Int)
          let gb : ByteGenome := gbs.map fun b => ⟨"", b⟩
          let g := decodeGenome gb
          let l0 := 12
          let csr ← timed "csr" fun t => buildCsr l0 (if t == 1 then #[] else gb)
          let okc ← timed "csr_check" fun t => checkIndex csr (if t == 1 then #[] else gb)
          assert! okc
          let ref R := bandMapper csr.lookup l0 sc0 T g gbs (decodeBytes R) R
          let t0 ← IO.monoNanosNow
          let bad := (reads.extract 0 k).foldl (fun n R => if Fast.mapFastTG P gbs idxs R == ref R then n else n + 1) 0
          say s!"reference check (bandMapper) on {min k reads.size} reads at T = -{P}: {bad} differ ({secs t0 (← IO.monoNanosNow)} s)"
          assert! bad == 0
      pure fun rs => if let some P := tP then par (fun R => (Fast.mapFastTG P gbs idxs R).map fun (w, s) => (w, s, false)) rs
        else if both then par (fun R => bothOf (best R) (best (revComp R))) rs
        else (if tasks ≤ 1 then rs.map (Fast.mapFast gbs idxs) else Fast.mapFastPar tasks gbs idxs rs).map
          (·.map fun (w, s) => (w, s, false))
    else do
      let B := ((← IO.getEnv "FAST_MZ_B").getD "24").toNat!
      let C := ((← IO.getEnv "FAST_MZ_C").getD (toString (25 - mz))).toNat!   -- context letters per side
      let W := ((← IO.getEnv "FAST_MZ_W").getD "8").toNat!   -- bytes per slot (4, 5, 6, 8)
      let T := ((← IO.getEnv "FAST_MZ_T").getD (toString mz)).toNat!   -- t-words pick the minimizer
      let idxs ← timed "index" fun t => gbs.map fun g => Mz.buildW (if t == 1 then g.push 0 else g) mz B C W T
      IO.println s!"minimizer k={mz} B={B} C={C} W={W} T={T} kf={idxs.toList.map (·.kf)} index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.sl.size + 8 * ix.runs.size) 0}"
      -- FAST_CHECK_PAR=P: a task per chromosome, P tasks for its entries (checkAllMzPar_eq)
      let cpar := ((← IO.getEnv "FAST_CHECK_PAR").getD "0").toNat!
      let ok ← timed "check" fun t =>
        (if cpar > 0 then Fast.checkAllMzPar cpar else Fast.checkAllMz) (if t == 1 then #[] else idxs) gbs
      IO.println s!"index check: {ok}"
      assert! ok
      let best R := Fast.mapChroms Fast.mzL R gbs idxs
      pure fun rs => if both then par (fun R => bothOf (best R) (best (revComp R))) rs
        else (if tasks ≤ 1 then rs.map (Fast.mapFastMz gbs idxs) else Fast.mapFastMzPar tasks gbs idxs rs).map
          (·.map fun (w, s) => (w, s, false))
  let fast := reads.foldl (fun k r => if Fast.fastOk r then k + 1 else k) 0
  IO.println s!"fast-path reads: {fast}"
  if let some ps := (← IO.getEnv "FAST_T") then
    let gen := reads.foldl (fun k r => if Fast.fastT ps.toNat! r then k + 1 else k) 0
    say s!"general fast-path reads: {gen}"
    assert! gen == reads.size
  else
    assert! fast == reads.size   -- other read lengths take the proved slow fallback
  let reps := ((← IO.getEnv "FAST_REPS").getD "1").toNat!   -- repeat the mapping (timing only)
  let t0 ← IO.monoNanosNow
  let mut res := #[]
  for k in [0:reps] do
    let rs := if t0 + k == 1 then #[] else reads
    let ta ← IO.monoNanosNow
    res ← (← IO.mkRef (mapAll rs)).get   -- forced before the clock is read again
    IO.println s!"rep {k}: {secs ta (← IO.monoNanosNow)} s ({res.size})"
  let mapped := res.foldl (fun k x => if x.isSome then k + 1 else k) 0
  let t1 ← IO.monoNanosNow
  IO.println s!"mapped: {mapped}"
  IO.println s!"map_seconds: {secs t0 t1 / Float.ofNat reps}  reads/s: {Float.ofNat (reps * reads.size) / secs t0 t1}"
  if let some tp := ← IO.getEnv "FAST_TRUTH" then
    let tl := ((lines (← IO.FS.readBinFile tp)).filter (·.size > 0)).extract 1 (reads.size + 1)
    assert! tl.size == reads.size
    let right := (tl.zip res).foldl (fun k (l, x) =>
      match (String.fromUTF8! l).splitOn "\t", x with
      | [_, _, pos, _, st], some (w, _, rv) => if pos.toNat! == w.start + 1 && (st == "-") == rv then k + 1 else k
      | [_, _, pos, _], some (w, _, _) => if pos.toNat! == w.start + 1 then k + 1 else k
      | _, _ => k) 0
    IO.println s!"at_true_position{if both then "_and_strand" else ""}: {right}"
  if both && (← IO.getEnv "FAST_SYM").isSome then
    let rc := mapAll (reads.map revComp)
    let bad := (res.zip rc).foldl (fun k (a, b) => match a, b with
      | some (w, s, rv), some (w', s', rv') => if w == w' && s == s' && rv != rv' then k else k + 1
      | none, none => k
      | _, _ => k + 1) 0
    IO.println s!"symmetry (reverse complements: same window, other strand): {res.size - bad} / {res.size} agree"
    assert! bad == 0
  match rest with
  | [dp] =>
    IO.FS.writeFile dp (String.join (List.zipWith (fun nm x => match x with
      | some (w, s, rv) => s!"{nm}\t{w.start}\t{w.len}\t{s}" ++ (if both then (if rv then "\t-" else "\t+") else "") ++ "\n"
      | none => s!"{nm}\tnone\n") names.toList res.toList))
  | _ => pure ()
  return 0
