import FastMapperPar
import FastMapperMz

/-!
Fast mapper benchmark (IO only, unproved).

    lake exe fast_bench <genome.fa> <reads.txt> [dump.tsv]

Reads the FASTA (one or more chromosomes) and the reads, builds the hashed
index of every chromosome, runs the proved checker on it, maps every read with
the proved `mapFast` (`FAST_TASKS=n`: `mapFastPar` over n tasks; `FAST_MZ=k`
[`FAST_MZ_B=B`]: minimizer index, `mapFastMz`/`mapFastMzPar`), prints times and reads/s, and optionally writes
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

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

/-- Runs `f` after reading the clock; `f` gets the time so it cannot be hoisted. -/
def timed (label : String) (f : Nat → α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← IO.mkRef (f t0)
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}_s: {secs t0 t1}"
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
  let mapAll : Array ByteArray → Array (Option (Window × Int)) ← if mz == 0 then do
      let idxs ← timed "index" fun t => gbs.map fun g => Fast.buildIdx (if t == 1 then g.push 0 else g)
      IO.println s!"index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + ix.ent.size + ix.odd.foldl (· + ·.size) 0) 0}"
      let ok ← timed "check" fun t => Fast.checkAll (if t == 1 then #[] else idxs) gbs
      IO.println s!"index check: {ok}"
      assert! ok
      pure fun rs => if tasks ≤ 1 then rs.map (Fast.mapFast gbs idxs) else Fast.mapFastPar tasks gbs idxs rs
    else do
      let B := ((← IO.getEnv "FAST_MZ_B").getD "24").toNat!
      let idxs ← timed "index" fun t => gbs.map fun g => Mz.build (if t == 1 then g.push 0 else g) mz B
      IO.println s!"minimizer k={mz} B={B} index_bytes: {idxs.foldl (fun n ix => n + ix.offs.size + 8 * ix.sl.size + 8 * ix.runs.size) 0}"
      let ok ← timed "check" fun t => Fast.checkAllMz (if t == 1 then #[] else idxs) gbs
      IO.println s!"index check: {ok}"
      assert! ok
      pure fun rs => if tasks ≤ 1 then rs.map (Fast.mapFastMz gbs idxs) else Fast.mapFastMzPar tasks gbs idxs rs
  let fast := reads.foldl (fun k r => if Fast.fastOk r then k + 1 else k) 0
  IO.println s!"fast-path reads: {fast}"
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
  match rest with
  | [dp] =>
    IO.FS.writeFile dp (String.join (List.zipWith (fun nm x => match x with
      | some (w, s) => s!"{nm}\t{w.start}\t{w.len}\t{s}\n"
      | none => s!"{nm}\tnone\n") names.toList res.toList))
  | _ => pure ()
  return 0
