import Proofs.Aligner
import Proofs.Fastq

/-! # pipe_prof: where the report-floor pipeline (`answerOfReads`) spends its time (benchmark only, unproved IO)

`pipe_prof INDEX R1 R2 [N]`, 1 thread. Per pair, the stages of `Spec.answerOfReads` run one after another, each
timed; the pair is counted at the stage that closes it (not a leftover). Mates under 25 letters are counted and
skipped (their second look scans the whole genome). -/

open MapSpec MapSpec.Fast Spec

deriving instance Inhabited for Spec.Uniqueness, Spec.Tier, Spec.PairAnswer

def main (args : List String) : IO Unit := do
  let [idx, f1, f2] := args.take 3 | throw (IO.userError "usage: pipe_prof INDEX R1 R2 [N]")
  let lim := (args[3]?.getD "100000000").toNat!
  let index ← IO.FS.readBinFile idx
  let insertSettings : InsertSettings := { range := (100, 1000) }
  let some (ix, G, offs, ns) := (readIndex index).2 | throw (IO.userError "index")
  let pgs := cutAll G #[0] #[G.n]
  let pk : PkMz := (ix, G)
  let cfg := tierCfg insertSettings pk #[0] pgs
  let r1 ← FastqReader.ofHandle (← IO.FS.Handle.mk f1 .read)
  let r2 ← FastqReader.ofHandle (← IO.FS.Handle.mk f2 .read)
  let chunk ← readChunk r1 r2 lim
  let mut cnt : Std.HashMap String Nat := {}
  let add := fun (m : Std.HashMap String Nat) (k : String) (v : Nat) => m.insert k (m.getD k 0 + v)
  let clock := fun (k : String) (v : Nat) (m : Std.HashMap String Nat) => add (add m s!"{k} [us]" (v / 1000)) s!"{k} runs" 1
  for (a0, b0) in chunk do
    let a := a0.letters
    let b := b0.letters
    if a.isEmpty || b.isEmpty then cnt := add cnt "trimmedAway" 1; continue
    if min a.size b.size < 25 then cnt := add cnt "skip: mate < 25" 1; continue
    let req := reqOf insertSettings a b
    let c := lookCap req
    let t0 ← IO.monoNanosNow
    let a1 ← (← IO.mkRef (if t0 == 0 then default else
      answerWith insertSettings req (fallbackFrom req) pk pgs offs ns a b
        (tierPair (pairCfg cfg pk a b) pk #[0] pgs (some a) (some b)))).get
    let t1 ← IO.monoNanosNow
    cnt := clock "1 router+walk" (t1 - t0) cnt
    if !LastResort.Leftover req a1 then cnt := add cnt "closed 1 router+walk" 1; continue
    let j ← (← IO.mkRef (if t1 == 0 then none else
      (joinAt cfg pk pgs c a b).map (answerWith insertSettings req none pk pgs offs ns a b))).get
    let t2 ← IO.monoNanosNow
    cnt := clock "2 join" (t2 - t1) cnt
    if (j.map fun x => !decide (LastResort.Leftover req x)) == some true then cnt := add cnt "closed 2 join" 1; continue
    let s := shortOk pk c a b
    let t3 ← IO.monoNanosNow
    let l ← (← IO.mkRef (if t3 == 0 then default else lookAt insertSettings req pk offs ns a b)).get
    let t4 ← IO.monoNanosNow
    let k := if s then "3 short-cap search" else "5 complete search"
    cnt := clock k (t4 - t3) cnt
    cnt := add cnt s!"closed {k}{if l.found.isSome then " (pair)" else " (bound)"}" 1
  for (k, v) in cnt.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{k}\t{v}"
