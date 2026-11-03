import Proofs.Sam
/-! Measurement only (NOT proved, not part of the tool): the pairs that reach the second look (`lookAt`) and what
each mate's full hit search costs there.

    lake exe second_look_bench INDEX R1.fq R2.fq MODE LIST
    MODE: list (write the 0-based indices of pairs reaching lookAt to LIST) | x1 | x2 (hitsX of mate 1 / mate 2 on
    the pairs in LIST, printing hit and placement counts) | look (lookAt on the pairs in LIST) -/
open MapSpec MapSpec.Fast Spec

def reachesLook (insertSettings : InsertSettings) (cfg : TierCfg) (pk : PkMz) (pgs : Array PGen) (offs ns : Array Nat)
    (read1 read2 : ByteArray) : Bool :=
  let req := reqOf insertSettings read1 read2
  let t := tierPair (pairCfg cfg pk read1 read2) pk #[0] pgs (some read1) (some read2)
  let a1 := answerWith insertSettings req (fallbackFrom req) pk pgs offs ns read1 read2 t
  if !decide (LastResort.Leftover req a1) then false else
  let c := lookCap req
  let j := (joinAt cfg pk pgs c read1 read2).map (answerWith insertSettings req none pk pgs offs ns read1 read2)
  match j with
  | some a => if !decide (LastResort.Leftover req a) then false else
      if shortOk pk c read1 read2 then false else (gaveUp req pk offs ns read1 read2 a1).isNone
  | none => if shortOk pk c read1 read2 then false else (gaveUp req pk offs ns read1 read2 a1).isNone

def main (args : List String) : IO UInt32 := do
  match args with
  | [indexPath, r1, r2, mode, listPath] =>
    let index ← IO.FS.readBinFile indexPath
    let some (ix, G, offs, ns) := (readIndex index).2 | throw (IO.userError "no index")
    let pk : PkMz := (ix, G)
    let insertSettings : InsertSettings := { range := (100, 1000) }
    let pgs := cutAll G #[0] #[G.n]
    let cfg := tierCfg insertSettings pk #[0] pgs
    let reads1 ← FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
    let reads2 ← FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
    let chunk ← readChunk reads1 reads2 1000000
    if mode == "list" then
      let mut out := ""
      let mut i := 0
      for (a, b) in chunk do
        let ra : ByteArray := a.letters
        let rb : ByteArray := b.letters
        if !ra.isEmpty && !rb.isEmpty && reachesLook insertSettings cfg pk pgs offs ns ra rb then out := out ++ s!"{i}\n"
        i := i + 1
      IO.FS.writeFile listPath out
      IO.println s!"listed {(out.splitOn "\n").length - 1}"
    else
      let idx := ((← IO.FS.readFile listPath).splitOn "\n").filterMap String.toNat?
      let pgsC := cutAll G offs ns
      for i in idx do
        let some (a, b) := chunk[i]? | continue
        let ra : ByteArray := a.letters
        let rb : ByteArray := b.letters
        let req := reqOf insertSettings ra rb
        let c := lookCap req
        if mode == "seeds" then
          for (nm, R) in [("m1", ra), ("m2", rb)] do
            for (st, Rs) in [("f", R), ("r", revCompK R)] do
              let m := Rs.size / 25
              let Ls := Rs.size / m
              let cells := (List.range m).map fun j =>
                let p := mzPrep pk.1 (seedHashAt Rs (j * Ls))
                let b := if p.ok then pk.1.hiB p.b - pk.1.loB p.b else 0
                let e := if p.ok then (mzLookSP pk.1 pk.2 Rs (j * Ls) 0 p).size else 999999
                s!"{b}:{e}"
              IO.println s!"{i} {nm}{st} need {sbound c + 1} of {m} seeds {" ".intercalate cells}"
        else if mode == "look" then
          let r := lookAt insertSettings req pk offs ns ra rb
          IO.println s!"{i} found {r.found.isSome} bps {r.bestPossibleScore} req {req}"
        else
          let t0 ← IO.monoNanosNow
          let l := hitsKPF pk ByteArray.empty offs pgsC (if mode == "x1" then ra else rb) c
          let n := l.length
          let t1 ← IO.monoNanosNow
          let rc := rareCost pk (if mode == "x1" then ra else rb) (sbound c + 1)
          IO.println s!"{i} {mode} hits {n} req {req} us {(t1 - t0) / 1000} rare {rc}"
    return 0
  | _ => IO.eprintln "usage"; return 1
