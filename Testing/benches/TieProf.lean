import Proofs.Aligner
import Proofs.Fastq

/-! # tie_prof: where the shim's CPU goes, by tier and reason (benchmark only, unproved IO)

`lake exe tie_prof INDEX R1.fq R2.fq [N]` — 1 thread, the first N pairs (default all). Runs the same
calls as `Spec.alignOneC` (gate, RT, `tierRest`, `tierUp`, `answerOfPair`, `finalize`) with a clock
between them, and prints µs per stage summed by (final tag, RT reason). Asserts the staged answer
equals `alignOneC`'s on every pair when `TP_CHECK=1`. -/

open MapSpec MapSpec.Fast Spec

def reasonStr : Option Reason → String
  | none => "-"
  | some r => match r with
    | .trimmedAway _ => "trim" | .tooShort _ => "short" | .noHit _ => "noHit" | .tie _ => "tie"
    | .noPartner _ => "noPartner" | .notProper => "notProper" | .noPair => "noPair"

structure Tally where
  n : Nat := 0
  t : Array Nat := Array.replicate 6 0
deriving Inhabited

deriving instance Inhabited for Spec.Uniqueness, Spec.Tier, Spec.PairAnswer

/-- One mate's RT search (`mateKP` at cap `P`) in two timed parts: lookups + same-length scoring
(`ilGFG`), then the gapped stage (`chromKBFG`); with pen, amb, lookups and anchors. -/
def probeMate (pk : PkMz) (pgs : Array PGen) (P : Nat) (R : ByteArray) : IO (Nat × Nat × Best × Nat × Nat × Best) := do
  let s : PrepM MzP := prepMate pk R
  let gbs2 := pgs ++ pgs
  let kf1 := kerHKG R s.K1 gbs2 gbs2
  let kf2 := kerHKG s.Rr s.K2 gbs2 gbs2
  let n := pgs.size
  let m := R.size / 25
  let Ls := R.size / m
  let t0 ← IO.monoNanosNow
  let x ← (← IO.mkRef (if t0 == 0 then (default, default, initP P) else ilGFG kf1 kf2 pk ByteArray.empty R s.Rr gbs2 #[0] n P Ls s.ps s.pr (2 * m + 1)
    ⟨ordG (s.ps.map (LookG.size pk)) m, [], Array.replicate n []⟩
    ⟨ordG (s.pr.map (LookG.size pk)) m, [], Array.replicate n []⟩ (initP P))).get
  let t1 ← IO.monoNanosNow
  let b ← (← IO.mkRef (if t1 == 0 then initP P else
    let b := (List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2
    (List.range n).foldl (fun b c => chromKBFG kf2 s.Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b) b)).get
  let t2 ← IO.monoNanosNow
  -- (prototype) the gap stage after a tie at p: only windows below p matter, so cap p - 1 from a fresh best
  let b1 := x.2.2
  let bT ← (← IO.mkRef (if t2 == 0 then initP P else
    if b1.amb && 0 < b1.pen && b1.pen ≤ P then
      let P' := b1.pen - 1
      let b := (List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c P' x.1.acc[c]! x.1.J b) (initP P')
      let b := (List.range n).foldl (fun b c => chromKBFG kf2 s.Rr gbs2 (n + c) P' x.2.1.acc[c]! x.2.1.J b) b
      if b.pen ≤ P' then b else b1
    else b)).get
  let t3 ← IO.monoNanosNow
  assert! (decodeP n P b == decodeP n P bT && decide (b.pen ≤ P) == decide (bT.pen ≤ P))
  let t4 ← IO.monoNanosNow
  let y ← (← IO.mkRef (if t4 == 0 then (default, default, initP P) else ilGFGT kf1 kf2 pk ByteArray.empty R s.Rr gbs2 #[0] n P Ls s.ps s.pr (2 * m + 1)
    ⟨ordG (s.ps.map (LookG.size pk)) m, [], Array.replicate n []⟩
    ⟨ordG (s.pr.map (LookG.size pk)) m, [], Array.replicate n []⟩ (initP P))).get
  let t5 ← IO.monoNanosNow
  let bY ← (← IO.mkRef (if t5 == 0 then initP P else tieCut P (fun Q b =>
      let b := (List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c Q y.1.acc[c]! y.1.J b) b
      (List.range n).foldl (fun b c => chromKBFG kf2 s.Rr gbs2 (n + c) Q y.2.1.acc[c]! y.2.1.J b) b) y.2.2)).get
  let t6 ← IO.monoNanosNow
  assert! (decodeP n P b == decodeP n P bY && decide (b.pen ≤ P) == decide (bY.pen ≤ P))
  IO.println s!"PH1T\t{x.2.2.amb}\t{y.2.2.amb}\t{t1 - t0}\t{t3 - t2}\t{t5 - t4}\t{t6 - t5}\t{y.1.J.length + y.2.1.J.length}"
  if b1.amb then IO.println s!"TIEGAP\t{b1.pen}\t{t2 - t1}\t{t3 - t2}\t{b.pen}\t{bT.pen}"
  let anc := (x.1.acc.toList ++ x.2.1.acc.toList).foldl (fun a l => a + l.foldl (fun a v => a + v.size) 0) 0
  return (t1 - t0, t2 - t1, b, x.1.J.length + x.2.1.J.length, anc, x.2.2)

def main (args : List String) : IO Unit := do
  let [idx, f1, f2] := args.take 3 | throw (IO.userError "usage: tie_prof INDEX R1 R2 [N]")
  let lim := (args[3]?.getD "100000000").toNat!
  let index ← IO.FS.readBinFile idx
  let insertSettings : InsertSettings := { range := (100, 1000) }
  let some (ix, G, offs, ns, H, M) := (readIndex index).2 | throw (IO.userError "index")
  let pgs := cutAll G #[0] #[G.n]
  let pk : PkMz := (ix, G)
  let cfg0 := tierCfg insertSettings pk #[0] pgs
  let r1 ← FastqReader.ofHandle (← IO.FS.Handle.mk f1 .read)
  let r2 ← FastqReader.ofHandle (← IO.FS.Handle.mk f2 .read)
  let chunk ← readChunk r1 r2 lim
  let check := (← IO.getEnv "TP_CHECK") == some "1"
  let probe := (← IO.getEnv "TP_MATE").isSome
  let allM := (← IO.getEnv "TP_MATE") == some "2"
  let mut accs : Std.HashMap String Tally := {}
  let mut tot : Array Nat := Array.replicate 6 0
  for (a0, b0) in chunk do
    let a := a0.letters
    let b := b0.letters
    let t0 ← IO.monoNanosNow
    let cfg := pairCfg cfg0 pk a b
    let s1 : PrepM MzP := prepMate pk a
    let s2 : PrepM MzP := prepMate pk b
    let cmax ← (← IO.mkRef (if t0 == 0 then 0 else max (costP pk (cfg.rcfg.cap1 a) s1) (costP pk (cfg.rcfg.cap1 b) s2))).get
    let gated := cfg.gate a b s1 s2 (costP pk (cfg.rcfg.cap1 a) s1) (costP pk (cfg.rcfg.cap1 b) s2)
    let t1 ← IO.monoNanosNow
    let rt ← (← IO.mkRef (if gated || t1 == 0 then none else some (tierRT cfg pk #[0] pgs a b))).get
    let t2 ← IO.monoNanosNow
    let tb ← (← IO.mkRef (if t2 == 0 then default else match rt with
      | none => tierRest cfg pk #[0] pgs a b none 0 0
      | some r => match r.out with
        | .mapped (x, y) =>
          { tag := .t1, why := none, c1 := r.c1, c2 := r.c2,
            m1 := { st := "U", cap := cfg.rcfg.cap1 a, cd := cfg.rcfg.cap1 a, pen := (-x.2).toNat, pl := some x },
            m2 := { st := "U", cap := cfg.rcfg.cap1 b, cd := cfg.rcfg.cap1 b, pen := (-y.2).toNat, pl := some y } }
        | .unmapped rs k => tierRest cfg pk #[0] pgs a b (some (rs, k)) r.c1 r.c2 : TierOut)).get
    let t3 ← IO.monoNanosNow
    let t ← (← IO.mkRef (if t3 == 0 then tb else tierUp cfg pk #[0] pgs a b tb)).get
    let t4 ← IO.monoNanosNow
    let ans ← (← IO.mkRef (if t4 == 0 then default else
      Report.answerOfPair reportTies (fallbackFrom insertSettings) mateRescue pk insertSettings pgs offs ns a b t)).get
    let t5 ← IO.monoNanosNow
    let fin ← (← IO.mkRef (if t5 == 0 then default else LastResort.finalize insertSettings (LastResort.fitNs ns) a b ans)).get
    let t6 ← IO.monoNanosNow
    if check then
      let ref := alignOne insertSettings #[] (some (ix, G, offs, ns, H, M)) (some a) (some b)
      assert! (match ref with | .aligned r => reprStr r == reprStr fin | _ => false)
    let cb := if cmax ≤ 2000 then "c<=2k" else if cmax ≤ 5000 then "c<=5k" else if cmax ≤ 10000 then "c<=10k" else if cmax ≤ 15000 then "c<=15k" else if cmax ≤ 30000 then "c<=30k" else if cmax ≤ 60000 then "c<=60k" else "c>60k"
    let key := s!"{cb}\t{t.tagStr}\t{reasonStr t.why}\t{if gated then "gated" else ""}\t{if fin.found.isSome then "found" else "none"}\t{repr fin.uniqueness}"
    let ds := #[t1 - t0, t2 - t1, t3 - t2, t4 - t3, t5 - t4, t6 - t5]
    let ac := accs.getD key {}
    accs := accs.insert key { n := ac.n + 1, t := (ac.t.zip ds).map fun (x, y) => x + y }
    tot := (tot.zip ds).map fun (x, y) => x + y
    if probe && (t.why.isSome || allM) then
      for (R, c) in [(a, t.c1), (b, t.c2)] do
        let c := if c == 0 then cfg.rcfg.cap1 R else c
        let (ta, tb, bb, nl, na, b1) ← probeMate pk pgs c R
        IO.println s!"MATE\t{reasonStr t.why}\t{t.tagStr}\t{c}\t{bb.pen}\t{bb.amb}\t{nl}\t{na}\t{ta / 1000}\t{tb / 1000}\t{b1.pen}\t{b1.amb}"
  let all := tot.foldl (· + ·) 0
  IO.println s!"pairs {chunk.size}  total {all / 1000000} ms  stages gate/RT/rest/up/answer/finalize ms: {tot.map (· / 1000000)}"
  IO.println "cost\ttag\twhy\tgated\tfound\tuniq\tpairs\tms_total\tshare%\tus/pair\tgate\tRT\trest\tup\tanswer\tfinal (ms)"
  let rows := accs.toArray.qsort fun x y => x.2.t.foldl (· + ·) 0 > y.2.t.foldl (· + ·) 0
  for (k, ac) in rows do
    let s := ac.t.foldl (· + ·) 0
    IO.println s!"{k}\t{ac.n}\t{s / 1000000}\t{s * 1000 / all / 10}.{s * 1000 / all % 10}\t{s / 1000 / ac.n}\t{ac.t.map (· / 1000000)}"
