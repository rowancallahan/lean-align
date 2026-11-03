import Proofs.Aligner
import Proofs.Fastq

/-! # floor_prof: which pairs the report floor (`junkScore`) breaks, and what can fix them (benchmark only)

`lake exe floor_prof INDEX R1 R2 [N] [FLOOR]` (default floor −50), 1 thread. For each pair, the shim's answer
(`alignOneC`). A pair breaks the new Spec when it reports a pair below the floor, or no pair with bound ≥ −16.
For those: is the reported pair a proved best (unique / tie), so its score is a bound; are both mates on the
fast path at 16 (≥ 125 letters); then the complete pair search at 16 (`pairGXE`): seen (a pair ≥ −16 exists,
reportable) or not (no proper pair ≥ −16, `none` valid), and its time. -/

open MapSpec MapSpec.Fast Spec

deriving instance Inhabited for Spec.Uniqueness, Spec.Tier, Spec.PairAnswer

def repScore (r : PairReport) : Int := r.mate1.score + r.mate2.score

/-- (prototype) `fallbackOf`, but each anchor's pair is kept only when it reaches the floor (the walk goes on). -/
def walkOf (k : Nat) (floor : Int) (pk : PkMz) (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat)
    (R1 R2 : ByteArray) (t : TierOut) : Option PairReport :=
  let s1 : PrepM MzP := prepMate pk R1
  let s2 : PrepM MzP := prepMate pk R2
  let ok := fun (p : Option PairReport) => p.bind fun p => if floor ≤ repScore p then some p else none
  let c1 := t.m1.pl.toList ++ Report.anchorsOf pk pgs R1 s1 k
  match c1.findSome? fun x => ok (Report.pairOf slack lo hi (Report.tryAt pk pgs offs ns hi 1000000 0 R1 t.m1 R2 s2 x).1
      (Report.tryAt pk pgs offs ns hi 1000000 0 R1 t.m1 R2 s2 x).2) with
  | some p => some p
  | none =>
    let c2 := t.m2.pl.toList ++ Report.anchorsOf pk pgs R2 s2 k
    c2.findSome? fun x => ok (Report.pairOf slack lo hi (Report.tryAt pk pgs offs ns hi 1000000 0 R2 t.m2 R1 s1 x).2
      (Report.tryAt pk pgs offs ns hi 1000000 0 R2 t.m2 R1 s1 x).1)

/-- (prototype) walk the exact hits of mate `RX` within 16 (best first, at most `K`): the other mate near each, checked
(`tryAt`); the first pair at or above the floor. -/
def walkHits (K : Nat) (floor : Int) (pk : PkMz) (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat)
    (RX RY : ByteArray) (xIsMate1 : Bool) : Option PairReport :=
  let sY : PrepM MzP := prepMate pk RY
  let lX := ((hitsKPF pk ByteArray.empty #[0] pgs RX 16).toArray.qsort fun u v => v.2 < u.2).toList.take K
  lX.findSome? fun x =>
    let r := Report.tryAt pk pgs offs ns hi 1000000 0 RX {} RY sY x
    let p := if xIsMate1 then Report.pairOf slack lo hi r.1 r.2 else Report.pairOf slack lo hi r.2 r.1
    p.bind fun p => if floor ≤ repScore p then some p else none

def main (args : List String) : IO Unit := do
  let [idx, f1, f2] := args.take 3 | throw (IO.userError "usage: floor_prof INDEX R1 R2 [N] [FLOOR]")
  let lim := (args[3]?.getD "100000000").toNat!
  let floor : Int := -((args[4]?.getD "50").toNat! : Int)
  let index ← IO.FS.readBinFile idx
  let insertSettings : InsertSettings := { range := (100, 1000) }
  let some (ix, G, offs, ns) := (readIndex index).2 | throw (IO.userError "index")
  let pgs := cutAll G #[0] #[G.n]
  let pk : PkMz := (ix, G)
  let cfg := tierCfg insertSettings pk #[0] pgs
  let r1 ← FastqReader.ofHandle (← IO.FS.Handle.mk f1 .read)
  let r2 ← FastqReader.ofHandle (← IO.FS.Handle.mk f2 .read)
  let chunk ← readChunk r1 r2 lim
  let mut cnt : Std.HashMap String (Nat × Nat) := {}
  for (a0, b0) in chunk do
    let a := a0.letters
    let b := b0.letters
    if a.isEmpty || b.isEmpty then cnt := cnt.alter "trimmedAway" (fun v => some ((v.getD (0,0)).1 + 1, 0)); continue
    let ans := match alignOne insertSettings [] (some (ix, G, offs, ns)) (some a) (some b) with
      | .aligned x => x | _ => default
    let bad := match ans.found with
      | some r => decide (repScore r < floor)
      | none => decide (-16 ≤ ans.bestPossibleScore)
    let key ← if !bad then pure (match ans.found with | some _ => "ok: pair >= floor" | none => "ok: none, bound < -16") else do
      let best := match ans.found, ans.uniqueness with
        | some r, .unique => some (repScore r) | some r, .multimapper => some (repScore r) | _, _ => none
      let why := match ans.found with | some r => if r.mate1.cigar.size == 1 && r.mate2.cigar.size == 1 && r.mate1.score < -200 then "degenerate" else "pair<floor" | none => "none,bound>=-16"
      if (best.map fun s => decide (s < -16)) == some true then pure s!"1 fixed by best bound ({why})" else
      let short := if a.size < 125 && b.size < 125 then "both<125" else if a.size < 125 || b.size < 125 then "one<125" else ""
      let t := tierPair (pairCfg cfg pk a b) pk #[0] pgs (some a) (some b)
      let tw ← IO.monoNanosNow
      let w3 ← (← IO.mkRef (if tw == 0 then none else walkOf 3 floor pk insertSettings.dovetailSlack 100 1000 pgs offs ns a b t)).get
      let tw2 ← IO.monoNanosNow
      cnt := cnt.alter "walk3 [us]" (fun v => some ((v.getD (0,0)).1 + (tw2 - tw) / 1000, 0))
      if w3.isSome then pure s!"2 walk3 pair >= floor {short} ({why})" else
      let w16 ← (← IO.mkRef (if tw2 == 0 then none else walkOf 16 floor pk insertSettings.dovetailSlack 100 1000 pgs offs ns a b t)).get
      let tw3 ← IO.monoNanosNow
      cnt := cnt.alter "walk16 [us]" (fun v => some ((v.getD (0,0)).1 + (tw3 - tw2) / 1000, 0))
      if w16.isSome then pure s!"3 walk16 pair >= floor {short} ({why})" else
      if short != "" then pure s!"5 LEFTOVER short mate {short} ({why})" else
      let tj ← IO.monoNanosNow
      let j ← (← IO.mkRef (if tj == 0 then false else noPairJ 16 16 cfg.hi pk ByteArray.empty a b)).get
      let tj2 ← IO.monoNanosNow
      cnt := cnt.alter "noPairJ16 [ms]" (fun v => some ((v.getD (0,0)).1 + (tj2 - tj) / 1000000, 0))
      if j then pure s!"4a discordant (noPairJ 16): none valid ({why})" else
      let sw := decide (costP pk 16 (prepMate pk b : PrepM MzP) < costP pk 16 (prepMate pk a : PrepM MzP))
      let t0 ← IO.monoNanosNow
      let r ← (← IO.mkRef (if t0 == 0 then none else pairGXE dcost0 cfg.usl cfg.lo cfg.hi 16 sw pk #[0] pgs a b)).get
      let t1 ← IO.monoNanosNow
      if (match r with | some (_, true) => true | _ => false) then
        for K in [256, 5000] do
          let v0 ← IO.monoNanosNow
          let t' := tierPair (pairCfg cfg pk a b) pk #[0] pgs (some a) (some b)
          let w ← (← IO.mkRef (if v0 == 0 then none else walkOf K floor pk insertSettings.dovetailSlack 100 1000 pgs offs ns a b t')).get
          let v1 ← IO.monoNanosNow
          IO.println s!"WALKANCH\t{K}\t{w.isSome}\t{(v1 - v0) / 1000}"
        for K in [64] do
          let v0 ← IO.monoNanosNow
          let w ← (← IO.mkRef (if v0 == 0 then none else walkHits K floor pk insertSettings.dovetailSlack 100 1000 pgs offs ns (if sw then b else a) (if sw then a else b) (!sw))).get
          let v1 ← IO.monoNanosNow
          IO.println s!"WALKHITS\t{K}\t{w.isSome}\t{(v1 - v0) / 1000}"
        let RX := if sw then b else a
        let RY := if sw then a else b
        let u0 ← IO.monoNanosNow
        let lX ← (← IO.mkRef (if u0 == 0 then [] else hitsKPF pk ByteArray.empty #[0] pgs RX 16)).get
        let u1 ← IO.monoNanosNow
        let lY ← (← IO.mkRef (if u1 == 0 then [] else hitsKPFN cfg.usl cfg.hi pk ByteArray.empty #[0] pgs RY 16 lX)).get
        let u2 ← IO.monoNanosNow
        IO.println s!"SEEN\t{lX.length}\t{lY.length}\t{(u1 - u0) / 1000}\t{(u2 - u1) / 1000}"
      let k := match r with
        | some (_, true) => s!"4b complete16: pair >= -16 ({why})" | some (_, false) => s!"4b complete16: none valid ({why})" | none => "4 complete16 n/a"
      cnt := cnt.alter (k ++ " [ms]") (fun v => some ((v.getD (0,0)).1 + (t1 - t0) / 1000000, 0))
      pure k
    cnt := cnt.alter key (fun v => some ((v.getD (0,0)).1 + 1, 0))
  for (k, v) in cnt.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{k}\t{v.1}"
