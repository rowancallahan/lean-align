import Proofs.Aligner
import Proofs.Fastq

/-! # floor_pipe: the cheap report-floor pipeline and repeat witnesses (benchmark only, unproved IO)

`floor_pipe INDEX R1 R2 [N]`, 1 thread. Per pair: today's answer (`alignOne`). With Rowan's length-scaled bound
(`e = min 4 (len/25 − 1)` for the shorter mate, `rmb = −4e`), a pair breaks the Spec at floor F when it reports a pair
below F, or no pair with bound ≥ rmb. Steps, in order, each with its CPU: (a) free: the router's bound, or a proved
best pair's own score, below rmb; (b) walk, 3 anchors per strand, first checked pair ≥ F; (c) anchor join `noPairJ`
at caps 4e / 4e; (d) short mates (e < 4) only: `pairGXE` at 4e when the rarest `e + 1` buckets per strand of both
mates hold ≤ 1000 places. The rest give up. For those: the largest exact occurrence count of a looked-up 25-letter seed
(either mate, either strand; witness at N = 200 / 500 / 1000 / 5000), and the complete search's CPU (`pairGXE` at 4e).
Both floors (−50, −100) in one pass. -/

open MapSpec MapSpec.Fast Spec

deriving instance Inhabited for Spec.Uniqueness, Spec.Tier, Spec.PairAnswer

def repScore (r : PairReport) : Int := r.mate1.score + r.mate2.score

def walkOf (k : Nat) (floor : Int) (pk : PkMz) (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat)
    (R1 R2 : ByteArray) (t : TierOut) : Option PairReport :=
    let s1 : PrepM MzP := prepMate pk R1
    let s2 : PrepM MzP := prepMate pk R2
    let ok := fun (p : Option PairReport) => p.bind fun p => if floor ≤ repScore p then some p else none
    let c1 := t.m1.pl.toList ++ Report.anchorsOf pk pgs R1 s1 k
    match c1.findSome? fun x => ok (Report.pairOf slack lo hi (Report.tryAt pk pgs offs ns hi 1000000 R1 t.m1 R2 s2 x).1
        (Report.tryAt pk pgs offs ns hi 1000000 R1 t.m1 R2 s2 x).2) with
    | some p => some p
    | none =>
      let c2 := t.m2.pl.toList ++ Report.anchorsOf pk pgs R2 s2 k
      c2.findSome? fun x => ok (Report.pairOf slack lo hi (Report.tryAt pk pgs offs ns hi 1000000 R2 t.m2 R1 s1 x).2
        (Report.tryAt pk pgs offs ns hi 1000000 R2 t.m2 R1 s1 x).1)

-- the largest exact occurrence count of a seed of `R` (both strands' seeds)
def maxOcc (pk : PkMz) (R : ByteArray) : Nat := Id.run do
  let s : PrepM MzP := prepMate pk R
  let n := R.size
  let m := n / 25
  if m == 0 then return 0
  let Ls := n / m
  let mut best := 0
  for b in [0:2] do
    let pp := if b == 0 then s.ps else s.pr
    let Rx := if b == 0 then R else s.Rr
    for j in [0:m] do
      if pp[j]!.ok then
        let c := (LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!).size
        if best < c then best := c
  return best

def rareSum (pk : PkMz) (R : ByteArray) (k : Nat) : Nat :=
  let s : PrepM MzP := prepMate pk R
  TierHeur.smallK pk s.ps (R.size / 25) k + TierHeur.smallK pk s.pr (R.size / 25) k

/-- (prototype) `anchAll` over only the `k` seeds with the smallest buckets. -/
def anchRare (pk : PkMz) (R : ByteArray) (k : Nat) : List Nat :=
  let m := R.size / 25
  let Ls := R.size / m
  let ps := (List.range m).map fun j => (j, LookG.prep pk (seedHashAt R (j * Ls)))
  let sel := ((ps.toArray.qsort fun x y => LookG.size pk x.2 < LookG.size pk y.2).toList.take k)
  sel.foldl (fun acc (j, p) => List.merge acc
    ((LookG.look pk ByteArray.empty R (j * Ls) (R.size - j * Ls) p).toList.map (· / 16)) (fun a b => decide (a ≤ b))) []

/-- (prototype) `noPairJ` joining only the rarest `sbound P + 1` seeds per strand (still sound by pigeonhole). -/
def noPairJR (P1 P2 hi : Nat) (pk : PkMz) (R1 R2 : ByteArray) : Bool :=
  fastT P1 R1 && fastT P2 R2 &&
    (let W := joinW P1 P2 hi R1.size R2.size
     let f1 := anchRare pk R1 (sbound P1 + 1)
     let r2 := anchRare pk (revCompK R2) (sbound P2 + 1)
     !nearAnyF W (f1.length + r2.length + 1) f1 r2 &&
       (let r1 := anchRare pk (revCompK R1) (sbound P1 + 1)
        let f2 := anchRare pk R2 (sbound P2 + 1)
        !nearAnyF W (r1.length + f2.length + 1) r1 f2))

def main (args : List String) : IO Unit := do
  let [idx, f1, f2] := args.take 3 | throw (IO.userError "usage: floor_pipe INDEX R1 R2 [N]")
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
  let t00 ← IO.monoNanosNow
  for (a0, b0) in chunk do
    let a := a0.letters
    let b := b0.letters
    if a.isEmpty || b.isEmpty then cnt := add cnt "trimmedAway" 1; continue
    let q0 ← IO.monoNanosNow
    let ans ← (← IO.mkRef (if q0 == 0 then default else match alignOne insertSettings [] (some (ix, G, offs, ns)) (some a) (some b) with
      | .aligned x => x | _ => default)).get
    let q1 ← IO.monoNanosNow
    cnt := add cnt "map [us]" ((q1 - q0) / 1000)
    let minLen := min a.size b.size
    let e := min 4 (minLen / 25 - 1)
    let rmb : Int := -4 * (e : Int)
    let cap := 4 * e
    for floor in [(-50 : Int), -100] do
      let F := s!"F{floor}"
      let bad := match ans.found with
        | some r => decide (repScore r < floor)
        | none => decide (rmb ≤ ans.bestPossibleScore)
      if !bad then cnt := add cnt s!"{F} 0 ok" 1; continue
      let degen := match ans.found with | some r => decide (r.mate1.score < -200) | none => false
      let why := if degen then "degen" else if ans.found.isSome then "pair<F" else "none"
      -- (a) free
      let best := match ans.found, ans.uniqueness with
        | some r, .unique => some (repScore r) | some r, .multimapper => some (repScore r) | _, _ => none
      let bnd := match best with | some s => min s ans.bestPossibleScore | none => ans.bestPossibleScore
      if bnd < rmb then cnt := add cnt s!"{F} a free" 1; continue
      -- (b) walk, 3 anchors per strand
      let w0 ← IO.monoNanosNow
      let t := tierPair (pairCfg cfg pk a b) pk #[0] pgs (some a) (some b)
      let w ← (← IO.mkRef (if w0 == 0 then none else walkOf 3 floor pk insertSettings.dovetailSlack 100 1000 pgs offs ns a b t)).get
      let w1 ← IO.monoNanosNow
      cnt := add cnt s!"{F} b walk3 [us]" ((w1 - w0) / 1000)
      if w.isSome then cnt := add cnt s!"{F} b walk3" 1; continue
      -- (c) anchor join at caps 4e / 4e
      -- the join's lookup cost: the rarest sbound(cap)+1 buckets per strand of both mates
      let jcost := rareSum pk a (sbound cap + 1) + rareSum pk b (sbound cap + 1)
      let jb := if jcost ≤ 2000 then "<=2k" else if jcost ≤ 5000 then "<=5k" else if jcost ≤ 20000 then "<=20k" else ">20k"
      let j ← (← IO.mkRef (if w1 == 0 || 20000 < jcost then false else (tierNo cfg pk #[0] pgs cap false false a b).isSome)).get
      let j1 ← IO.monoNanosNow
      cnt := add cnt s!"{F} c noPairJ [us]" ((j1 - w1) / 1000)
      cnt := add cnt s!"{F} c join cost {jb} [us]" ((j1 - w1) / 1000)
      cnt := add cnt s!"{F} c join cost {jb} tried" 1
      if j then cnt := add cnt s!"{F} c join cost {jb} proved" 1
      if j then
        cnt := add cnt s!"{F} c noPairJ" 1
        -- without (c): this pair goes to (d) if short and cheap, else to the witness test / complete search
        let short := decide (minLen < 125)
        let budget := rareSum pk a (e + 1) + rareSum pk b (e + 1)
        if short && budget ≤ 1000 then cnt := add cnt s!"{F} noC d" 1; continue
        let occ := max (maxOcc pk a) (maxOcc pk b)
        let wit := if occ ≥ 5000 then ">=5000" else if occ ≥ 1000 then "1000-4999" else if occ ≥ 500 then "500-999" else if occ ≥ 200 then "200-499" else "<200"
        let g0 ← IO.monoNanosNow
        let r ← (← IO.mkRef (if g0 == 0 then none else pairGXE dcost0 cfg.usl cfg.lo cfg.hi cap false pk #[0] pgs a b)).get
        let g1 ← IO.monoNanosNow
        cnt := add cnt s!"{F} noC occ {wit}" 1
        cnt := add cnt s!"{F} noC occ {wit} [ms]" ((g1 - g0) / 1000000)
        if (match r with | some (_, false) => false | _ => true) then cnt := add cnt s!"{F} noC occ {wit} search undecided" 1
        continue
      -- (d) short mates: pairGXE at 4e under a tiny budget
      let short := decide (minLen < 125)
      let band := if minLen < 50 then "<50" else if minLen < 75 then "50-75" else if minLen < 100 then "75-100" else if minLen < 125 then "100-125" else ">=125"
      if short then
        let budget := rareSum pk a (e + 1) + rareSum pk b (e + 1)
        if budget ≤ 1000 then
          let d0 ← IO.monoNanosNow
          let r ← (← IO.mkRef (if d0 == 0 then none else pairGXE dcost0 cfg.usl cfg.lo cfg.hi cap false pk #[0] pgs a b)).get
          let d1 ← IO.monoNanosNow
          cnt := add cnt s!"{F} d shortcap [us]" ((d1 - d0) / 1000)
          match r with
          | some (_, false) => cnt := add cnt s!"{F} d shortcap none-valid" 1; continue
          | some (_, true) => cnt := add cnt s!"{F} d shortcap pair>=rmb (not reportable yet)" 1; continue
          | none => pure ()
      -- gave up: witness and complete-search cost
      let occ := max (maxOcc pk a) (maxOcc pk b)
      let wit := if occ ≥ 5000 then ">=5000" else if occ ≥ 1000 then "1000-4999" else if occ ≥ 500 then "500-999" else if occ ≥ 200 then "200-499" else "<200"
      let g0 ← IO.monoNanosNow
      let r ← (← IO.mkRef (if g0 == 0 then none else pairGXE dcost0 cfg.usl cfg.lo cfg.hi cap false pk #[0] pgs a b)).get
      let g1 ← IO.monoNanosNow
      let res := match r with | some (_, true) => "pair" | some (_, false) => "none" | none => "n/a"
      cnt := add cnt s!"{F} e GAVEUP {if short then "short " ++ band else "long"} occ {wit} ({why})" 1
      cnt := add cnt s!"{F} e GAVEUP occ {wit}: complete search {res}" 1
      cnt := add cnt s!"{F} e GAVEUP occ {wit}: complete search [ms]" ((g1 - g0) / 1000000)
  let t01 ← IO.monoNanosNow
  IO.println s!"pairs\t{chunk.size}\ttotal s\t{(t01 - t00) / 1000000000}"
  for (k, v) in cnt.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{k}\t{v}"
