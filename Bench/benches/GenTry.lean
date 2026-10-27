import FastGenAlgo

/-!
Experiments on the general fast path (IO only, unproved; the index is not checked).

    lake exe gen_try <genome.fa> <reads.txt>      env GEN_T=P, GEN_BOTH=1

Prints mapping time and, per mapping, the total number of anchors of all seeds.
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

def revComp (r : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.emptyWithCapacity r.size
  for i in [0:r.size] do
    let c := r.get! (r.size - 1 - i)
    o := o.push (if c == 65 then 84 else if c == 84 then 65 else if c == 67 then 71 else if c == 71 then 67 else c)
  return o

def anchors (ix : Fast.HIdx) (G R : ByteArray) : Nat := Id.run do
  let m := R.size / 25
  let Ls := R.size / m
  let mut n := 0
  for j in [0:m] do
    n := n + (Fast.lookupHG ix G R (j * Ls) 0 0 (Fast.seedHashAt R (j * Ls))).size
  return n

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def ker16a (R : ByteArray) (gbs : Array ByteArray) (c st len : Nat) : Nat :=
  let k := Fast.kerG R gbs[c]! st len 15
  if k ≤ 15 then k
  else if st + len ≤ gbs[c]!.size ∧ len = R.size ∧ Fast.hamming R gbs[c]! st 4 0 R.size 0 = 4 then 16
  else if Fast.filt16 R gbs[c]! st len then 16 else 17

def ker16b (R : ByteArray) (gbs : Array ByteArray) (c st len : Nat) : Nat :=
  let k := Fast.kerG R gbs[c]! st len 15
  if k ≤ 15 then k
  else if Fast.filt16 R gbs[c]! st len then 16 else 17

/-- Stage-by-stage profile of `chromG` (one chromosome, start from `initP`). -/
def prof (P : Nat) (g : ByteArray) (idx : Fast.HIdx) (rs : Array ByteArray) : IO Unit := do
  let lim := min P 16
  let gbs := #[g]
  let setup := rs.map fun R =>
    let m := R.size / 25
    let Ls := R.size / m
    let ps := (Array.range m).map fun j => Fast.seedHashAt R (j * Ls)
    (R, Ls, ps, Fast.ordG (ps.map (Fast.sizeH idx)) m)
  let t0 ← IO.monoNanosNow
  let r1s ← (← IO.mkRef (setup.map fun (R, Ls, ps, ord) =>
    Fast.phase1 idx R gbs 0 P lim Ls ps ord [] [] (Fast.initP P))).get
  let t1 ← IO.monoNanosNow
  let ks := (setup.zip r1s).map fun ((R, _, _, _), r1) =>
    let Q1 := min r1.1.pen P
    if 0 < gapBound sc0 (-(Q1 : Int)) then
      some (R, (Fast.shapesAt Q1).filter (· != (0, 0)),
        Fast.diagsB r1.2.1 (r1.2.1.length - Fast.sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int))), r1.1)
    else none
  let nK := (ks.filter (·.isSome)).size
  let dK := ks.foldl (fun n x => n + (x.map (·.2.2.1.length)).getD 0) 0
  let t2 ← IO.monoNanosNow
  let b2s ← (← IO.mkRef ((ks.zip r1s).map fun (k, r1) => match k with
    | some (R, shs, ds, b1) => Fast.stageK R gbs 0 lim shs ds b1
    | none => r1.1)).get
  let t3 ← IO.monoNanosNow
  let bs := ((setup.zip r1s).zip b2s).map fun (((R, _, _, _), r1), b2) =>
    let Q2 := min b2.pen P
    if lim < Q2 then
      some (R, Fast.shapesAt Q2, Fast.shifts (gapBound sc0 (-(Q2 : Int))),
        Fast.diagsB r1.2.1 (r1.2.1.length - Fast.sbound P) (2 * gapBound sc0 (-(Q2 : Int))), b2)
    else none
  let nB := (bs.filter (·.isSome)).size
  let dB := bs.foldl (fun n x => n + (x.map (·.2.2.2.1.length)).getD 0) 0
  let pB := bs.foldl (fun n x => n + (x.map fun y => y.2.2.2.1.length * y.2.2.1.length).getD 0) 0
  let t4 ← IO.monoNanosNow
  let b3s ← (← IO.mkRef (bs.map fun x => match x with
    | some (R, shs, sh, ds, b2) => (Fast.stageB P R gbs 0 shs sh ds b2).pen
    | none => 0)).get
  let t5 ← IO.monoNanosNow
  let anc := r1s.foldl (fun n r1 => n + r1.2.1.foldl (· + ·.size) 0) 0
  let looks := r1s.foldl (fun n r1 => n + r1.2.2.length) 0
  IO.println s!"mappings {rs.size}: lookups {looks} anchors {anc}"
  let fc := (setup.zip r1s).foldl (fun (n, f, b) ((R, _, _, _), r1) => r1.2.1.foldl (fun (n, f, b) arr =>
    arr.foldl (fun (n, f, b) e =>
      let st := e / 16 - R.size
      if e / 16 < R.size then (n, f, b) else
      if Fast.kerG R g st R.size 15 ≤ 15 then (n, f, b) else
      if Fast.filt16 R g st R.size then (n + 1, f + 1, b + (if Fast.bandPen 16 R gbs ⟨0, st, R.size⟩ ≤ 16 then 1 else 0))
      else (n + 1, f, b)) (n, f, b)) (n, f, b)) (0, 0, 0)
  IO.println s!"phase1 windows above 15: {fc.1}, pass filt16: {fc.2.1}, of which pen 16: {fc.2.2}"
  let ws := (setup.zip r1s).foldl (fun acc ((R, _, _, _), r1) => r1.2.1.foldl (fun acc arr =>
    arr.foldl (fun acc e => if e / 16 < R.size then acc else acc.push (R, e / 16 - R.size)) acc) acc) #[]
  let u0 ← IO.monoNanosNow
  let s1 ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + Fast.kerG R g st R.size 15) 0)).get
  let u1 ← IO.monoNanosNow
  let s2 ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + (if Fast.filt16 R g st R.size then 1 else 0)) 0)).get
  let u2 ← IO.monoNanosNow
  let s3 ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + Fast.ker16 R gbs 0 st R.size) 0)).get
  let u3 ← IO.monoNanosNow
  let s4 ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + ker16a R gbs 0 st R.size) 0)).get
  let u4 ← IO.monoNanosNow
  let s5 ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + ker16b R gbs 0 st R.size) 0)).get
  let u5 ← IO.monoNanosNow
  let nb := ws.foldl (fun a (R, st) => a + (if Fast.kerG R g st R.size 15 = 16 ∧ ¬ (st + R.size ≤ g.size ∧ Fast.hamming R g st 4 0 R.size 0 = 4) ∧ Fast.filt16 R g st R.size then 1 else 0)) 0
  let v0 ← IO.monoNanosNow
  let sb ← (← IO.mkRef (ws.foldl (fun a (R, st) => a + (if Fast.kerG R g st R.size 15 = 16 ∧ ¬ (st + R.size ≤ g.size ∧ Fast.hamming R g st 4 0 R.size 0 = 4) ∧ Fast.filt16 R g st R.size then Fast.bandPen 16 R gbs ⟨0, st, R.size⟩ else 0)) 0)).get
  let v1 ← IO.monoNanosNow
  IO.println s!"band calls {nb}: {secs v0 v1} s ({sb})"
  IO.println s!"ker16a {secs u3 u4} s ({s4}) ker16b {secs u4 u5} s ({s5})"
  IO.println s!"{ws.size} windows: kerG15 {secs u0 u1} s ({s1}), filt16 {secs u1 u2} s ({s2}), ker16 {secs u2 u3} s ({s3})"
  IO.println s!"phase1 {secs t0 t1} s; stage K: {nK} mappings, {dK} diagonals, {secs t2 t3} s (diag selection {secs t1 t2} s)"
  IO.println s!"stage B: {nB} mappings, {dB} diagonals, {pB} banded passes, {secs t4 t5} s (diag selection {secs t3 t4} s; {b3s.size})"

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: _ := args | return 2
  let ls := lines (← IO.FS.readBinFile gpath)
  let g := ls[1]!
  let rl := (lines (← IO.FS.readBinFile rpath)).filter (·.size > 0)
  let reads := (Array.range (rl.size / 2)).map fun i => rl[2 * i + 1]!
  let P := ((← IO.getEnv "GEN_T").getD "16").toNat!
  let both := (← IO.getEnv "GEN_BOTH").isSome
  let idx := Fast.buildIdx g
  let rs := if both then reads ++ reads.map revComp else reads
  let an := rs.map (anchors idx g)
  IO.println s!"mappings {rs.size}: anchors mean {Float.ofNat (an.foldl (· + ·) 0) / Float.ofNat rs.size} max {an.foldl max 0}"
  if (← IO.getEnv "GEN_PROF").isSome then prof P g idx rs
  let t0 ← IO.monoNanosNow
  let res ← (← IO.mkRef (rs.map (Fast.mapFastTG P #[g] #[idx]))).get
  let t1 ← IO.monoNanosNow
  IO.println s!"mapped {(res.filter (·.isSome)).size}  seconds {Float.ofNat (t1 - t0) / 1e9}"
  return 0
