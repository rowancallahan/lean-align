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
  let t0 ← IO.monoNanosNow
  let res ← (← IO.mkRef (rs.map (Fast.mapFastTG P #[g] #[idx]))).get
  let t1 ← IO.monoNanosNow
  IO.println s!"mapped {(res.filter (·.isSome)).size}  seconds {Float.ofNat (t1 - t0) / 1e9}"
  return 0
