import MapperPacked

/-!
Benchmark (unproved IO): byte-by-byte mismatch count vs the proved 2-bit
packed `hamPacked` (`pool/mapper/MapperPacked.lean`) on a one-line FASTA.

    lake exe packed_bench [genome.fa] [pairs] [len]

Two workloads, each `pairs` counts of length `len` (default 10M x 100):
  random : G[p, p+len) vs G[q, q+len), independent random ACGT windows
  similar: G[p, p+len) vs R[p-7, p-7+len), R = G[7..] with ~1% substitutions
  cached : like random, both windows inside one clean 64K-letter region (no cache misses)
Every result of the packed count is checked equal to the byte count.
-/

open MapSpec.Packed MapSpec.Mz

/-- Plain byte loop (same shape as the fast mapper's `hamming`, without the cap). -/
def hamBytes (G R : ByteArray) (p r : Nat) (i stop m : Nat) : Nat :=
  if i < stop then
    hamBytes G R p r (i + 1) stop (if G.get! (p + i) != R.get! (r + i) then m + 1 else m)
  else m
termination_by stop - i

@[inline] def rnd (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13); let x := x ^^^ (x >>> 7); x ^^^ (x <<< 17)

def cleanAt (G : ByteArray) (p len : Nat) : Bool := Id.run do
  for i in [0:len] do
    if !acgt (G.get! (p + i)) then return false
  return true

/-- `n` random starts `p ∈ [lo, hi)` with `G[p, p+len)` all ACGT. -/
def positions (G : ByteArray) (n len lo : Nat) (seed : UInt64) (hi : Nat := G.size - len) :
    Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity n
  let mut x := seed
  while out.size < n do
    x := rnd x
    let p := (x >>> 11).toNat % hi
    if p ≥ lo && cleanAt G p len then out := out.push p
  return out

def runBytes (G R : ByteArray) (ps rs : Array Nat) (len : Nat) : Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity ps.size
  for k in [0:ps.size] do
    out := out.push (hamBytes G R ps[k]! rs[k]! 0 len 0)
  return out

def runPacked (pG pR : Array UInt64) (ps rs : Array Nat) (len : Nat) : Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity ps.size
  for k in [0:ps.size] do
    out := out.push (hamPacked pG pR ps[k]! rs[k]! len)
  return out

def sumA (a : Array Nat) : Nat := a.foldl (· + ·) 0

def timeIt (label : String) (f : Unit → Array Nat) : IO (Array Nat) := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  let s := sumA r
  if s == 1 then IO.println ""
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  IO.println s!"  {label}: {ms} ms  ({(t1 - t0) / max 1 r.size} ns/count, sum {s})"
  return r

def main (args : List String) : IO UInt32 := do
  let path := args.getD 0 "/home/user/data/chr21.1l.fa"
  let n := (args.getD 1 "10000000").toNat!
  let len := (args.getD 2 "100").toNat!
  let raw ← IO.FS.readBinFile path
  let mut h := 0
  while h < raw.size && raw.get! h != 10 do h := h + 1
  let mut e := h + 1
  while e < raw.size && raw.get! e != 10 do e := e + 1
  let G := raw.extract (h + 1) e
  IO.println s!"genome {G.size} letters; {n} counts of length {len}"
  -- R: G shifted by 7 with ~1% substitutions at ACGT letters
  let mut R := G.extract 7 G.size
  let mut x : UInt64 := 0x9E3779B97F4A7C15
  for i in [0:R.size] do
    x := rnd x
    let c := R.get! i
    if acgt c && x % 100 == 0 then
      R := R.set! i (if c == 65 then 67 else 65)
  let t0 ← IO.monoNanosNow
  let pG := packGenome G
  let pR := packGenome R
  let am := packAcgt G
  if pG.size + pR.size + am.size == 0 then IO.println ""
  let t1 ← IO.monoNanosNow
  IO.println s!"packing G, R and the ACGT mask: {(t1 - t0) / 1000000} ms ({pG.size} words each)"
  let mut ok := true
  -- the proved ACGT check agrees with the byte check on some windows
  let ws := positions G 100000 len 0 12345
  for p in ws do
    if !allAcgt am p len then ok := false
  let mut y : UInt64 := 777
  let mut nBad := 0
  for _ in [0:200000] do
    y := rnd y
    let p := (y >>> 11).toNat % (G.size - len)
    if allAcgt am p len != cleanAt G p len then ok := false
    if !cleanAt G p len then nBad := nBad + 1
  IO.println s!"allAcgt vs byte check on 300000 windows ({nBad} not clean): {if ok then "agree" else "DIFFER"}"
  -- "cached": both windows inside one 64K-letter clean region (compute cost, no cache misses)
  let c0 := (positions G 1 65536 0 99)[0]!
  for (name, Rb, pRb, shift, lo, hi) in [("random", G, pG, 0, 7, G.size - len),
      ("similar", R, pR, 7, 7, G.size - len), ("cached", G, pG, 0, c0, c0 + 65536 - len)] do
    let ps := positions G n len lo (if shift == 0 then 1 else 2) hi
    let rs := if shift == 0 then positions G n len lo 3 hi else ps.map (· - 7)
    IO.println s!"{name}:"
    let a ← timeIt "byte loop " fun _ => runBytes G Rb ps rs len
    let b ← timeIt "hamPacked " fun _ => runPacked pG pRb ps rs len
    let same := a == b
    IO.println s!"  results equal: {same}"
    if !same then ok := false
  return (if ok then 0 else 1)
