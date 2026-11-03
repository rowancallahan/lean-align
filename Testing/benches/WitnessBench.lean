import Proofs.Sam
/-! Measurement only (NOT proved, not part of the tool): how many pairs a witness-first check would catch.

    lake exe witness_bench INDEX R1.fq R2.fq N MODE OUT
    MODE: size (bucket sizes only) | fwd (verify forward places) | both (forward + reverse-complement places)
    OUT: 0-based indices of caught pairs, one per line. -/
open MapSpec MapSpec.Fast Spec

-- in-chromosome places among the first `N` of a seed's lookup (a lower bound on its occurrences on that strand)
def placesLB (pk : PkMz) (offs ns : Array Nat) (R : ByteArray) (s N : Nat) (p : MzP) : Nat :=
  let a := lookupPWk pk.1 pk.2 R s p 0 0 N
  ((a.extract 0 N).toList.countP fun e => GaveUp.inChrom offs ns (e / 16))

def bucket (pk : PkMz) (p : MzP) : Nat := if p.ok then pk.1.hiB p.b - pk.1.loB p.b else 0

-- seed `j` of mate `R` repeats at least `N` times (lower bound), or its bucket allows it (`size` mode)
def seedRep (mode : String) (pk : PkMz) (offs ns : Array Nat) (R Rr : ByteArray) (N j : Nat) : Bool :=
  let s := 25 * j
  let p := mzPrep pk.1 (seedHashAt R s)
  let sr := R.size - s - 25
  let pr := mzPrep pk.1 (seedHashAt Rr sr)
  let bf := bucket pk p
  let br := bucket pk pr
  if mode == "size" then decide (N ≤ bf) || (decide (N ≤ bf + br) && mode == "both")
  else if mode == "fwd" then
    decide (N ≤ bf) && p.ok && decide (N ≤ placesLB pk offs ns R s N p)
  else
    if decide (bf + br < N) then false else
    let cf := if p.ok && decide (0 < bf) then placesLB pk offs ns R s N p else 0
    if N ≤ cf then true else
    let cr := if pr.ok && decide (0 < br) then placesLB pk offs ns Rr sr N pr else 0
    decide (N ≤ cf + cr)

def mateRep (mode : String) (pk : PkMz) (offs ns : Array Nat) (R : ByteArray) (N : Nat) : Bool :=
  let Rr := revCompK R
  let sizeOk := ((List.range (R.size / 25)).countP fun j =>
    let s := 25 * j
    decide (N ≤ bucket pk (mzPrep pk.1 (seedHashAt R s)) +
      (if mode == "both" then bucket pk (mzPrep pk.1 (seedHashAt Rr (R.size - s - 25))) else 0))) ≥ 2
  if mode == "size" then sizeOk
  else sizeOk && GaveUp.countGE (fun j => seedRep mode pk offs ns R Rr N j) 2 (List.range (R.size / 25))

def main (args : List String) : IO UInt32 := do
  match args with
  | [indexPath, r1, r2, nS, mode, outPath] =>
    let N := nS.toNat!
    let index ← IO.FS.readBinFile indexPath
    let some (ix, G, offs, ns) := (readIndex index).2 | throw (IO.userError "no index")
    let pk : PkMz := (ix, G)
    let reads1 ← FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
    let reads2 ← FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
    let chunk ← readChunk reads1 reads2 1000000
    let mut caught := 0
    let mut out := ""
    let mut i := 0
    for (a, b) in chunk do
      let ra : ByteArray := a.letters
      let rb : ByteArray := b.letters
      if (!ra.isEmpty && mateRep mode pk offs ns ra N) || (!rb.isEmpty && mateRep mode pk offs ns rb N) then
        caught := caught + 1
        out := out ++ s!"{i}\n"
      i := i + 1
    IO.FS.writeFile outPath out
    IO.println s!"pairs {chunk.size} caught {caught} mode {mode} N {N}"
    return 0
  | _ => IO.eprintln "usage: witness_bench INDEX R1 R2 N MODE OUT"; return 1
