import Proofs.Sam

/-! Benchmark only (unproved IO): for the pairs named in NAMES (one per line), how many grid seeds (offsets
0, 25, 50, …) of each trimmed mate lie inside chromosomes at least `gaveUpRepeats` times (`GaveUp.seedCount`).
  gaveup_k INDEX R1.fq R2.fq NAMES  →  lines "name k1 k2" -/

def main (args : List String) : IO Unit := do
  let [indexPath, r1, r2, namesPath] := args | throw (IO.userError "usage: gaveup_k INDEX R1 R2 NAMES")
  let names := (← IO.FS.lines namesPath).foldl (fun s n => s.insert n) (Std.HashSet.emptyWithCapacity 1024)
  let index ← IO.FS.readBinFile indexPath
  let some (ix, G, offs, ns) := (Spec.readIndex index).2 | throw (IO.userError "no router index")
  let kOf (R : ByteArray) : Nat :=
    (List.range (R.size / Spec.seedLength)).countP fun j =>
      Spec.gaveUpRepeats ≤ Spec.GaveUp.seedCount (ix, G) offs ns R (Spec.seedLength * j)
  let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
  let reads2 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
  repeat
    let some a ← Spec.readFastqRecord reads1 | break
    let some b ← Spec.readFastqRecord reads2 | break
    let n := Spec.mateName a.name
    if names.contains n then
      let a := Spec.trimRecord a
      let b := Spec.trimRecord b
      IO.println s!"{n} {kOf a.letters} {kOf b.letters}"
