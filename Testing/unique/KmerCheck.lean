-- Runs the proved checker `UniqueGenome.checkUnique` on a FASTA (read with the shim's own `Spec.readFasta`).
--   kmer_check GENOME.fa K      exit 0 = every K-mer occurs once on both strands (then `genome_windows_far` applies)
import Proofs.Fasta
import UniqueGenome

def main (args : List String) : IO UInt32 := do
  let [fasta, kText] := args | throw (IO.userError "usage: kmer_check GENOME.fa K")
  let k := kText.toNat!
  let genome ← Spec.readFasta (← IO.FS.Handle.mk fasta .read)
  let S := UniqueGenome.strands (genome.map (·.2))
  let kmers := S.foldl (fun n s => n + (s.size + 1 - k)) 0
  let ok := UniqueGenome.checkUnique k S
  IO.println s!"{genome.size} chromosomes, {S.size} strands, {S.foldl (· + ·.size) 0} letters, {kmers} {k}-mers"
  IO.println (if ok then s!"PASS: every {k}-mer occurs once on both strands; for 150-letter windows d = {150 / k - 1}"
    else s!"FAIL: some {k}-mer occurs twice")
  return if ok then 0 else 1
