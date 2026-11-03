# Rowan's check: type-check + fuzz in five commands

Run from a checkout of `claude/festive-fermi-mf9mo6` (Lean 4.35 on PATH: `export PATH=$HOME/.elan/bin:$PATH`).

1. **Type-check and proofs** (builds everything; checks axioms, the Spec mirrors, FROZEN hashes; ~10-15 min):

       FUZZ=1 sh Testing/scripts/CI_check.sh

   Must end with `ALL CHECKS PASSED`. The axiom lines for `alignPairs_correct` / `alignPairs_end_to_end`
   must list only `propext, Classical.choice, Quot.sound`; their one hypothesis is `SettingsOk` (`junkScore ≤ -16`).

2. **Output fuzz on a tiny generated genome** (no data needed, ~20 s; part of step 1 with `FUZZ=1`, here alone):

       sh Testing/scripts/fuzz_ci.sh

   Must print `VIOLATIONS: none`. It checks every SAM record against its FASTQ and the genome (flags, mate
   fields, TLEN, CIGAR lengths, SEQ/QUAL windows, no CIGAR without an aligned base, no mate under 20 letters,
   XU values incl. `repetitiveUnknown`).

3. **Simulated reads vs minibwa on a real chromosome** (4 commands, see `Testing/fuzz/README.md`):

       python3 Testing/benches/sim_pairs.py G.fa fz 10000 mason 42
       lean-align map shim.idx fz_R1.fq fz_R2.fq ours.sam 100 1000
       minibwa map -t 4 mb fz_R1.fq fz_R2.fq > mb.sam
       python3 Testing/fuzz/compare_sam.py ours.sam mb.sam

4. **The hard check: is any of our claims false?** (rescores minibwa's placements in our scoring; rules A-D must be 0):

       sh Testing/repro/fuzz_audit.sh          # needs hg38 (Testing/repro/README.md, "fresh checkout")

   A: AS ≠ recomputed score · B: XB below our own pair · C: XB below a proper pair built from minibwa's placement
   (would falsify the bound) · D: `unique` but minibwa has an equal-or-better proper pair elsewhere.

5. **Unique-genome exact match** (every 15-mer unique; ours must equal minibwa byte for byte on columns 1-11):

       bash Testing/unique/run.sh OUT

Where each number comes from and how to recreate it: `Testing/repro/README.md` and
`Testing/notes/RESULTS_2026-11-02.md`.
