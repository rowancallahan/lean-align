#!/bin/sh
# Output-fuzz regression on a tiny generated genome: no hg38, no download, about a minute.   sh Testing/scripts/fuzz_ci.sh
# 1. a 2 Mb genome with repeats and N runs from a fixed seed (sim_genome_dup.py), `lean-align build`;
# 2. ~2 100 simulated pairs (mason, low, high) + ~800 edge-case pairs (fuzz_reads.py) with fixed seeds;
# 3. `lean-align map`, then sam_fuzz_check.py: flags, mate fields, TLEN, CIGAR/SEQ/QUAL lengths, '*' handling,
#    provenance, no CIGAR without an aligned base, no mapped mate under 20 letters: every count must be 0.
# 4. fastq_cases.py: FASTQ edge cases (CRLF, no final newline, >1000 bases, short names, ...) accepted or rejected as Spec/Fastq says.
# Needs lake build (lean-align) and python3. Wired into CI_check.sh as `FUZZ=1 sh Testing/scripts/CI_check.sh`.
set -eu
cd "$(dirname "$0")/../.."
lean=.lake/build/bin/lean-align
d=$(mktemp -d "${TMPDIR:-/tmp}/fuzz_ci.XXXXXX"); trap 'rm -rf "$d"' EXIT
python3 -I Testing/scripts/sim_genome_dup.py "$d/g" 2 2 7 > /dev/null
"$lean" build "$d/g/all.fa" "$d/idx"
for m in mason low high; do python3 -I Testing/benches/sim_pairs.py "$d/g/all.fa" "$d/$m" 700 $m 11 > /dev/null; done
python3 -I Testing/scripts/fuzz_reads.py "$d/g/all.fa" "$d/edge" 40 3 > /dev/null
# one input pair of files; read names get the set as a prefix so they stay unique
for r in 1 2; do
  : > "$d/R$r.fq"
  for s in mason low high edge; do awk -v p="${s}_" 'NR%4==1{print "@" p substr($0,2); next}{print}' "$d/${s}_R$r.fq" >> "$d/R$r.fq"; done
done
echo "$(($(wc -l < "$d/R1.fq") / 4)) pairs"
"$lean" map "$d/idx" "$d/R1.fq" "$d/R2.fq" "$d/out.sam" 100 1000
python3 -I Testing/scripts/sam_fuzz_check.py "$d/out.sam" "$d/R1.fq" "$d/R2.fq" "$d/idx.chromosomes"
python3 -I Testing/scripts/fastq_cases.py "$lean" "$d/idx" "$d/mason_R1.fq" "$d/mason_R2.fq" "$d"
