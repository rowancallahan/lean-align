#!/bin/bash
# Real-data comparison and rescoring of REAL_VS_MINIBWA: shim and minibwa on NovaSeq and HiSeq 200k, then real_vs_minibwa.py and rescore_unique.py.
#   bash Testing/repro/real_rescore.sh OUTDIR
# rescore_unique.py reads the 3 GB genome (Testing/data/downloads/hg38.upper.fa = the release's genome.fa).
set -eu
cd "$(dirname "$0")/../.."
o=$1; mkdir -p "$o"; P=Testing/data/prebuilt; MB=${MINIBWA:-minibwa}
for s in novaseq_200k hg002_200k; do
  taskset -c 0-3 .lake/build/bin/lean-align map $P/shim.idx $P/${s}_R1.fq $P/${s}_R2.fq "$o/$s.ours.sam" 100 1000
  $MB map -t 4 $P/mb $P/${s}_R1.fq $P/${s}_R2.fq > "$o/$s.mb.sam" 2> "$o/$s.mb.err"
  python3 -I Testing/fuzz/real_vs_minibwa.py $s "$o/$s.ours.sam" "$o/$s.mb.sam" $P/${s}_R1.fq $P/${s}_R2.fq > "$o/$s.report.md"
  mv "$s.examples.tsv" "$o/"                       # the script writes its examples file into the current directory
  python3 -I Testing/fuzz/rescore_unique.py $s "$o/$s.ours.sam" "$o/$s.mb.sam" $P/${s}_R1.fq $P/${s}_R2.fq Testing/data/downloads/hg38.upper.fa > "$o/$s.rescore.md"
  echo "=== $s"; grep -h "\[ALARMING\] |" "$o/$s.report.md"; grep -h "BUG? count" "$o/$s.rescore.md"
done
