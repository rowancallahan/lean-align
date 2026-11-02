#!/bin/bash
# Mapped / unique vs minibwa (the tables of OUTPUT_FUZZ §1-2): shim and minibwa on each set, then output_vs_minibwa.py.
#   bash Testing/repro/mapping.sh OUTDIR SET...        SET = hg38_mason hg38_low hg002_200k novaseq_200k (prefix in Testing/data/prebuilt)
# Prints section (1) (mapped, placeholder, unique, MAPQ) and the relation table (2) of each set's analysis.md. Deterministic given the binary.
set -eu
cd "$(dirname "$0")/../.."
out=$1; shift
P=Testing/data/prebuilt; MB=${MINIBWA:-minibwa}
for s in "$@"; do
  d=$out/$s; mkdir -p "$d"
  taskset -c 0-3 .lake/build/bin/lean-align map $P/shim.idx $P/${s}_R1.fq $P/${s}_R2.fq "$d/ours.sam" 100 1000
  $MB map -t 4 $P/mb $P/${s}_R1.fq $P/${s}_R2.fq > "$d/mb.sam" 2> "$d/mb.err"
  python3 -I Testing/scripts/output_vs_minibwa.py "$s" "$d/ours.sam" "$d/mb.sam" > "$d/analysis.md"
  sed -n '/### (1)/,/^Of our/p;/### (2)/,/^Same strand/p;/^Pairs both tools call unique/p' "$d/analysis.md" | grep -v '^$\|^|---'
done
