#!/bin/bash
# The hg38 fuzz of FUZZ_SEEDS: Testing/fuzz/README.md's four commands for SEEDS x MODES, then audit_vs_minibwa.py (rules A-E).
#   bash Testing/repro/fuzz_audit.sh OUTDIR [PAIRS=10000] ["1 2 3"] ["mason low high"]
# Per mode the seeds are mapped in ONE run (names get an x<seed>_ prefix) so each tool loads its index once; minibwa's insert-size estimate is then per mode.
set -eu
cd "$(dirname "$0")/../.."
o=$1; n=${2:-10000}; seeds=${3:-"1 2 3"}; modes=${4:-"mason low high"}
P=Testing/data/prebuilt; MB=${MINIBWA:-minibwa}; mkdir -p "$o"
[ -s "$o/hg38.1l.fa" ] || awk '/^>/{if(c)print ""; print; c=1; next}{printf "%s", $0} END{print ""}' Testing/data/downloads/hg38.upper.fa > "$o/hg38.1l.fa"
for m in $modes; do
  for r in 1 2; do : > "$o/all_${m}_R$r.fq"; done
  for s in $seeds; do
    python3 -I Testing/benches/sim_pairs.py "$o/hg38.1l.fa" "$o/fz_${m}_$s" $n $m $s > /dev/null
    for r in 1 2; do awk -v p="x${s}_" 'NR%4==1{print "@" p substr($0,2); next}{print}' "$o/fz_${m}_${s}_R$r.fq" >> "$o/all_${m}_R$r.fq"; done
  done
  .lake/build/bin/lean-align map $P/shim.idx "$o/all_${m}_R1.fq" "$o/all_${m}_R2.fq" "$o/ours_$m.sam" 100 1000
  $MB map -t 4 $P/mb "$o/all_${m}_R1.fq" "$o/all_${m}_R2.fq" > "$o/mb_$m.sam" 2> "$o/mb_$m.err"
  for s in $seeds; do
    for t in ours mb; do awk -v p="x${s}_" '/^@/ || index($1,p)==1' "$o/${t}_$m.sam" > "$o/${t}_${m}_$s.sam"; done
    echo "--- $m seed $s"
    python3 -I Testing/fuzz/compare_sam.py "$o/ours_${m}_$s.sam" "$o/mb_${m}_$s.sam" | tail -1
    python3 -I Testing/fuzz/audit_vs_minibwa.py "$o/ours_${m}_$s.sam" "$o/mb_${m}_$s.sam" "$o/hg38.1l.fa" "$m seed $s" | grep -E "HARD|info C|info H"
  done
done
