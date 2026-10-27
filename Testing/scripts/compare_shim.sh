#!/bin/sh
# Shim (lean-align build / map) vs the whole-genome bench harness (mode RTX, the same proved tierPair),
# one thread each, on chr21 and the read sets in Testing/data/downloads.   sh Testing/scripts/compare_shim.sh
set -eu
cd "$(dirname "$0")/../.."
root=$PWD; D=$root/Testing/data/downloads; B=$root/.lake/build/bin; T="python3 $root/Testing/scripts/timed.py"
O=${OUT:-${TMPDIR:-/tmp}/lean_align_compare}; mkdir -p "$O"
sets="hiseq250:hg002_200k novaseq151:novaseq_200k mason:sim_mason low:sim_low"

$T "bench build" $B/whole_genome build "$O/wg" "$D/chr21.fa"
WG_CHECK=1 WG_MODES=RTX WG_READS="" $T "bench check index (once)" $B/whole_genome pmap "$O/wg" "$D/chr21.fa" | grep -E "TIME|rror" || true
reads=""; for s in $sets; do n=${s%%:*}; f=${s#*:}; reads="$reads$n=$D/${f}_R1.fq:$D/${f}_R2.fq:0;"; done
WG_MODES=RTX WG_TASKS=1 WG_OUT="$O" WG_READS="$reads" $T "bench map (all sets)" $B/whole_genome pmap "$O/wg" "$D/chr21.fa" | grep -E "RESULT|TIME|MISMATCH|rror" || true

$T "shim build" $B/lean-align build "$D/chr21.fa" "$O/shim.idx"
for s in $sets; do n=${s%%:*}; f=${s#*:}
  $T "shim map $n" $B/lean-align map "$O/shim.idx" "$D/${f}_R1.fq" "$D/${f}_R2.fq" "$O/$n.sam" 100 1000
done
