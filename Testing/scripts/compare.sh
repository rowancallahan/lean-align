#!/bin/sh
# Speed comparison on one genome and the read sets in Testing/data/downloads:
#   shim     .lake/build/bin/lean-align (Main.lean: build, then map), 1 thread
#   bench    .lake/build/bin/whole_genome, mode RTX (the same proved tierPair), 1 and 4 tasks
#   minibwa  default build and -march=native build, 1 and 4 threads
# Runs one after another, nothing else on the box.   sh Testing/scripts/compare.sh [genome.fa]
# SETS="hiseq250:hg002_200k" limits the read sets (name:file prefix in Testing/data/downloads).
# Needs: lake build whole_genome; MINIBWA (default build) and MINIBWA_NATIVE set to the two binaries.
set -eu
cd "$(dirname "$0")/../.."
root=$PWD; D=$root/Testing/data/downloads; B=$root/.lake/build/bin
T="python3 $root/Testing/scripts/timed.py"
G=${1:-$D/chr21.fa}; O=${OUT:-${TMPDIR:-/tmp}/lean_align_compare}; mkdir -p "$O"
sets=${SETS:-"hiseq250:hg002_200k novaseq151:novaseq_200k mason:sim_mason low:sim_low"}

echo "== index"
$T "shim build" $B/lean-align build "$G" "$O/shim.idx"
$T "bench build" $B/whole_genome build "$O/wg" "$G"
WG_CHECK=1 WG_MODES=RTX WG_READS="" $T "bench check index (once)" $B/whole_genome pmap "$O/wg" "$G" >/dev/null
$T "minibwa index" "$MINIBWA" index -t 1 "$G" "$O/mb"

echo "== map"
for s in $sets; do n=${s%%:*}; r1=$D/${s#*:}_R1.fq; r2=$D/${s#*:}_R2.fq
  $T "$n shim t1" $B/lean-align map "$O/shim.idx" "$r1" "$r2" "$O/$n.shim.sam" 100 1000
  for t in 1 4; do
    WG_MODES=RTX WG_TASKS=$t WG_READS="$n=$r1:$r2:0" $T "$n bench t$t" $B/whole_genome pmap "$O/wg" "$G" | grep -E "^TIME|RESULT"
    $T "$n minibwa t$t" sh -c "'$MINIBWA' map -t $t '$O/mb' '$r1' '$r2' > '$O/$n.mb.sam'"
    $T "$n minibwa-native t$t" sh -c "'$MINIBWA_NATIVE' map -t $t '$O/mb' '$r1' '$r2' > /dev/null"
  done
done
