#!/bin/sh
# Speed comparison on one genome and the read sets in Testing/data/downloads, at THREADS cores (default "2 4"):
#   shim     .lake/build/bin/lean-align (Main.lean: build, then map), pinned to N cores with taskset
#   bench    .lake/build/bin/whole_genome, mode RTX (the same proved tierPair, mapping time only), N tasks
#   minibwa  default build and -march=native build, -t N, pinned to N cores
# Runs one after another, nothing else on the box.   sh Testing/scripts/compare.sh [genome.fa]
# Last step: the shim on a tiny genome = its FASTQ/SAM I/O cost alone.
# SETS="hiseq250:hg002_200k" limits the read sets (name:file prefix in Testing/data/downloads).
# Needs: lake build whole_genome; MINIBWA (default build) and MINIBWA_NATIVE set to the two binaries.
# MB_INDEX_FLAGS="-l" builds minibwa's index in its low-memory mode.
set -u   # no -e: a tool that fails (e.g. out of memory) is recorded and the rest still run
cd "$(dirname "$0")/../.."
root=$PWD; D=$root/Testing/data/downloads; B=$root/.lake/build/bin
T="python3 $root/Testing/scripts/timed.py"
# map timings repeat REPEAT times (default 3); report the median (this box varies ~30% run to run)
R=${REPEAT:-3}
TR() { label=$1; shift; i=0; while [ $i -lt $R ]; do $T "$label run$((i+1))" "$@"; i=$((i+1)); done; }
G=${1:-$D/chr21.fa}; O=${OUT:-${TMPDIR:-/tmp}/lean_align_compare}; mkdir -p "$O"
sets=${SETS:-"hiseq250:hg002_200k novaseq151:novaseq_200k mason:sim_mason low:sim_low"}
threads=${THREADS:-"2 4"}
cores() { echo "0-$(($1 - 1))"; }

echo "== index"
$T "shim build" $B/lean-align build "$G" "$O/shim.idx"
[ "${BENCH:-1}" = 1 ] && $T "bench build" $B/whole_genome build "$O/wg" "$G"
[ "${BENCH:-1}" = 1 ] && WG_CHECK=1 WG_MODES=RTX WG_READS="" $T "bench check index (once)" $B/whole_genome pmap "$O/wg" "$G" >/dev/null
$T "minibwa index" "$MINIBWA" index ${MB_INDEX_FLAGS:-} -t 1 "$G" "$O/mb"

echo "== map"
for s in $sets; do n=${s%%:*}; r1=$D/${s#*:}_R1.fq; r2=$D/${s#*:}_R2.fq
  for t in $threads; do
    TR "$n shim t$t" taskset -c $(cores $t) $B/lean-align map "$O/shim.idx" "$r1" "$r2" "$O/$n.shim.sam" 100 1000
    [ "${BENCH:-1}" = 1 ] && WG_MODES=RTX WG_TASKS=$t WG_READS="$n=$r1:$r2:0" $T "$n bench t$t" taskset -c $(cores $t) $B/whole_genome pmap "$O/wg" "$G" | grep -E "^TIME|RESULT"
    TR "$n minibwa t$t" taskset -c $(cores $t) sh -c "'$MINIBWA' map -t $t '$O/mb' '$r1' '$r2' > '$O/$n.mb.sam'"
    TR "$n minibwa-native t$t" taskset -c $(cores $t) sh -c "'$MINIBWA_NATIVE' map -t $t '$O/mb' '$r1' '$r2' > /dev/null"
  done
done

echo "== shim I/O only (FASTQ in, SAM out; a 20 kb random genome, so mapping costs ~nothing)"
python3 -c "import random; random.seed(1); print('>tiny'); print(''.join(random.choice('ACGT') for _ in range(20000)))" > "$O/tiny.fa"
$B/lean-align build "$O/tiny.fa" "$O/tiny.idx"
for s in $sets; do n=${s%%:*}; r1=$D/${s#*:}_R1.fq; r2=$D/${s#*:}_R2.fq
  for t in $threads; do
    TR "$n shim I/O only t$t" taskset -c $(cores $t) $B/lean-align map "$O/tiny.idx" "$r1" "$r2" "$O/$n.tiny.sam" 100 1000
  done
done
