#!/bin/sh
# Scaling curve: chromosomes -> pairs/s, RSS, index bytes for the interleaved (pairFastI, mode I)
# and scheduled (pairFastS, modes S1/S2) proved pair mappers on one index; dumps compared with cmp.
# usage: sh bench/sched_scale.sh <dir with g<n>.fa, g<n>.pe_1/_2.reads.txt> "1 2 3 4"
set -e
D=$1; B=$(dirname $0)/../.lake/build/bin/pair_bench
for n in $2; do
  echo "== g$n"
  PAIR_MODES=${MODES:-I,S1,S2} PAIR_STATS=1 PAIR_MZ=22 $B $D/g$n.fa $D/g$n.pe_1.reads.txt $D/g$n.pe_2.reads.txt $D/g$n.out
  for m in $(echo ${MODES:-I,S1,S2} | tr , ' '); do cmp $D/g$n.out.I $D/g$n.out.$m; done
  echo "g$n identical"
done
