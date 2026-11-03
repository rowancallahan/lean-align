#!/bin/bash
# One headline timing row, one tool at a time (method of N32_KERNELS.md section 4): per tool one warm-up empty-FASTQ run, then
# 3 x (empty-FASTQ run, full run); CPU of the map part = (user+sys)(full) - (user+sys)(empty right before); 4 cores.
#   bash time_row.sh SET_R1.fq SET_R2.fq SHIM_IDX MB_PREFIX LEAN_ALIGN MINIBWA > timing.txt
set -u
r1=$1; r2=$2; idx=$3; mb=$4; la=$5; mbbin=$6; here=$(dirname "$0")/..; T="python3 -I $here/scripts/timed.py"
e=$(mktemp -d); : > $e/e1.fq; : > $e/e2.fq
ours() { taskset -c 0-3 $T "$1" bash -c "$la map $idx $2 $3 $e/out.sam 100 1000 > /dev/null"; }
theirs() { taskset -c 0-3 $T "$1" bash -c "$mbbin map -t 4 $mb $2 $3 > $e/mb.sam 2>/dev/null"; }
for tool in ${TOOLS:-ours theirs}; do
  $tool warm-$tool $e/e1.fq $e/e2.fq
  for i in 1 2 3; do $tool empty-$tool $e/e1.fq $e/e2.fq; $tool full-$tool $r1 $r2; done
done 2>&1 | grep '^TIME'
rm -rf $e
