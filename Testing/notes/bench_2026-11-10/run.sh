#!/bin/bash
# usage: run.sh LOG "label:bin ..." ; minibwa included as label mb. env: THREADS="1 2 4" SETS="n1m h1m" REPS=3
set -eu
LOG=$1; BINS=$2; THREADS=${THREADS:-"1 2 4"}; SETS=${SETS:-"n1m h1m"}; REPS=${REPS:-3}
R=/home/user/lean-align; I=/root/idx/ic.idx; MBI=$R/Testing/data/prebuilt/mb; MB=/root/minibwa/minibwa; P=/root/p1m; B=/root/bench
for s in $SETS; do r1=$P/${s}_R1.fq; r2=$P/${s}_R2.fq
 for T in $THREADS; do
  for b in $BINS; do l=${b%%:*}; x=${b#*:}
   if [ $l = mb ]; then python3 $B/drop.py $I; else python3 $B/drop.py $MBI.mbw $MBI.l2b; fi
   for k in $(seq $REPS); do
    cat $r1 $r2 > /dev/null
    if [ $l = mb ]; then cat $MBI.mbw $MBI.l2b > /dev/null; python3 $B/mbrun.py "$s T$T $l r$k" $T $x $MBI $r1 $r2
    else cat $I > /dev/null; taskset -c 0-$((T-1)) python3 $R/Testing/scripts/timed_load.py "$s T$T $l r$k" $x map $I $r1 $r2 /dev/null 100 1000; fi
   done; done; done; done | tee -a $LOG
