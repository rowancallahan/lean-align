#!/bin/bash
# prefetch_bench.sh BASEBIN PFBIN INDEX R1 R2 TAG OUTDIR REPS : interleaved reps, 1 core then 4 cores, variants of the look-ahead (env LA_PF_B / LA_PF_MODE).
BASE=$1; PF=$2; IDX=$3; R1=$4; R2=$5; TAG=$6; O=$7; REPS=${8:-3}; H=$(dirname $0); mkdir -p $O
cat $IDX > /dev/null
run() { v=$1; c=$2; b=$3; B=$4; M=$5
  LA_PF_B=$B LA_PF_MODE=$M python3 -I $H/cache_run.py $c "$TAG $v c$c" $O/x.sam $b map $IDX $R1 $R2 $O/x.sam 100 1000; }
for rep in $(seq $REPS); do for c in 0 0-3; do
  run base $c $BASE 0 0
  run pf_off $c $PF 0 0
  run pf2_B4 $c $PF 4 2
  run pf2_B8 $c $PF 8 2
  run pf2_B16 $c $PF 16 2
  run pf2_B32 $c $PF 32 2
  run touch1_B8 $c $PF 8 1
  run touch1_B16 $c $PF 16 1
done; done
