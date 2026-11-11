#!/bin/bash
# prefetch_bench.sh BASEBIN PFBIN INDEX R1 R2 TAG OUTDIR REPS : interleaved reps (variant order reversed on every second rep), 1 core then 4 cores.
# VARS='name:bin:B:mode ...' overrides the list. Variants: base (BASEBIN), off (PFBIN, LA_PF_B=0), pf2_Bn (prefetch look-ahead n slots), touch1_Bn (volatile read look-ahead n slots).
BASE=$1; PF=$2; IDX=$3; R1=$4; R2=$5; TAG=$6; O=$7; REPS=${8:-3}; H=$(dirname $0); mkdir -p $O
cat $IDX > /dev/null
run() { v=$1; c=$2; b=$3; B=$4; M=$5
  LA_PF_B=$B LA_PF_MODE=$M python3 -I $H/cache_run.py $c "$TAG $v c$c" $O/x.sam $b map $IDX $R1 $R2 $O/x.sam 100 1000; }
VARS=${VARS:-"base:$BASE:0:0 off:$PF:0:0 pf2_B4:$PF:4:2 pf2_B8:$PF:8:2 pf2_B16:$PF:16:2 pf2_B32:$PF:32:2 touch1_B4:$PF:4:1 touch1_B8:$PF:8:1 touch1_B16:$PF:16:1 touch1_B32:$PF:32:1"}
for rep in $(seq $REPS); do for c in 0 0-3; do
  L=$VARS; [ $((rep % 2)) = 0 ] && L=$(echo $VARS | tr ' ' '\n' | tac | tr '\n' ' ')
  for x in $L; do IFS=: read v b B M <<< "$x"; run $v $c $b $B $M; done
done; done
