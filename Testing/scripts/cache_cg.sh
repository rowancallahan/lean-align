#!/bin/bash
# cache_cg.sh MODE BIN INDEX R1 R2 TAG OUTDIR : cache simulation of one mapping run on 1 core.
# MODE=callgrind : callgrind --cache-sim=yes with the host's geometry (callgrind ignores --D1/--LL when the CPU reports an L3), collecting only inside Spec.MapFast.job
# MODE=cg-laptop : cachegrind I1 32K/8, D1 32K/8, LL 8M/16        (whole run; subtract a 500-pair run to get the job's share)
# MODE=cg-server : cachegrind I1 32K/8, D1 48K/12, LL 32M/16      (same)
MODE=$1; BIN=$2; IDX=$3; R1=$4; R2=$5; TAG=$6; O=$7; mkdir -p $O
case $MODE in
  callgrind) T="--tool=callgrind --cache-sim=yes --toggle-collect=lp_lean__align_Spec_MapFast_job --callgrind-out-file=$O/$TAG.$MODE.out";;
  cg-laptop) T="--tool=cachegrind --I1=32768,8,64 --D1=32768,8,64 --LL=8388608,16,64 --cachegrind-out-file=$O/$TAG.$MODE.out";;
  cg-server) T="--tool=cachegrind --I1=32768,8,64 --D1=49152,12,64 --LL=33554432,16,64 --cachegrind-out-file=$O/$TAG.$MODE.out";;
esac
taskset -c 0 valgrind $T $BIN map $IDX $R1 $R2 $O/x.$TAG.$MODE.sam 100 1000 > $O/$TAG.$MODE.log 2>&1
rm -f $O/x.$TAG.$MODE.sam
