#!/bin/bash
cd /home/user/S
declare -A C=( [base]="JOB_PAIRS=16000" [jp8k]="JOB_PAIRS=8000" [jp4k]="JOB_PAIRS=4000" [jp2k]="JOB_PAIRS=2000" [d4]="DEPTH=4" [jp4k_d4]="JOB_PAIRS=4000 DEPTH=4" [w5]="WORKERS=5" )
for rep in 1 2 3; do
 for s in h1m n1m; do
  for c in base jp8k jp4k jp2k d4 jp4k_d4 w5; do
   L=${c}_${s}_$rep; ./run.sh $L $s ${C[$c]}
   python3 an.py $L > res/$L.an 2>&1
   echo "$L $(cat res/$L.md5 | cut -c1-8)" >> res/summary.txt
  done
 done
done
echo ALLDONE >> res/summary.txt
