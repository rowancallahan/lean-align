#!/bin/bash
cd /home/user/S; R=res/summary2.txt
declare -A C=( [base]="" [jp2k]="JOB_PAIRS=2000" [jp4k]="JOB_PAIRS=4000" [jp8k]="JOB_PAIRS=8000" [if16]="IN_FLIGHT=16" [if32]="IN_FLIGHT=32" [if16jp4k]="IN_FLIGHT=16 JOB_PAIRS=4000" [file]="" )
for rep in 1 2 3; do
 for c in base jp2k jp4k jp8k if16 if32 if16jp4k file; do
  sink=fifo; [ $c = file ] && sink=file; [ $rep = 3 ] && sink=fifomd5; [ $c = file ] && [ $rep = 3 ] && sink=file
  L=e_${c}_h1m_$rep
  env ${C[$c]} python3 gzrun.py $L bin/m64e gz/h1m_R1.fq.gz gz/h1m_R2.fq.gz new $sink >> $R 2>&1
  python3 gzan.py $L > res/$L.gz.an 2>&1
 done
done
echo ALLDONE >> $R
