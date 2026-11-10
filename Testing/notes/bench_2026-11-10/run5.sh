#!/bin/bash
# 5M via zcat FIFOs, 4 threads, 3 reps rotated. bins: fst mf mb
R=/home/user/lean-align; I=/root/idx/ic.idx; MBI=$R/Testing/data/prebuilt/mb; MB=/root/minibwa/minibwa; B=/root/bench; F=/root/fifo; mkdir -p $F
declare -A BIN=([fst]=/root/bin/festive [mf]=/root/bin/mapfiles_64ae73f [mb]=$MB)
for s in nova5m hiseq5m; do
 for k in 1 2 3; do
  list="fst mf mb"; [ $k = 2 ] && list="mb mf fst"
  for l in $list; do
   rm -f $F/a $F/b; mkfifo $F/a $F/b
   if [ $l = mb ]; then python3 $B/drop.py $I; cat $MBI.mbw $MBI.l2b > /dev/null; else python3 $B/drop.py $MBI.mbw $MBI.l2b; cat $I > /dev/null; fi
   zcat /root/big/${s}_R1.fq.gz > $F/a & zcat /root/big/${s}_R2.fq.gz > $F/b &
   if [ $l = mb ]; then python3 $B/mbrun.py "$s T4 $l r$k" 4 $MB $MBI $F/a $F/b
   else taskset -c 0-3 python3 $R/Testing/scripts/timed_load.py "$s T4 $l r$k" ${BIN[$l]} map $I $F/a $F/b /dev/null 100 1000; fi
   wait
  done; done; done
echo FINISHED
