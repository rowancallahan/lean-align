#!/bin/bash
# FIFO-sink reruns: fsk=festive, mfk=mapfiles 64ae73f; 1M all T; then 5M T4 (fsk, mfk, mb->/dev/null)
R=/home/user/lean-align; I=/root/idx/ic.idx; MBI=$R/Testing/data/prebuilt/mb; B=/root/bench
for s in n1m h1m; do r1=/root/p1m/${s}_R1.fq; r2=/root/p1m/${s}_R2.fq
 for T in 1 2 4; do for k in 1 2 3; do
  list="fsk:/root/bin/festive mfk:/root/bin/mapfiles_64ae73f"; [ $k = 2 ] && list="mfk:/root/bin/mapfiles_64ae73f fsk:/root/bin/festive"
  for b in $list; do python3 $B/drop.py $MBI.mbw $MBI.l2b; cat $r1 $r2 $I > /dev/null
   bash $B/sinkrun.sh "$s T$T ${b%%:*} r$k" $T ${b#*:} $r1 $r2; done; done; done; done > $B/log_sink1m.txt
F=/root/fifo; mkdir -p $F
for s in nova5m hiseq5m; do for k in 1 2 3; do
  list="fsk mfk mb"; [ $k = 2 ] && list="mb mfk fsk"
  for l in $list; do rm -f $F/a $F/b; mkfifo $F/a $F/b
   if [ $l = mb ]; then python3 $B/drop.py $I; cat $MBI.mbw $MBI.l2b > /dev/null; else python3 $B/drop.py $MBI.mbw $MBI.l2b; cat $I > /dev/null; fi
   zcat /root/big/${s}_R1.fq.gz > $F/a & zcat /root/big/${s}_R2.fq.gz > $F/b &
   case $l in mb) python3 $B/mbrun.py "$s T4 mb r$k" 4 /root/minibwa/minibwa $MBI $F/a $F/b;;
    fsk) bash $B/sinkrun.sh "$s T4 fsk r$k" 4 /root/bin/festive $F/a $F/b;;
    mfk) bash $B/sinkrun.sh "$s T4 mfk r$k" 4 /root/bin/mapfiles_64ae73f $F/a $F/b;; esac
   wait; done; done; done > $B/log_sink5m.txt
echo FINISHED > $B/run3.done
