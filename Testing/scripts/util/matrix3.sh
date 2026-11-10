#!/bin/bash
cd /home/user/S; R=res/summary3.txt
for rep in 1 2 3; do
 for c in m64e m64w d4 d8 sc15 ; do
  sink=fifo; [ $rep = 3 ] && sink=fifomd5
  L=f_${c}_h1m_$rep
  python3 gzrun.py $L bin/$c gz/h1m_R1.fq.gz gz/h1m_R2.fq.gz new $sink >> $R 2>&1
  python3 gzan.py $L > res/$L.gz.an 2>&1
 done
done
for c in m64e m64w d4 d8; do
  L=f_${c}_h3m_1; python3 gzrun.py $L bin/$c gz2/h3m_R1.fq.gz gz2/h3m_R2.fq.gz new fifo >> $R 2>&1; python3 gzan.py $L > res/$L.gz.an 2>&1
done
echo ALLDONE >> $R
