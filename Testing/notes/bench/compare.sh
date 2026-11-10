#!/bin/sh
# spec/fastq-bytes (sfb) vs festive dd2f3cb (fst) vs byte_pipeline B (bpB, PIPE_B=1). 4 cores, SAM to /dev/null, 3 reps
# rotated, index warmed before each run. Sets: n1m/h1m plain, nova5m/hiseq5m zcat FIFO. Then an md5 run per binary per set.
S=${S:?set S to a scratch dir}; REPO=${REPO:?set REPO to the festive checkout}
I=$S/idx/ic.idx; F=$S/fifo; mkdir -p $F; C="taskset -c 0-3"
BINS=${BINS:-"sfb:$S/bin/sfb fst:$S/bin/fst bpB:$S/bin/bpB"}   # label:binary ...; label bpB runs with PIPE_B=1
feed() { case $1 in
  *.gz) rm -f $F/a $F/b; mkfifo $F/a $F/b; zcat $1 > $F/a & zcat $2 > $F/b & in1=$F/a; in2=$F/b;;
  *) cat $1 $2 > /dev/null; in1=$1; in2=$2;; esac; }
env_of() { [ $1 = bpB ] && echo PIPE_B=1 || echo PIPE_B=0; }
SETS="n1m:$S/p1m/n1m_R1.fq:$S/p1m/n1m_R2.fq h1m:$S/p1m/h1m_R1.fq:$S/p1m/h1m_R2.fq"
for s in $SETS; do n=${s%%:*}; r=${s#*:}; r1=${r%%:*}; r2=${r#*:}
  for k in 1 2 3; do
    list=$BINS; [ $k = 2 ] && list=$(echo $BINS | tr ' ' '\n' | tac | tr '\n' ' ')
    for b in $list; do l=${b%%:*}; x=${b#*:}
      cat $I > /dev/null; feed $r1 $r2
      env $(env_of $l) $C python3 ${REPO:?set REPO}/Testing/scripts/timed_load.py "$n $l r$k" $x map $I $in1 $in2 /dev/null 100 1000; wait
    done; done
done
for s in $SETS; do n=${s%%:*}; r=${s#*:}; r1=${r%%:*}; r2=${r#*:}
  for b in $BINS; do l=${b%%:*}; x=${b#*:}
    feed $r1 $r2; rm -f $F/o; mkfifo $F/o; md5sum < $F/o > $S/md5.$n.$l &
    env $(env_of $l) $C $x map $I $in1 $in2 $F/o 100 1000; wait; echo "MD5 $n $l $(cat $S/md5.$n.$l)"
  done; done
