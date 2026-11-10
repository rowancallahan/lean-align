#!/bin/sh
# Headline: ours (byte_pipeline B, PIPE_B=1) vs minibwa, 4 cores, SAM to /dev/null, index load separate, 3 reps.
# Sets: n1m/h1m plain files; nova5m/hiseq5m via zcat FIFO. Then md5 runs (untimed) of B and plain festive on the 1M sets.
S=${S:?set S to a scratch dir}; REPO=${REPO:?set REPO to the festive checkout}
D=${REPO:?set REPO}/Testing/data/prebuilt
I=$S/idx/ic.idx; M=$D/mb; F=$S/fifo; mkdir -p $F
C="taskset -c 0-3"; B=${OURS:-$S/bin/bpB}
drop() { python3 -c "import os,sys
for f in sys.argv[1:]:
    fd = os.open(f, os.O_RDONLY); os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED); os.close(fd)" "$@"; }
feed() { case $1 in
  *.gz) rm -f $F/a $F/b; mkfifo $F/a $F/b; zcat $1 > $F/a & zcat $2 > $F/b & in1=$F/a; in2=$F/b;;
  *) cat $1 $2 > /dev/null; in1=$1; in2=$2;; esac; }
for s in n1m:$S/p1m/n1m_R1.fq:$S/p1m/n1m_R2.fq h1m:$S/p1m/h1m_R1.fq:$S/p1m/h1m_R2.fq \
         nova5m:$S/big/nova5m_R1.fq.gz:$S/big/nova5m_R2.fq.gz hiseq5m:$S/big/hiseq5m_R1.fq.gz:$S/big/hiseq5m_R2.fq.gz; do
  n=${s%%:*}; r=${s#*:}; r1=${r%%:*}; r2=${r#*:}
  drop $M.*
  for k in 1 2 3; do cat $I > /dev/null; feed $r1 $r2
    PIPE_B=1 $C python3 ${REPO:?set REPO}/Testing/scripts/timed_load.py "$n oursB r$k" $B map $I $in1 $in2 /dev/null 100 1000; wait; done
  drop $I
  for k in 1 2 3; do cat $M.* > /dev/null; feed $r1 $r2
    $C python3 $REPO/Testing/notes/bench/phases.py "$n minibwa r$k" 99999999999 /dev/null 0 -- sh -c "$S/bin/minibwa map -t 4 $M $in1 $in2 > /dev/null 2> $S/mb.err"; wait
    echo "MBLOAD $n minibwa r$k $(grep 'index loaded' $S/mb.err | sed 's/.*::\([0-9.]*\)\*\([0-9.]*\)\].*/\1 \2/')"; done
done
for n in n1m h1m; do for b in oursB:$B plain:$S/bin/pl0; do l=${b%%:*}; x=${b#*:}
  rm -f $F/o; mkfifo $F/o; md5sum < $F/o > $S/md5.$n.$l &
  PIPE_B=1 $C $x map $I $S/p1m/${n}_R1.fq $S/p1m/${n}_R2.fq $F/o 100 1000; wait; echo "MD5 $n $l $(cat $S/md5.$n.$l)"; done; done
for n in nova5m hiseq5m; do
  rm -f $F/o $F/a $F/b; mkfifo $F/o $F/a $F/b; md5sum < $F/o > $S/md5.$n.oursB & zcat $S/big/${n}_R1.fq.gz > $F/a & zcat $S/big/${n}_R2.fq.gz > $F/b &
  PIPE_B=1 $C $B map $I $F/a $F/b $F/o 100 1000; wait; echo "MD5 $n oursB $(cat $S/md5.$n.oursB)"; done
