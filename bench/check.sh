#!/bin/sh
# Benchmark only: run `proto` on the three test sets in $D and compare its
# per-read answers with reference dumps ($D/ref_*.tsv, made by an earlier
# prototype; on 100 kb also the proved mapper's $D/spec*.tsv prefixes).
#   sh bench/check.sh [l0=25]
set -e
D=${D:-/home/user/data}; B=$(dirname $0)/../.lake/build/bin; L=${1:-25}
export LEAN_ABORT_ON_PANIC=1
for t in 100k:c21_100k.fa:c21_100k.r10k 1m:c21_1m.fa:c21_1m.r10k chr21:chr21.1l.fa:chr21.r100k; do
  n=${t%%:*}; r=${t##*:}; g=${t#*:}; g=${g%%:*}
  echo "== $n"; $B/proto $D/$g $D/$r.reads.txt $L $D/$r.truth.tsv $D/out_$n.tsv
  cmp $D/out_$n.tsv $D/ref_$n.tsv && echo "same as ref_$n"
done
for r in hard_1m:c21_1m hard_chr21:chr21.1l rep:rep; do
  $B/proto $D/${r#*:}.fa $D/${r%:*}.reads.txt $L - $D/out_${r%:*}.tsv | grep reads/s
  cmp $D/out_${r%:*}.tsv $D/ref_${r%:*}.tsv && echo "same as ref_${r%:*}"
done
for s in $D/spec*.tsv; do
  case $s in *hard2*) R=hard2_100k G=c21_100k ;; *hard*) R=hard_100k G=c21_100k ;; *rep2*) R=rep2 G=rep2 ;; *rep*) R=rep G=rep ;; *) R=c21_100k.r10k G=c21_100k ;; esac
  $B/proto $D/$G.fa $D/$R.reads.txt $L - $D/out_spec.tsv > /dev/null
  k=$(wc -l < $s); head -n $k $D/out_spec.tsv | cmp - $s && echo "same as $(basename $s) ($k reads)"
done
