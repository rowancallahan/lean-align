#!/bin/sh
# Benchmark only: seed schemes in bench/ProtoSketch.lean on chr21, 100k reads.
# Each run's per-read answers are compared with scheme 0:25 (every 25-mer).
#   sh bench/seed_schemes.sh [scheme ...]
set -e
D=${D:-/home/user/data}; B=$(dirname $0)/../.lake/build/bin
export LEAN_ABORT_ON_PANIC=1 PROTO_REPS=${PROTO_REPS:-3}
S=${*:-"0:25 0:21 0:17 1:21:5 1:19:7 1:17:9 1:15:11 1:13:13 2:21:16 2:19:12 2:17:8 2:15:4 3:15:4:5"}
$B/proto_sketch $D/chr21.1l.fa $D/chr21.r100k.reads.txt 0:25 - $D/sk_ref.tsv > /dev/null
for s in $S; do
  echo "== $s"
  $B/proto_sketch $D/chr21.1l.fa $D/chr21.r100k.reads.txt $s - $D/sk_out.tsv | grep -v index_seconds
  case $s in 3:*) ;; *) cmp $D/sk_out.tsv $D/sk_ref.tsv && echo "same answers as 0:25" ;; esac
done
