#!/bin/sh
# Benchmark only: seed schemes in bench/ProtoSketch.lean on chr21, 100k reads.
# Entries are CTX,PICK,scheme (scheme 0:k every k-mer, 1:k:w minimizers,
# 2:k:s closed syncmers, 3:k:s:t open syncmers — counting only, 4:k:w:thr
# weighted minimizers: k-mers of buckets with > thr genome k-mers ordered last).  Each run's
# per-read answers are compared with scheme 0:25 (every 25-mer).
#   sh bench/seed_schemes.sh [entry ...]
set -e
D=${D:-/home/user/data}; B=$(dirname $0)/../.lake/build/bin
export LEAN_ABORT_ON_PANIC=1 PROTO_REPS=${PROTO_REPS:-3}
S=${*:-"0,0,0:25 0,0,0:21 0,0,1:21:5 1,0,1:21:5 0,0,1:19:7 1,0,1:19:7 0,0,1:17:9 1,0,1:17:9 0,0,1:15:11 1,0,1:15:11 1,0,1:13:13 1,0,4:19:7:8 1,0,4:17:9:8 1,0,4:15:11:8 1,0,4:15:11:24 0,0,2:21:16 1,1,2:21:16 0,0,2:19:12 1,1,2:19:12 1,0,2:17:8 1,0,2:15:4 1,1,2:15:4 0,0,3:15:4:5"}
$B/proto_sketch $D/chr21.1l.fa $D/chr21.r100k.reads.txt 0:25 - $D/sk_ref.tsv > /dev/null
for e in $S; do
  c=${e%%,*}; r=${e#*,}; p=${r%%,*}; s=${r#*,}
  echo "== CTX=$c PICK=$p $s"
  CTX=$c PICK=$p $B/proto_sketch $D/chr21.1l.fa $D/chr21.r100k.reads.txt $s - $D/sk_out.tsv | grep -v index_seconds
  case $s in 3:*) ;; *) cmp $D/sk_out.tsv $D/sk_ref.tsv && echo "same answers as 0:25" ;; esac
done
