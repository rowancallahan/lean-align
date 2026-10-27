#!/bin/bash
# Proved fast mapper over minimizer indexes: sweep (k, B, c), compare answers with a dump.
#   G=chr21 TASKS="1 4" bash bench/mz_sweep.sh 0,0 21,22,3 17,22,4      (k=0: hashed 25-mer index)
# Needs $DATA/$G.1l.fa, $DATA/$G.r100k.reads.txt and the reference dump $REF.
set -u
BIN=${BIN:-$(cd "$(dirname "$0")/.." && pwd)/.lake/build/bin/fast_bench}
cd "${DATA:-/home/user/data}" || exit 1
G=${G:-chr21}; REF=${REF:-ref.dump}; [ "$G" = chr1 ] && REF=${REF1:-ref1.dump}
for kb in "$@"; do
  IFS=, read -r k B C <<< "$kb"; C=${C:-$((25 - k))}
  for t in ${TASKS:-1}; do
    out=$(FAST_TASKS=$t FAST_REPS=3 FAST_MZ=$k FAST_MZ_B=$B FAST_MZ_C=$C "$BIN" "$G.1l.fa" "$G.r100k.reads.txt" /tmp/mz_sweep.tsv 2>&1)
    same=$(cmp -s /tmp/mz_sweep.tsv "$REF" && echo SAME || echo DIFF)
    best=$(echo "$out" | grep "^rep " | awk '{print $3}' | sort -g | head -1)
    bytes=$(echo "$out" | grep -o "index_bytes: [0-9]*" | awk '{print $2}')
    ix=$(echo "$out" | grep "^index_s" | awk '{print $2}'); ck=$(echo "$out" | grep "^check_s" | awk '{print $2}')
    echo "$G k=$k B=$B c=$C tasks=$t $same bytes=$bytes build_s=$ix check_s=$ck best_rep_s=$best reads/s=$(echo "100000/${best:-0}" | bc)"
  done
done
