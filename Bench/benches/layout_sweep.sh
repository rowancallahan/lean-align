#!/bin/sh
# Index layout sweep (bench/Layout.lean), answers compared with a Proto dump.
#   G=chr21 REF=ref.dump SORT=both sh bench/layout_sweep.sh boxed n,24 z,22,24
# Data dir: $DATA (default /home/user/data) holding $G.1l.fa and $G.r100k.reads.txt.
# Specs: boxed | w,s,B,kb | n,B | m,k,B | mn,k,B | z,k,B (proved MzIndex; CHECK=1 runs its checker).
set -u
cd "${DATA:-/home/user/data}" || exit 1
L="$(dirname "$0")/../.lake/build/bin/layout"
[ -x "$L" ] || L=/home/user/lean-align/.lake/build/bin/layout
G=${G:-chr21}; R=${R:-$G.r100k.reads.txt}; REF=${REF:-ref.dump}
for sp in "$@"; do
  out=$("$L" "$G.1l.fa" "$R" "$sp" /tmp/layout_dump.tsv) || { echo "== $G $sp FAILED"; continue; }
  same=$(cmp -s /tmp/layout_dump.tsv "$REF" && echo SAME || echo DIFF)
  echo "== $G $sp $same"; echo "$out" | grep -v "^genome\|mem end"
done
