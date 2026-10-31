#!/bin/sh
# A/B timing of the word kernels on candidate windows (k250_bench: kerGK / hamA / ker16K per window class),
# runs alternated A B A B ...; every run also asserts word results = byte results.
#   sh scripts/ab_kernel.sh <k250_bench A> <k250_bench B> [runs=5] [dir=out/bench]
# Prints per line label: median ns/window for A and B and B/A.
set -eu
A=$1; B=$2; N=${3:-5}; D=${4:-out/bench}
O=$D/ab_kernel; mkdir -p "$O"; rm -f "$O"/*.log
i=1
while [ $i -le "$N" ]; do
  "$A" "$D/k/chr1.fa" "$D/k/k_1.reads.txt" "$D/k/k.truth.tsv" 1 > "$O/A$i.log"
  "$B" "$D/k/chr1.fa" "$D/k/k_1.reads.txt" "$D/k/k.truth.tsv" 1 > "$O/B$i.log"
  i=$((i + 1))
done
python3 - "$O" "$N" <<'PY'
import re, sys, statistics as st
o, n = sys.argv[1], int(sys.argv[2])
def parse(f):
    sec, out = "", []
    for l in open(f):
        if not l.startswith("  "): sec = l.strip(); continue
        m = re.match(r"\s+(.*?): ([0-9.]+) ns/window", l)
        if m: out.append((f"{sec} | {m.group(1)}", float(m.group(2))))
    return out
runs = {x: [parse(f"{o}/{x}{i}.log") for i in range(1, n + 1)] for x in "AB"}
for k, (lab, _) in enumerate(runs["A"][0]):
    a = st.median(r[k][1] for r in runs["A"]); b = st.median(r[k][1] for r in runs["B"])
    print(f"{a:10.1f} {b:10.1f}  {b / a:5.2f}  {lab}")
PY
