#!/bin/sh
# A/B timing of the whole pair path (whole_genome pmap, mode RTX = the proved tierPair), runs alternated A B A B ...
#   sh scripts/ab_pair.sh <whole_genome A> <whole_genome B> [runs=5] [dir=out/bench] [pairs=20000]
# env: AB_TASKS (1), and any WG_* knob (passed through, e.g. WG_PG=4 WG_XBUD=5000).
# Checks that A and B write byte-identical RTX and tier dumps; prints wall / CPU medians and B/A.
set -eu
A=$1; B=$2; N=${3:-5}; D=${4:-out/bench}; P=${5:-20000}
T=${AB_TASKS:-1}
O=$D/ab_pair; mkdir -p "$O/A" "$O/B"
L=$((2 * P))
head -n $L "$D/g/p150_1.reads.txt" > "$O/r1.txt"; head -n $L "$D/g/p150_2.reads.txt" > "$O/r2.txt"
: > "$O/times.tsv"
i=1
while [ $i -le "$N" ]; do
  for x in A B; do
    if [ $x = A ]; then bin=$A; else bin=$B; fi
    line=$(WG_READS="p=$O/r1.txt:$O/r2.txt:0" WG_MODES=RTX WG_TASKS=$T WG_OUT="$O/$x" WG_TIEROUT=1 \
      "$bin" pmap "$D/g/ix" "$D/g/chr1.fa" "$D/g/chr2.fa" | grep "^RESULT")
    wall=$(echo "$line" | sed -E 's/.*kept [0-9]+, ([0-9.]+) s,.*/\1/')
    cpu=$(echo "$line" | sed -E 's/.*cpu ([0-9.]+) s.*/\1/')
    printf '%s\t%s\t%s\n' $x "$wall" "$cpu" >> "$O/times.tsv"
    echo "run $i $x: wall $wall s, cpu $cpu s"
  done
  i=$((i + 1))
done
cmp "$O/A/RTX_p.tsv" "$O/B/RTX_p.tsv" && cmp "$O/A/tiers_p.tsv" "$O/B/tiers_p.tsv" && echo "dumps identical (RTX, tiers)"
python3 - "$O/times.tsv" <<'PY'
import sys, statistics as st
r = [l.split("\t") for l in open(sys.argv[1]) if l.strip()]
m = {x: (st.median(float(a[1]) for a in r if a[0] == x), st.median(float(a[2]) for a in r if a[0] == x)) for x in "AB"}
print(f"median wall A {m['A'][0]:.3f} s  B {m['B'][0]:.3f} s  B/A {m['B'][0] / m['A'][0]:.3f}")
print(f"median cpu  A {m['A'][1]:.3f} s  B {m['B'][1]:.3f} s  B/A {m['B'][1] / m['A'][1]:.3f}")
PY
