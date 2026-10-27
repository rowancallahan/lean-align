#!/bin/sh
# Deterministic A/B: callgrind instruction counts of the whole pair path (whole_genome pmap, mode RTX) on the
# first <pairs> pairs (default 2000), counted inside tierPair only (index load / hashing / IO excluded).
#   sh scripts/ab_ir.sh <whole_genome A> <whole_genome B> [dir=out/bench] [pairs=2000] [top=25]
# Prints total Ir for A and B, B/A, and the top functions of each by self Ir.
set -eu
A=$1; B=$2; D=${3:-out/bench}; P=${4:-2000}; TOP=${5:-25}
O=$D/ab_ir; mkdir -p "$O"
L=$((2 * P))
head -n $L "$D/g/p150_1.reads.txt" > "$O/r1.txt"; head -n $L "$D/g/p150_2.reads.txt" > "$O/r2.txt"
for x in A B; do
  if [ $x = A ]; then bin=$A; else bin=$B; fi
  WG_READS="p=$O/r1.txt:$O/r2.txt:0" WG_MODES=RTX WG_TASKS=1 WG_OUT="$O/$x" WG_TIEROUT=1 \
    valgrind --tool=callgrind --toggle-collect='lp_lean__align_MapSpec_Fast_tierPair' --callgrind-out-file="$O/$x.cg" "$bin" pmap "$D/g/ix" "$D/g/chr1.fa" "$D/g/chr2.fa" \
    > "$O/$x.log" 2>&1
  callgrind_annotate --threshold=100 "$O/$x.cg" 2>/dev/null | head -n $((TOP + 25)) > "$O/$x.top.txt"
done
cmp "$O/A/RTX_p.tsv" "$O/B/RTX_p.tsv" && echo "dumps identical"
for x in A B; do echo "== $x"; grep -E "PROGRAM TOTALS|Ir +file:function" -A $TOP "$O/$x.top.txt" | cut -c1-160; done
python3 - "$O/A.top.txt" "$O/B.top.txt" <<'PY'
import re, sys
t = [int(re.search(r"([\d,]+) \(100.0%\)\s+PROGRAM TOTALS", open(f).read()).group(1).replace(",", "")) for f in sys.argv[1:]]
print(f"total Ir A {t[0]:,}  B {t[1]:,}  B/A {t[1] / t[0]:.4f}")
PY
