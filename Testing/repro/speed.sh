#!/bin/bash
# Speed of the map step vs minibwa, by the method of N32_KERNELS §5 / N33_CPU §5: 4 threads, one tool at a time, per tool one warm-up
# empty-FASTQ run, then REPS x (empty-FASTQ run, full run); map time = full - empty right before (index load subtracted, FASTQ read
# + SAM write included); CPU = user + sys. Medians. x = minibwa / ours (> 1: we are faster).
#   bash Testing/repro/speed.sh SET [REPS=6] [THREADS=4]        SET = a prefix in Testing/data/prebuilt (hg38_mason, novaseq_200k ...) or PATH_PREFIX of PATH_R1.fq / PATH_R2.fq
# Needs: lake build lean-align; $MINIBWA = the minibwa c07de5c binary; the bench-release data. Nothing else may run on the box.
set -eu
cd "$(dirname "$0")/../.."
set=$1; reps=${2:-6}; T=${3:-4}
P=Testing/data/prebuilt; MB=${MINIBWA:-minibwa}; lean=.lake/build/bin/lean-align; cpus=0-$((T - 1))
case $set in */*) r=$set ;; *) r=$P/$set ;; esac
d=$(mktemp -d "${TMPDIR:-/tmp}/speed.XXXXXX"); trap 'rm -rf "$d"' EXIT
: > "$d/e_R1.fq"; : > "$d/e_R2.fq"
TIMEFORMAT='%R %U %S'
ours()    { taskset -c $cpus $lean map $P/shim.idx "$1" "$2" "$d/o.sam" 100 1000 2>/dev/null; }
minibwa() { taskset -c $cpus $MB map -t $T $P/mb "$1" "$2" > "$d/o.sam" 2>/dev/null; }
timed()   { { time "$1" "$2" "$3"; } 2>&1; }       # prints "wall user sys"
for tool in ours minibwa; do
  $tool "$d/e_R1.fq" "$d/e_R2.fq"                    # warm-up
  for i in $(seq "$reps"); do
    e=$(timed $tool "$d/e_R1.fq" "$d/e_R2.fq"); f=$(timed $tool "${r}_R1.fq" "${r}_R2.fq")
    echo "$tool $i $e $f" >> "$d/t.txt"
  done
done
python3 -I - "$d/t.txt" "$set" "$T" <<'PY'
import sys, statistics as st
rows = [l.split() for l in open(sys.argv[1])]
res = {}
for t in ('ours', 'minibwa'):
    R = [list(map(float, r[2:])) for r in rows if r[0] == t]     # ew eu es fw fu fs
    wall = [r[3] - r[0] for r in R]; cpu = [(r[4] + r[5]) - (r[1] + r[2]) for r in R]; e2e = [r[3] for r in R]
    res[t] = (st.median(wall), st.median(cpu), st.median(e2e))
    print(f'{sys.argv[2]} {t:8s} map wall {res[t][0]:7.2f} s  CPU {res[t][1]:7.2f} s  end-to-end {res[t][2]:7.2f} s   runs wall {[round(x, 1) for x in wall]}  CPU {[round(x, 1) for x in cpu]}')
o, m = res['ours'], res['minibwa']
print(f'{sys.argv[2]} {sys.argv[3]} threads: minibwa {m[0]:.2f} s / ours {o[0]:.2f} s = {m[0] / o[0]:.2f}x wall; CPU {m[1]:.2f} / {o[1]:.2f} = {m[1] / o[1]:.2f}x; end-to-end {m[2]:.2f} / {o[2]:.2f} = {m[2] / o[2]:.2f}x')
PY
