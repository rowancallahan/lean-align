#!/bin/bash
# pmp.sh N OUT CMD... : run CMD, take a gdb stack sample of every thread every 0.5 s (up to N samples), then print
# the most common Lean frames of busy threads
N=$1; OUT=$2; shift 2
"$@" & pid=$!
: > $OUT
for i in $(seq $N); do
  sleep 0.5; kill -0 $pid 2>/dev/null || break
  gdb -p $pid -batch -ex "thread apply all bt 40" 2>/dev/null | grep -E "^#|^Thread" >> $OUT
done
wait $pid
python3 - "$OUT" <<'PY'
import sys, re, collections
c = collections.Counter(); top = collections.Counter(); cur = []
def flush():
    fr = [re.search(r' in (\S+)', l).group(1) for l in cur if ' in ' in l]
    fr = [f for f in fr if 'lp_lean__align' in f or f.startswith('l_')]
    if fr and not any(w in ' '.join(fr) for w in ('Task_get', 'task_get')):
        top[fr[0]] += 1
        for f in set(fr): c[f] += 1
for l in open(sys.argv[1]):
    if l.startswith('Thread'): flush(); cur = []
    else: cur.append(l)
flush()
print("innermost:", *[f"{n} {f}" for f, n in top.most_common(8)], sep="\n  ")
print("inclusive:", *[f"{n} {f}" for f, n in c.most_common(25)], sep="\n  ")
PY
