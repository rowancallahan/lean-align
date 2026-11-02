#!/usr/bin/env python3
"""Medians of shim_ab.sh runs: wall and CPU with the index load subtracted (lean-align: the timed empty-FASTQ run
before it; minibwa: its own "index loaded" wall and wall*CPU-ratio), then minibwa / ours multiples.
   python3 -I ab_med.py LOG [OURS_LABEL]"""
import re, sys, statistics
from collections import defaultdict
runs, mbl = {}, {}
for l in open(sys.argv[1]):
    m = re.match(r'TIME (\S+) (\S+) r(\d+)( empty)?: wall ([\d.]+) s, cpu ([\d.]+) s', l)
    if m: runs[(m[1], m[2], m[3], bool(m[4]))] = (float(m[5]), float(m[6]))
    m = re.match(r'TIME (\S+) (\S+) r(\d+): .* load ([\d.]+) s, loadcpu ([\d.]+) s', l)
    if m: mbl[(m[1], m[2], m[3])] = (float(m[4]), float(m[5]))   # load measured in the run (timed_load.py)
    m = re.match(r'MBLOAD (\S+) (\S+) r(\d+) ([\d.]+) ([\d.]+)', l)
    if m: mbl[(m[1], m[2], m[3])] = (float(m[4]), float(m[4]) * float(m[5]))
res = defaultdict(list)
for (s, v, r, e), (w, c) in runs.items():
    if e: continue
    lw, lc = mbl[(s, v, r)] if (s, v, r) in mbl else runs[(s, v, r, True)]
    res[(s, v)].append((w - lw, c - lc, w, c, lw))
med = {}
for (s, v), xs in sorted(res.items()):
    md = lambda i: statistics.median(x[i] for x in xs)
    med[(s, v)] = (md(0), md(1), md(2))
    print(f'{s:8} {v:9} wall-load {md(0):6.1f}  cpu-load {md(1):6.1f}  | wall {md(2):6.1f} cpu {md(3):6.1f} load {md(4):5.1f}  runs: '
          + ' '.join(f'{x[0]:.1f}/{x[1]:.1f}' for x in xs))
ours = sys.argv[2] if len(sys.argv) > 2 else None
for s in sorted({k[0] for k in med}):
    for v in sorted(k[1] for k in med if k[0] == s and not k[1].startswith('mb')):
        if ours and v != ours: continue
        for mb in sorted(k[1] for k in med if k[0] == s and k[1].startswith('mb')):
            a, b = med[(s, mb)], med[(s, v)]
            print(f'{s}: {mb} {a[0]:.1f} s / {v} {b[0]:.1f} s = {a[0] / b[0]:.2f}x (CPU {a[1] / b[1]:.2f}x; end-to-end {a[2]:.1f} / {b[2]:.1f} = {a[2] / b[2]:.2f}x)')
