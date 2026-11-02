#!/usr/bin/env python3
"""Counts for a lean-align SAM (pairs: both mates mapped, real vs degenerate last-resort pairs, XU:Z:unique, and for
mason/low names both mates within 20 of the true start on the true chromosome and strand).
   python3 -I sam_stats.py OURS.sam [BASE.sam]   (BASE: also count pairs whose placement or XU differs)"""
import re, sys
def pairs(path):
    cur = []
    for l in open(path):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        cur.append((r[0], f, r[2], int(r[3]), r[5], [t for t in r[11:] if t.startswith('XU:') or t.startswith('XB:')]))
        if len(cur) == 2:
            yield cur if cur[0][1] & 64 else cur[::-1]; cur = []
    assert not cur
def truth(qn):
    m = re.match(r's\d+:([^:]+):(\d+)-\d+([+-]):(\d+)-\d+([+-])', qn)
    return None if not m else [(m[1], int(m[2]) + 1, m[3] == '-'), (m[1], int(m[4]) + 1, m[5] == '-')]
def stats(path):
    n = mapped = degen = uniq = at = 0
    for p in pairs(path):
        n += 1
        if all(not a[1] & 4 for a in p):
            if all(re.fullmatch(r'\d+I', a[4]) for a in p): degen += 1
            else: mapped += 1
        if 'XU:Z:unique' in p[0][5]: uniq += 1
        t = truth(p[0][0])
        if t and all(not a[1] & 4 and a[2] == t[i][0] and abs(a[3] - t[i][1]) <= 20 and bool(a[1] & 16) == t[i][2]
                     for i, a in enumerate(p)): at += 1
    return n, mapped, degen, uniq, at
n, m, d, u, a = stats(sys.argv[1])
pc = lambda x: f'{x} ({100 * x / n:.2f}%)'
print(f'pairs {n}  mapped {pc(m)}  degenerate {pc(d)}  unique {pc(u)}  at truth {pc(a)}')
if len(sys.argv) > 2:
    diff = sum(1 for x, y in zip(pairs(sys.argv[1]), pairs(sys.argv[2])) if [(a[1], a[2], a[3], a[4], a[5]) for a in x] != [(a[1], a[2], a[3], a[4], a[5]) for a in y])
    print(f'pairs differing from {sys.argv[2]}: {diff}')
