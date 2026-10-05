#!/usr/bin/env python3
"""Benchmark only.  Would harder quality trimming act as free soft clipping?
For each proper minibwa pair (primary records of the Q20-trimmed reads), re-trim each mate
with the trimmer's rule at a higher neutral quality Q (best-sum window of q - Q, N = -inf),
re-score the kept window with the spec's scoring (parasail sg_dx, as mb_penalty.py) near
minibwa's position, and count pairs whose both mates are >= 100 bp and within the cap.
   python3 bench/trim_sweep.py <genome.1l.fa> <minibwa.sam> Q1 Q2 ..."""
import mmap, re, sys, parasail
from collections import Counter
PAD = 40
M = parasail.matrix_create("ACGTN", 0, -4)
fa, sam, Qs = sys.argv[1], sys.argv[2], [int(q) for q in sys.argv[3:]]
f = open(fa, "rb")
G = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
chrom = {}
i = 0
while i < len(G):
    j = G.find(b"\n", i)
    name = G[i + 1:j].split()[0].decode()
    k = G.find(b"\n", j + 1)
    k = len(G) if k < 0 else k
    chrom[name] = (j + 1, k - j - 1)
    i = k + 1

def window(seq, qual, Q):
    # best-sum window of (q - Q), the trimmer's rule with neutral quality Q
    best, bs, be, cur, cs = None, 0, 0, 0, 0
    for i, (b, c) in enumerate(zip(seq, qual)):
        v = (ord(c) - 33 - Q) if b in "ACGT" else -10**6
        if cur <= 0: cur, cs = v, i
        else: cur += v
        if best is None or cur >= best: best, bs, be = cur, cs, i + 1
    return bs, be

def span(f):
    s, n = chrom[f[2]]
    lead = re.match(r"(\d+)[SH]", f[5])
    p = int(f[3]) - 1 - (int(lead.group(1)) if lead else 0)
    return s + max(0, p - PAD), s + min(n, p + len(f[9]) + PAD)

def pen(read, r): return -parasail.sg_dx_scan_16(read, r, 8, 2, M).score
capRun = lambda n: 16 if n >= 150 else 12
capNew = lambda n: 4 * (n // 25) - 1
cnt = {Q: Counter() for Q in Qs}
recs, pairs = {}, []
for line in open(sam):
    if line[0] == "@": continue
    f = line.split("\t")
    fl = int(f[1])
    if fl & 0x900: continue
    r = recs.setdefault(f[0], [None, None])
    r[0 if fl & 64 else 1] = f
    if not (r[0] and r[1]): continue
    a, b = r
    del recs[f[0]]
    if not (int(a[1]) & 2) or int(a[1]) & 4 or int(b[1]) & 4: continue
    pairs.append((a[9], a[10], span(a), b[9], b[10], span(b)))
# read the reference windows in genome order (sequential IO), then score from memory
W = {sp: None for p in pairs for sp in (p[2], p[5])}
for sp in sorted(W): W[sp] = G[sp[0]:sp[1]].decode().upper()
tot = len(pairs)
for s1, q1, sp1, s2, q2, sp2 in pairs:
    a, b = (None, s1, q1), (None, s2, q2)
    refs = [W[sp1], W[sp2]]
    for Q in Qs:
        ls, ps = [], []
        for m, rf in zip((a, b), refs):
            s, e = window(m[1], m[2], Q)
            ls.append(e - s); ps.append(pen(m[1][s:e], rf) if e - s >= 100 else 999)
        c = cnt[Q]
        if min(ls) < 100: c["short"] += 1; continue
        c["run"] += all(p <= capRun(n) for p, n in zip(ps, ls))
        c["new"] += all(p <= capNew(n) for p, n in zip(ps, ls))
        c["bp"] += sum(ls)
print("pairs", tot)
for Q in Qs:
    c = cnt[Q]
    print(f"Q{Q}: mate<100 {100*c['short']/tot:.1f}%  within run caps {100*c['run']/tot:.1f}%  "
          f"within new proved caps {100*c['new']/tot:.1f}%  mean kept bp/mate {c['bp']/2/max(1,tot-c['short']):.0f}")
