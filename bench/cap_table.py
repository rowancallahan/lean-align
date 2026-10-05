#!/usr/bin/env python3
"""Benchmark only.  Which cap would keep which share of minibwa's unique proper pairs?
Re-trims each mate of minibwa's proper pairs at quality Q (the trimmer's rule), re-scores the
kept window with the spec's scoring near minibwa's position (as trim_sweep.py), and prints,
for MAPQ > 0 and MAPQ >= 20 (both mates), the share of pairs whose both mates are within
cap X (optionally also within the proved cap 4*(n//25)-1), for mates >= 100 bp or >= 50 bp.
   python3 bench/cap_table.py <genome.1l.fa> <minibwa.sam> Q > table.txt"""
import sys
sys.argv, (fa, sam, Q) = sys.argv[:1], sys.argv[1:4]
Q = int(Q)
import mmap, re, parasail
PAD = 40
M = parasail.matrix_create("ACGTN", 0, -4)
FH = open(fa, "rb")
G = mmap.mmap(FH.fileno(), 0, access=mmap.ACCESS_READ)
chrom, i = {}, 0
while i < len(G):
    j = G.find(b"\n", i); name = G[i + 1:j].split()[0].decode()
    k = G.find(b"\n", j + 1); k = len(G) if k < 0 else k
    chrom[name] = (j + 1, k - j - 1); i = k + 1

def window(seq, qual):
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

recs, pairs = {}, []
for line in open(sam):
    if line[0] == "@": continue
    f = line.split("\t"); fl = int(f[1])
    if fl & 0x900: continue
    r = recs.setdefault(f[0], [None, None]); r[0 if fl & 64 else 1] = f
    if not (r[0] and r[1]): continue
    a, b = r; del recs[f[0]]
    if not (int(a[1]) & 2) or int(a[1]) & 4 or int(b[1]) & 4: continue
    mq = min(int(a[4]), int(b[4]))
    if mq == 0: continue
    pairs.append((mq, [(m[9], m[10], span(m)) for m in (a, b)]))
W = {m[2]: None for _, ms in pairs for m in ms}
for sp in sorted(W): W[sp] = G[sp[0]:sp[1]].decode().upper()
rows = []  # (mapq, [(len, pen)] per mate)
for mq, ms in pairs:
    ls = []
    for seq, qual, sp in ms:
        s, e = window(seq, qual)
        ls.append((e - s, -parasail.sg_dx_scan_16(seq[s:e], W[sp], 8, 2, M).score if e - s >= 30 else 999))
    rows.append((mq, ls))
prov = lambda n: 4 * (n // 25) - 1
caps = [12, 16, 20, 24, 25, 28, 30, 32, 35, 39, 45, 50, 60, 80, 999]
for mqmin in (1, 20):
    sel = [ls for mq, ls in rows if mq >= mqmin]
    N = len(sel)
    print(f"\nQ{Q}  minibwa proper, both MAPQ >= {mqmin}: {N} pairs")
    print("cap  | >=100bp, cap only | >=100bp, min(cap, proved) | >=50bp, cap only | >=50bp, min(cap, proved)")
    for X in caps:
        out = []
        for lmin in (100, 50):
            a = sum(all(n >= lmin and p <= X for n, p in ls) for ls in sel)
            b = sum(all(n >= lmin and p <= min(X, prov(n)) for n, p in ls) for ls in sel)
            out += [f"{100*a/N:5.1f}%", f"{100*b/N:5.1f}%"]
        print(f"{X:>4} | " + " | ".join(out))
    short = sum(any(n < 50 for n, _ in ls) for ls in sel)
    print(f"pairs with a mate < 50 bp after trimming: {100*short/N:.1f}%")
