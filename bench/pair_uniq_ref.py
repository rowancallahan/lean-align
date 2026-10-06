#!/usr/bin/env python3
"""Benchmark only.  Brute pair-level-uniqueness reference (DRAFT spec `pairSpecU`).
From the per-mate hit dump of `PAIR_HITS=<file> PAIR_UNIQ=1 ... pair_bench`
(name, mate, then chr:start:len:pen:strand for every placement of penalty <= 12),
take every proper pair (MapSpec.properPair), keep the one whose summed score
beats every other pair at different placements, else none.  Output in the
pair_bench dump format.
   python3 bench/pair_uniq_ref.py <hits.tsv> [lo=100] [hi=1000] [multi=0] [genome.fa nsample mate1.reads.txt mate2.reads.txt] > ref.tsv
With a one-line FASTA, `nsample` random dumped hits are rescored by an independent
affine DP (scoring 0/-4/-6/-2, read fully aligned to the window): fails loudly on
any difference."""
import random, sys

lo = int(sys.argv[2]) if len(sys.argv) > 2 else 100
hi = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
multi = len(sys.argv) > 4 and sys.argv[4] == "1"

def proper(a, b):
    f, r = (a, b) if a[3] == "+" else (b, a)
    if f[0] != r[0] or f[3] != "+" or r[3] != "-": return False
    end = r[1] + r[2]
    return f[1] <= end and lo <= end - f[1] <= hi

def show(p, k):
    return ("%d\t" % p[0] if multi else "") + "%d\t%d\t%d\t%s" % (p[1], p[2], -k, p[3])

def parse(fields):
    h = {}
    for x in fields:
        c, s, l, k, st = x.split(":")
        p = (int(c), int(s), int(l), st)
        assert h.get(p, int(k)) == int(k), "one placement, two penalties"
        h[p] = int(k)
    return h

rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
assert len(rows) % 2 == 0
hits = []
for i in range(0, len(rows), 2):
    a, b = rows[i], rows[i + 1]
    assert a[0] == b[0] and a[1] == "1" and b[1] == "2"
    hits.append((a[0], parse(a[2:]), parse(b[2:])))
    h1, h2 = hits[-1][1], hits[-1][2]
    best, n = None, 0
    for p, k in h1.items():
        for q, m in h2.items():
            if not proper(p, q): continue
            s = k + m
            if best is None or s < best[0]: best, n = (s, p, k, q, m), 1
            elif s == best[0]: n += 1
    print("%s\t%s\t%s" % (a[0], show(best[1], best[2]), show(best[3], best[4])) if best and n == 1 else a[0] + "\tnone")

if len(sys.argv) > 8:
    seqs = [l.strip() for l in open(sys.argv[5]) if not l.startswith(">")]
    comp = {"A": "T", "C": "G", "G": "C", "T": "A"}
    def rc(s): return "".join(comp.get(c, c) for c in reversed(s))
    def pen(x, y):  # global affine alignment penalty, x fully against y
        INF = 10 ** 9
        n, m = len(x), len(y)
        M = [[INF] * (m + 1) for _ in range(n + 1)]; X = [r[:] for r in M]; Y = [r[:] for r in M]
        M[0][0] = 0
        for j in range(1, m + 1): Y[0][j] = 6 + 2 * j
        for i in range(1, n + 1): X[i][0] = 6 + 2 * i
        for i in range(1, n + 1):
            for j in range(1, m + 1):
                M[i][j] = min(M[i-1][j-1], X[i-1][j-1], Y[i-1][j-1]) + (0 if x[i-1] == y[j-1] else 4)
                X[i][j] = min(M[i-1][j] + 8, X[i-1][j] + 2, Y[i-1][j] + 8)
                Y[i][j] = min(M[i][j-1] + 8, Y[i][j-1] + 2, X[i][j-1] + 8)
        return min(M[n][m], X[n][m], Y[n][m])
    mates = {}
    for m in (1, 2):
        rl = [l.strip() for l in open(sys.argv[7 + m - 1])]
        for j in range(0, len(rl), 2): mates[(rl[j][1:], m)] = rl[j + 1]
    random.seed(1)
    ns = int(sys.argv[6])
    for _ in range(ns):
        nm, h1, h2 = random.choice(hits)
        m, h = random.choice([(1, h1), (2, h2)])
        if not h: continue
        p, k = random.choice(sorted(h.items()))
        r = mates[(nm, m)]
        if p[3] == "-": r = rc(r)
        w = seqs[p[0]][p[1]:p[1] + p[2]]
        assert pen(r, w) == k, (nm, m, p, k, pen(r, w))
    print("rescored %d sampled hits: all equal" % ns, file=sys.stderr)
