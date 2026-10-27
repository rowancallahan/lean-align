#!/usr/bin/env python3
"""Summarise bench/seed_stats.py output files (analysis only).

    python3 bench/seed_report.py <files...>

Per mate (both strands) and scheme m (m seeds of L = n // m letters, 25-letter seeds when
m = n // 25): candidate diagonals (distinct strand+diagonal) that a cap-exact search must score
when it looks up the s+1 seeds with the smallest bucket per strand (`bucket`), the s+1 with the
fewest hits (`oracle`), or all seeds (`all`); `gen` = key-matched entries (genome reads) of the
bucket-chosen seeds.
"""
import sys, ast, numpy as np
from collections import defaultdict

data = defaultdict(list)
for f in sys.argv[1:]:
    for line in open(f):
        i, mate, M, n, s, L, rec = ast.literal_eval(line)
        def cands(pick):
            ds = set()
            g = 0
            for st, seeds in enumerate(rec):
                for (h, sz, km, dg) in pick(seeds):
                    ds.update((st, d) for d in dg)
                    g += km
            return len(ds), g
        b, gb = cands(lambda ss: sorted(ss, key=lambda r: r[1])[: s + 1])
        o, _ = cands(lambda ss: sorted(ss, key=lambda r: r[0])[: s + 1])
        a, ga = cands(lambda ss: ss)
        data[M].append((b, o, a, gb, ga))

def pct(a, qs=(50, 90, 99, 99.9)):
    a = np.asarray(a)
    return " ".join(f"p{q}={np.percentile(a, q):.0f}" for q in qs) + f" mean={a.mean():.1f} sum={a.sum()}"

for M in sorted(data, reverse=True):
    d = np.array(data[M])
    print(f"m={M} mates={len(d)}")
    for j, name in enumerate(["cand bucket", "cand oracle", "cand all", "gen reads bucket", "gen reads all"]):
        print(f"   {name:18s} {pct(d[:, j])}")
    for thr in (64, 256, 1024):
        print(f"   mates with > {thr} candidates (bucket): {(d[:, 0] > thr).mean() * 100:.2f}%, their share of candidates {d[d[:, 0] > thr, 0].sum() / max(1, d[:, 0].sum()) * 100:.1f}%")
