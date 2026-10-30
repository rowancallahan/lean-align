#!/usr/bin/env python3
"""Benchmark only.  Split a read set by a whole_genome dump (line i = pair i):
   python3 Testing/benches/split_by_dump.py tie <tiers_set.tsv> R1.fq R2.fq out_prefix   -> _tie / _rest (RT reason tie1/tie2)
   python3 Testing/benches/split_by_dump.py danger <danger_set.tsv> R1.fq R2.fq out_prefix -> _dng / _safe
     (danger: both mates have a hitting seed and all their hitting seeds are danger seeds)"""
import sys
mode, dump, r1, r2, out = sys.argv[1:6]
assert mode in ("tie", "danger")
cls = {}
for line in open(dump):
    f = line.rstrip("\n").split("\t")
    if mode == "tie": cls[int(f[0][1:])] = f[32].startswith("tie")
    else:
        h1, d1, h2, d2 = map(int, f[1:5]); cls[int(f[0][1:])] = h1 > 0 and h1 == d1 and h2 > 0 and h2 == d2
names = ("tie", "rest") if mode == "tie" else ("dng", "safe")
def recs(p):
    with open(p) as h:
        while True:
            r = [h.readline() for _ in range(4)]
            if not r[0]: return
            assert r[0].startswith("@"), r[0]
            yield "".join(r)
o = {(k, m): open(f"{out}_{k}_R{m}.fq", "w") for k in names for m in (1, 2)}
n = 0
for i, (a, b) in enumerate(zip(recs(r1), recs(r2)), 1):
    k = names[0] if cls[i] else names[1]
    o[(k, 1)].write(a); o[(k, 2)].write(b); n = i
assert n == len(cls), (n, len(cls))
