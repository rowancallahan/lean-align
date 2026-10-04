#!/usr/bin/env python3
"""Benchmark only.  Brute proper-pair reference: per-mate dumps of
`PROTO_BOTH=1 proto` (name, start, len, score, strand | none) -> pair dump in
the format of `PROTO_PAIR=... proto`.
   python3 bench/pair_ref.py <mate1.tsv> <mate2.tsv> [lo=100] [hi=1000] > ref.tsv"""
import sys
lo = int(sys.argv[3]) if len(sys.argv) > 3 else 100
hi = int(sys.argv[4]) if len(sys.argv) > 4 else 1000
m1 = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
m2 = [l.rstrip("\n").split("\t") for l in open(sys.argv[2])]
assert len(m1) == len(m2) and all(a[0] == b[0] for a, b in zip(m1, m2))
for a, b in zip(m1, m2):
    ok = len(a) == 5 and len(b) == 5 and a[4] != b[4]
    if ok:
        f, r = (a, b) if a[4] == "+" else (b, a)
        frag = int(r[1]) + int(r[2]) - int(f[1])
        ok = lo <= frag <= hi
    print("\t".join([a[0]] + a[1:] + b[1:]) if ok else a[0] + "\tnone")
