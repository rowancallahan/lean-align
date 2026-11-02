#!/usr/bin/env python3
"""Benchmark only (n31 repeat hint). Seed-count flag vs RT ties, from whole_genome dumps made with
WG_SEEDCNT=1 WG_TIEROUT=1 (seedcnt_<set>.tsv, tiers_<set>.tsv in DIR).
   python3 repeat_hint.py DIR set [R1.fq R2.fq outprefix N stat]   (last 4: write the flagged pairs as _flag / _rest FASTQ)
A mate's statistic = best strand of (min | median) bucket size over its seeds; a pair is flagged when both mates >= N."""
import sys
d, s = sys.argv[1:3]
rows = []
for a, b in zip(open(f"{d}/tiers_{s}.tsv"), open(f"{d}/seedcnt_{s}.tsv")):
    t = a.rstrip("\n").split("\t"); c = b.rstrip("\n").split("\t"); assert t[0] == c[0]
    v = list(map(int, c[1:]))   # mate1: min_f med_f min_r med_r, mate2 the same
    st = {"min": [max(v[0], v[2]), max(v[4], v[6])], "med": [max(v[1], v[3]), max(v[5], v[7])]}
    rows.append((t[1], t[32].startswith("tie"), st))
def flag(r, N, stat): return min(r[2][stat]) >= N
if len(sys.argv) > 4:
    r1, r2, out, N, stat = sys.argv[3:8]; N = int(N)
    o = {(k, m): open(f"{out}_{k}_R{m}.fq", "w") for k in ("flag", "rest") for m in (1, 2)}
    def recs(p):
        with open(p) as h:
            while True:
                r = [h.readline() for _ in range(4)]
                if not r[0]: return
                yield "".join(r)
    for r, a, b in zip(rows, recs(r1), recs(r2)):
        k = "flag" if flag(r, N, stat) else "rest"; o[(k, 1)].write(a); o[(k, 2)].write(b)
    sys.exit()
n = len(rows); ties = sum(r[1] for r in rows)
print(f"== {s}: {n} pairs, {ties} RT ties ({100*ties/n:.1f}%)")
print("stat    N   flagged  ties_flagged  catch%  prec%  nonTie_flagged  of_which_T1(unique)")
for stat in ("min", "med"):
    for N in (20, 50, 100, 200, 500, 1000):
        f = [r for r in rows if flag(r, N, stat)]; ft = sum(r[1] for r in f); fu = sum(1 for r in f if not r[1] and r[0] == "T1")
        print(f"{stat}  {N:5d}  {len(f):7d}  {ft:7d}  {100*ft/ties:6.1f}  {100*ft/max(1,len(f)):6.1f}  {len(f)-ft:7d}  {fu:7d}")
