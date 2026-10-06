#!/usr/bin/env python3
"""Benchmark only.  Mode RTX tier 2 pairs: why they are T2, and which ones `tierUp` (codecs/TierOpt.lean)
promotes: `t2Opt` (T2b, a best proper pair from what the router already reports) and the exact pair search
`pairGXE` (T1u unique best / T1um tie, WG_XEBUD).

Input: WG_TIEROUT=1 dumps (tiers_<set>.tsv: name, tag, 15 columns per mate as MateX.show, then RT's
reason ("gated" = skipped by the budget gate), g0, pf).

  python3 bench/t2_opt.py cause tiers_*.tsv        T2 cause breakdown and certified share per cause
  python3 bench/t2_opt.py lines tiers.tsv [TAGS]   the certified T2 lines, or the lines tagged TAGS (e.g. T1u,T2b),
                                                   for bench/tier_vs_mb.py join
  python3 bench/t2_opt.py tags base.tsv new.tsv     per set: % of pairs and % of base T2 per new tag
  python3 bench/t2_opt.py mb join_*.tsv            certified pairs vs minibwa's re-scored pair penalty
Proper pair = properPairU with usl 0, lo 100, hi 1000 (the bench defaults WG_USL, WG_MIN, WG_MAX).
"""
import sys, csv, collections

LO, HI, USL = 100, 1000, 0


def proper(a, b):
    """properPairU on (chr, start, len, strand) placements."""
    if a[0] != b[0] or a[3] == b[3]:
        return False
    f, r = (a, b) if a[3] == "+" else (b, a)
    fr = r[1] + r[2] - f[1]
    return f[1] <= r[1] + r[2] and LO <= fr <= HI and f[1] <= r[1] + USL and f[1] + f[2] <= r[1] + r[2] + USL


def mpl(m):
    return None if m[4] == "-" else (m[4], int(m[5]), int(m[6]), m[7])


def pf_floor(g):
    return 4 if g < 4 else (8 if g < 8 else g + 1)


def certified(a):
    """`t2Opt`: T2, both ceiling placements, proper, pH1 + pH2 <= pairFloor."""
    if a[1] != "T2":
        return False
    m1, m2, pf = a[2:17], a[17:32], a[34]
    x, y = mpl(m1), mpl(m2)
    fl = max(int(m1[2]) + int(m2[2]), 0 if pf == "-" else pf_floor(int(pf)))
    return x is not None and y is not None and proper(x, y) and int(m1[11]) + int(m2[11]) <= fl


def cause(a):
    w = a[32]
    return "tie" if w.startswith("tie") else w.rstrip("12")


def main():
    cmd, files = sys.argv[1], sys.argv[2:]
    if cmd == "lines":
        tags = set(files[1].split(",")) if len(files) > 1 else None
        for L in open(files[0]):
            a = L.rstrip("\n").split("\t")
            if (a[1] in tags) if tags else certified(a):
                sys.stdout.write(L)
    elif cmd == "tags":
        base, new = files
        n = sum(1 for _ in open(new))
        t2 = sum(1 for L in open(base) if L.split("\t")[1] in ("T2", "T2b"))
        C = collections.Counter(L.split("\t")[1] for L in open(new))
        print(f"{new}: pairs {n}, base T2 {t2} ({100 * t2 / n:.1f}%)")
        for k in ["T1u", "T1um", "T2b", "T2"]:
            print(f"  {k:5s} {C[k]:6d} {100 * C[k] / n:6.2f}% of pairs {100 * C[k] / t2:6.1f}% of T2")
        p = C["T1u"] + C["T1um"] + C["T2b"]
        print(f"  promoted {p:6d} {100 * p / n:6.2f}% of pairs {100 * p / t2:6.1f}% of T2")
    elif cmd == "cause":
        for f in files:
            n, t2, C, K, S = 0, 0, collections.Counter(), collections.Counter(), collections.Counter()
            for L in open(f):
                a = L.rstrip("\n").split("\t")
                n += 1
                if a[1] != "T2":
                    continue
                t2 += 1
                k = cause(a)
                C[k] += 1
                K[k] += certified(a)
                S[k] += int(a[2 + 11]) + int(a[17 + 11]) <= 16
            print(f"{f}: pairs {n}, T2 {t2} ({100 * t2 / n:.1f}%), certified {sum(K.values())} "
                  f"({100 * sum(K.values()) / t2:.1f}% of T2, {100 * sum(K.values()) / n:.2f}% of pairs)")
            print("  cause       T2   %T2  pH1+pH2<=16  certified")
            for k, v in C.most_common():
                print(f"  {k:10s} {v:5d} {100 * v / t2:5.1f} {S[k]:12d} {K[k]:10d}")
    elif cmd == "mb":
        for f in files:
            C = collections.Counter()
            for r in csv.DictReader(open(f), delimiter="\t"):
                C["pairs"] += 1
                if r["mbmap1"] != "1" or r["mbmap2"] != "1":
                    continue
                o = int(r["ours1"]) + int(r["ours2"])
                m = int(r["mbpen1"]) + int(r["mbpen2"])
                pl = lambda s: (lambda c, a, b, d: (c, int(a), int(b), d))(*s.split(":"))
                pr = proper(pl(r["mbpl1"]), pl(r["mbpl2"]))
                C["mb maps both"] += 1
                C["mb proper"] += pr
                C["mb better, proper (violation)"] += m < o and pr
                C["mb better, not proper"] += m < o and not pr
                C["mb equal"] += m == o
                C["mb equal elsewhere"] += m == o and (r["pl1"], r["pl2"]) != (r["mbpl1"], r["mbpl2"])
                C["mb worse"] += m > o
            print(f, dict(C))


if __name__ == "__main__":
    main()
