#!/usr/bin/env python3
"""Benchmark only.  minibwa paired SAM vs the proved mapper's pair dump (= pairSpec
answer, T = -12, proper pair [100, 1000]) vs simulation truth.
   python3 bench/mb_compare.py <minibwa.sam> <pair_dump.tsv> <truth.tsv> [chrom names in dump order...]
A minibwa pair "reports" when both primary records are mapped with the proper-pair flag;
MAPQ = min of the two.  Positions are compared after removing a leading soft clip, within
TOL bp.  minibwa's own alignment penalty (sc0: mismatch 4, gap 6 + 2L) is computed from
CIGAR + NM; soft-clipped alignments count as beyond the cap (the spec is global)."""
import re, sys
TOL = 5
sam, dump, truth = sys.argv[1:4]
names = sys.argv[4:] or None

def pen(cigar, nm):
    ops = re.findall(r"(\d+)([MIDSH])", cigar)
    if any(o in "SH" for _, o in ops): return 99
    gaps = [int(l) for l, o in ops if o in "ID"]
    return 4 * (nm - sum(gaps)) + sum(6 + 2 * l for l in gaps)

mb = {}
for line in open(sam):
    if line[0] == "@": continue
    f = line.split("\t")
    flag = int(f[1])
    if flag & 0x900: continue
    lead = re.match(r"(\d+)S", f[5])
    nm = int(next(t[5:] for t in f[11:] if t.startswith("NM:i:"))) if not flag & 4 else 0
    rec = (flag, f[2], int(f[3]) - 1 - (int(lead.group(1)) if lead else 0), "-" if flag & 16 else "+",
           int(f[4]), pen(f[5], nm) if not flag & 4 else 99)
    mb.setdefault(f[0], [None, None])[0 if flag & 64 else 1] = rec

tr = {}
for line in list(open(truth))[1:]:
    p, c, a, sa, b, sb = line.split()
    tr[p] = (c, (int(a) - 1, sa), (int(b) - 1, sb))

sp = {}
for line in open(dump):
    f = line.split()
    if f[1] == "none": continue
    if names:  # chrom index before each hit
        sp[f[0]] = (names[int(f[1])], (int(f[2]), f[5]), (int(f[7]), f[10]), -int(f[4]), -int(f[9]))
    else:
        c = tr[f[0]][0]
        sp[f[0]] = (c, (int(f[1]), f[4]), (int(f[5]), f[8]), -int(f[3]), -int(f[7]))

def near(x, y): return x[1] == y[1] and abs(x[0] - y[0]) <= TOL
def same(c1, h1, h2, c2, k1, k2): return c1 == c2 and near(h1, k1) and near(h2, k2)

N = len(tr)
rows = {}
def bump(k): rows[k] = rows.get(k, 0) + 1
for p, (tc, t1, t2) in tr.items():
    m = mb.get(p)
    mrep = m and m[0] and m[1] and not (m[0][0] & 4) and not (m[1][0] & 4) and m[0][0] & 2
    mq = min(m[0][4], m[1][4]) if mrep else -1
    if mrep: mc, mh1, mh2 = m[0][1], (m[0][2], m[0][3]), (m[1][2], m[1][3])
    s = sp.get(p)
    if s: bump("spec maps"); bump("spec at truth") if same(s[0], s[1], s[2], tc, t1, t2) else None
    for q in (0, 1, 20, 60):
        if mrep and mq >= q:
            bump(f"mb q>={q} reports")
            if same(mc, mh1, mh2, tc, t1, t2): bump(f"mb q>={q} at truth")
            at = " [at truth]" if same(mc, mh1, mh2, tc, t1, t2) else " [NOT at truth]"
            if s:
                bump((f"mb q>={q} on spec-mapped: same as spec" if same(mc, mh1, mh2, s[0], s[1], s[2])
                      else f"mb q>={q} on spec-mapped: DIFFERENT from spec") + at)
            else:
                ok = m[0][5] <= 12 and m[1][5] <= 12
                bump((f"mb q>={q} on spec-unmapped: both mates within cap (spec tie/ambiguous)" if ok
                      else f"mb q>={q} on spec-unmapped: beyond cap (extra sensitivity)") + at)
        elif s: bump(f"mb q>={q} misses spec-mapped")
print(f"pairs: {N}")
for k in sorted(rows): print(f"{k}: {rows[k]}")
