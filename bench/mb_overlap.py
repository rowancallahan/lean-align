#!/usr/bin/env python3
"""Benchmark only.  Same-place overlap of the proved mapper's pairs with minibwa's.
Denominators (Rowan): minibwa's NON-multimapping proper pairs = primary records, flag 0x2,
both mates mapped, both MAPQ > 0; and the same with both MAPQ >= 20.  A pair of ours is at the same place when, for each mate,
our window (chromosome, strand, [start, start + len)) overlaps minibwa's aligned reference
span.  Pairs of the denominator we do not have at the same place are split into: ours
elsewhere (our penalty vs minibwa's, re-scored), trimmed away, mate < 100 bp after
trimming, beyond the running cap (16 / 12; and whether the proved cap 4·(n/25) − 1 would
reach), within cap (ours none: a tie at the same best penalty, insert size or other).
Penalties are re-scored as in mb_penalty.py (spec scoring sc0, parasail sg_dx, ±PAD
around minibwa's position) for OUR trimmed mate (the trimmer's best-sum window of q − Q,
non-ACGT = −10⁶), not minibwa's clipped read.  Reference windows are read in genome order.
   python3 bench/mb_overlap.py <genome.1l.fa> <minibwa.sam> <cut_R1.fq> <cut_R2.fq> <our_dump.tsv> <chrom names,> [Q]"""
import mmap, re, sys, parasail
from collections import Counter
PAD = 40
M = parasail.matrix_create("ACGTN", 0, -4)
fa, sam, fq1, fq2, dump, cnames = sys.argv[1:7]
Q = int(sys.argv[7]) if len(sys.argv) > 7 else 25
cnames = cnames.split(",")
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

def fq(path):
    out = []
    with open(path) as h:
        while True:
            nm = h.readline()
            if not nm: break
            s = h.readline().strip(); h.readline(); q = h.readline().strip()
            out.append((nm[1:].split()[0], s, q))
    return out
R1, R2 = fq(fq1), fq(fq2)
idx = {r[0]: i for i, r in enumerate(R1)}

def window(seq, qual):
    best, bs, be, cur, cs = None, 0, 0, 0, 0
    for i, (b, c) in enumerate(zip(seq, qual)):
        v = (ord(c) - 33 - Q) if b in "ACGT" else -10**6
        if cur <= 0: cur, cs = v, i
        else: cur += v
        if best is None or cur >= best: best, bs, be = cur, cs, i + 1
    return bs, be
RC = str.maketrans("ACGTN", "TGCAN")
def rc(s): return s.translate(RC)[::-1]
def reflen(cig): return sum(int(n) for n, op in re.findall(r"(\d+)([MDN=X])", cig))

ours = {}
for l in open(dump):
    x = l.rstrip("\n").split("\t")
    i = int(x[0][1:]) - 1
    if x[1] == "none": ours[i] = ("none", x[2] if len(x) > 2 else "")
    else:
        ours[i] = ("hit", [(cnames[int(x[5 * m + 1])], int(x[5 * m + 2]), int(x[5 * m + 3]), -int(x[5 * m + 4]),
                            x[5 * m + 5]) for m in (0, 1)])

recs, mb = {}, {}
for line in open(sam):
    if line[0] == "@": continue
    f = line.split("\t", 11)
    fl = int(f[1])
    if fl & 0x900: continue
    r = recs.setdefault(f[0], [None, None])
    r[0 if fl & 64 else 1] = f
    if r[0] and r[1]:
        del recs[f[0]]
        a, b = r
        fa_, fb = int(a[1]), int(b[1])
        proper = bool(fa_ & 2) and not fa_ & 4 and not fb & 4
        mates = []
        for x in (a, b):
            fl = int(x[1])
            if fl & 4: mates.append(None); continue
            lead = re.match(r"(\d+)[SH]", x[5])
            p0 = int(x[3]) - 1
            mates.append((x[2], p0, p0 + reflen(x[5]), "-" if fl & 16 else "+", int(x[4]),
                          p0 - (int(lead.group(1)) if lead else 0), len(x[9])))
        mb[idx[f[0]]] = (proper, mates)
assert not recs, len(recs)

def same(h, m):
    c, s, n, _, st = h
    return m is not None and c == m[0] and st == m[3] and s < m[2] and m[1] < s + n

THR = (1, 20)   # denominators: both mates MAPQ > 0, and both MAPQ >= 20
cat = {t: Counter() for t in THR}
denom = Counter()
todo = {}       # pair -> "elsewhere" / "none", with the thresholds whose D holds it
N = len(R1)
for i in range(N):
    o = ours.get(i, ("none", "missing"))
    p, ms = mb.get(i, (False, [None, None]))
    for t in THR:
        inD = p and all(m is not None and m[4] >= t for m in ms)
        denom[t] += inD
        c = cat[t]
        if o[0] == "hit":
            c["ours: mapped"] += 1
            if inD and all(same(h, m) for h, m in zip(o[1], ms)): c["D: same place"] += 1; continue
            if not inD:
                c["ours mapped, not in D: " + ("minibwa proper, MAPQ below D's" if p else "minibwa not proper")] += 1
                continue
            todo.setdefault(i, ["elsewhere", []])[1].append(t)
        elif inD:
            if o[1] == "trimmed": c["D: ours none: trimmed away"] += 1
            elif o[1] == "short": c["D: ours none: mate < 100 bp after trimming"] += 1
            else: todo.setdefault(i, ["none", []])[1].append(t)

# re-score our trimmed mates at minibwa's position (windows read in genome order)
def mate(i, k, m):
    nm, s, q = (R1, R2)[k][i]
    a, e = window(s, q)
    t = s[a:e]
    t = rc(t) if m[3] == "-" else t
    cs, cn = chrom[m[0]]
    return t, (cs + max(0, m[5] - PAD), cs + min(cn, m[5] + m[6] + PAD))
jobs = [(i, w, ts_, [mate(i, k, mb[i][1][k]) for k in (0, 1)]) for i, (w, ts_) in todo.items()]
W = {sp: None for _, _, _, ts in jobs for _, sp in ts}
for sp in sorted(W): W[sp] = G[sp[0]:sp[1]].decode().upper()
capRun = lambda n: 16 if n >= 150 else 12
capNew = lambda n: 4 * (n // 25) - 1
for i, w, thr, ts in jobs:
    ps = [-parasail.sg_dx_scan_16(t, W[sp], 8, 2, M).score for t, sp in ts]
    ls = [len(t) for t, _ in ts]
    if w == "elsewhere":
        op = max(h[3] for h in ours[i][1])
        mp = max(ps)
        k = "D: ours elsewhere, worse mate " + ("better than" if op < mp else "equal to" if op == mp
            else "WORSE than") + " minibwa's (re-scored)"
    elif all(p <= capRun(n) for p, n in zip(ps, ls)):
        k = "D: ours none: within cap (tie / insert / other)"
    elif all(p <= capNew(n) for p, n in zip(ps, ls)):
        k = "D: ours none: beyond cap 16/12, within proved cap 4(n/25)-1"
    else:
        k = "D: ours none: beyond proved cap"
    for t in thr: cat[t][k] += 1
print(f"pairs {N}; Q{Q}")
for t in THR:
    d = denom[t]
    print(f"== D = minibwa proper, primary, both mapped, both MAPQ >= {t}: {d}")
    for k in sorted(cat[t]):
        print(f"{k}: {cat[t][k]} ({100 * cat[t][k] / d:.2f}% of D)")
