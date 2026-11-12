#!/usr/bin/env python3
"""Deep caps (bench only): truth penalties of sim pairs vs RTX dumps.
  analyze.py <genome.fa> <sim_R1.fq> <truth_R1.tsv> <truth_R2.tsv> <RTX_base.tsv> [<RTX_variant.tsv> ...]
truth_*.tsv: `dc truth` output (index, len, pen, nmis, ngapev, coords).  RTX dumps: whole_genome WG_OUT.
Prints: max-mate truth penalty bins for all pairs and for pairs the base leaves unmapped; kept / at truth per dump;
clean disjoint seed (any seed length L) for the base's unmapped mates.  Asserts on anything unexpected."""
import sys, collections
G, FQ, T1, T2, BASE, *VAR = sys.argv[1:]
# the bench reads the multi-record FASTA as ONE sequence: later header lines stay in it as letters
chroms, offs, pos = [], [], 0
for l in open(G):
    l = l.rstrip("\n")
    if l.startswith(">"):
        if chroms: pos += len(l)
        chroms.append(l[1:].split()[0]); offs.append(pos)
    else: pos += len(l)
import bisect
truth = []
with open(FQ) as h:
    for k, l in enumerate(h):
        if k % 4 == 0:
            n = l[1:].split()[0]; _, c, a, b = n.split(":")
            iv = lambda s: (int(s[:-1].split("-")[0]), int(s[:-1].split("-")[1]), s[-1])
            truth.append((c, iv(a), iv(b)))
def tr(p):
    out = []
    for l in open(p):
        f = l.rstrip("\n").split("\t")
        if f[1] == "-": out.append(None); continue
        out.append((int(f[1]), int(f[2]), [int(x) for x in f[5].split(",")] if len(f) > 5 and f[5] else []))
    return out
t1, t2 = tr(T1), tr(T2)
assert len(t1) == len(t2) == len(truth), (len(t1), len(t2), len(truth))
def dump(p):
    d = []
    for l in open(p):
        f = l.rstrip("\n").split("\t")
        d.append(None if f[1] == "none" else ((int(f[1]), int(f[2]), int(f[3]), int(f[4]), f[5]), (int(f[6]), int(f[7]), int(f[8]), int(f[9]), f[10])))
    assert len(d) == len(truth), (p, len(d))
    return d
def at(h, c, iv):  # same chromosome and strand, overlapping the true interval
    assert h[0] == 0
    r = bisect.bisect_right(offs, h[1]) - 1; x = h[1] - offs[r]
    return chroms[r] == c and h[4] == iv[2] and x < iv[1] and iv[0] < x + h[2]
def ok(x, i):
    c, a, b = truth[i]
    return x is not None and at(x[0], c, a) and at(x[1], c, b)
def pen(i):
    if t1[i] is None or t2[i] is None: return None
    return max(t1[i][1], t2[i][1])
BINS = [(0, 16), (17, 20), (21, 23), (24, 24), (25, 28), (29, 32), (33, 40), (41, 10**9)]
def binof(p):
    if p is None: return "trimmed"
    for a, b in BINS:
        if a <= p <= b: return f"{a}-{b}" if b < 10**9 else f">{a - 1}"
base = dump(BASE)
n = len(truth)
print(f"pairs {n}")
for lab, sel in (("all", range(n)), ("base unmapped", [i for i in range(n) if base[i] is None]),
                 ("base not at truth", [i for i in range(n) if not ok(base[i], i)])):
    c = collections.Counter(binof(pen(i)) for i in sel)
    print(f"max mate truth penalty, {lab} ({len(sel)}): " + ", ".join(f"{k} {c[k]}" for k in sorted(c, key=lambda k: (k[0] == '>' or k == 'trimmed', int(k.split('-')[0].lstrip('>')) if k != 'trimmed' else 0))))
for p in [BASE] + VAR:
    d = dump(p)
    kept = sum(x is not None for x in d); good = sum(ok(d[i], i) for i in range(n))
    gain = sum(ok(d[i], i) and not ok(base[i], i) for i in range(n)); lost = sum(ok(base[i], i) and not ok(d[i], i) for i in range(n))
    wrong = sum(d[i] is not None and not ok(d[i], i) for i in range(n))
    print(f"{p}: kept {kept}, at truth {good} ({100 * good / n:.2f}%), kept not at truth {wrong}, gained vs base {gain}, lost {lost}")
# clean disjoint seed of each mate the base leaves unmapped, by seed length (m = len // L seeds, seed j at j*(len // m))
def clean(t, L):
    ln, _, cs = t; m = ln // L
    if m == 0: return False
    l = ln // m
    return any(not any(2 * j * l < x < 2 * (j * l + l) for x in cs) for j in range(m))
un = [i for i in range(n) if base[i] is None and pen(i) is not None]
for L in (25, 21, 18, 16, 14):
    c = collections.Counter()
    for i in un:
        b = binof(pen(i)); c[b, "n"] += 1; c[b, "ok"] += clean(t1[i], L) and clean(t2[i], L)
    print(f"L={L}: base-unmapped pairs with a clean seed in both mates, by max truth penalty: " +
          ", ".join(f"{a}-{b if b < 10**9 else 'inf'} {c[binof(a), 'ok']}/{c[binof(a), 'n']}" for a, b in BINS))
