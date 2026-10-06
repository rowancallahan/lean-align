#!/usr/bin/env python3
"""Benchmark only.  Mapping accuracy on simulated pairs (bench/sim_pairs.py), minibwa paper Fig 2a style.
   python3 bench/sim_eval.py <genome.1l.fa> <set_R1.fq> <set_R2.fq> <minibwa.sam|-> <out.json> [label=dump.tsv ...]
A mate is correct if |Gs ∩ Ga| / |Gs ∪ Ga| >= 10% (Gs = simulated reference interval, Ga = aligned
interval: minibwa POS + CIGAR reference length; ours the reported window) and same chromosome.
minibwa: primary records; one point per MAPQ threshold (cumulative from the top).  Ours: one point per
dump (no MAPQ).  Per read: % aligned of all simulated reads; per pair: both mates aligned (pair MAPQ =
min of mates), wrong if either mate is wrong.  For our wrong mates the trimmed mate is re-scored with
the spec scoring (parasail sg_dx, 0/-4, gap 6+2k) at its true interval: truth worse than ours means
the spec optimum is not the true locus (expected; the mapper returns the spec optimum).
SIM_TRUTH: truth file instead of names (see below).  SIM_Q: trimmer neutral quality (25), as WG_TRIMQ.  SIM_UNM=A,...: dumps run at config A's caps
(16 from 150 bp, 12 from 100, 11 from 75) whose unmapped pairs are split by the true locus's penalty.  The SAM may be cut to its first 6 columns."""
import json, mmap, os, re, sys
import parasail
fa, fq1, fq2, sam, out = sys.argv[1:6]
dumps = [a.split("=", 1) for a in sys.argv[6:]]
Q = int(os.environ.get("SIM_Q", "25"))
CH = ["chr%s" % c for c in list(range(1, 23)) + ["X", "Y"]]   # chromosome order of the index (wk/chroms.txt)
UNM = os.environ.get("SIM_UNM", "A").split(",")   # dumps whose unmapped pairs are classified (A's caps)
THR = [60, 50, 40, 30, 20, 15, 10, 5, 3, 1, 0]

def fq(path):
    L = open(path).read().split("\n")
    return [(L[i][1:].split()[0].rsplit("/", 1)[0] if L[i].split()[0][-2:] in ("/1", "/2") else L[i][1:].split()[0], L[i + 1], L[i + 3])
            for i in range(0, len(L) - 3, 4)]
R = [fq(fq1), fq(fq2)]
N = len(R[0])
truth = []   # per pair: chrom, [(b, e, strand)] x 2
# SIM_TRUTH=<tsv>: name <tab> chrom:b-e±:b-e± per pair in FASTQ order (e.g. from mason's --out-alignment)
TN = [l.split("\t")[1].strip() for l in open(os.environ["SIM_TRUTH"])] if "SIM_TRUTH" in os.environ else None
for j, (nm, _, _) in enumerate(R[0]):
    x = ("_:" + TN[j] if TN else nm).split(":")
    truth.append((x[1], [(int(m[1]), int(m[2]), m[3]) for m in (re.match(r"(\d+)-(\d+)([+-])", y) for y in x[2:4])]))
idx = {nm: i for i, (nm, _, _) in enumerate(R[0])}

def ok(i, k, c, b, e):
    tc, ts = truth[i][0], truth[i][1][k]
    inter = min(e, ts[1]) - max(b, ts[0])
    return c == tc and inter > 0 and inter / (max(e, ts[1]) - min(b, ts[0])) >= 0.1

res = {}
def curve(name, mates):
    """mates: pair index -> [(conf, correct) or None] x 2; returns points per threshold."""
    pts = []
    for t in (THR if name == "minibwa" else [None]):
        ra = rw = pa = pw = 0
        for ms in mates.values():
            got = [m for m in ms if m is not None and (t is None or m[0] >= t)]
            ra += len(got); rw += sum(not m[1] for m in got)
            if all(m is not None for m in ms) and (t is None or min(m[0] for m in ms) >= t):
                pa += 1; pw += any(not m[1] for m in ms)
        pts.append(dict(thr=t, reads=ra, reads_wrong=rw, pct_reads=100 * ra / (2 * N), err_reads=rw / max(ra, 1),
                        pairs=pa, pairs_wrong=pw, pct_pairs=100 * pa / N, err_pairs=pw / max(pa, 1)))
    return pts

if sam != "-":
    mb = {}
    for line in open(sam):
        if line[0] == "@": continue
        f = line.split("\t", 6); fl = int(f[1])
        if fl & 0x904: continue
        rl = sum(int(n) for n, op in re.findall(r"(\d+)([MDN=X])", f[5]))
        i, k = idx[f[0]], 0 if fl & 64 else 1
        b = int(f[3]) - 1
        mb.setdefault(i, [None, None])[k] = (int(f[4]), ok(i, k, f[2], b, b + rl))
    res["minibwa"] = curve("minibwa", mb)

FH = open(fa, "rb")
G = mmap.mmap(FH.fileno(), 0, access=mmap.ACCESS_READ)
off, i = {}, 0
while i < len(G):
    j = G.find(b"\n", i); k = G.find(b"\n", j + 1); k = len(G) if k < 0 else k
    off[G[i + 1:j].split()[0].decode()] = j + 1; i = k + 1
M = parasail.matrix_create("ACGTN", 0, -4)
RC = str.maketrans("ACGTN", "TGCAN")
def truthPen(i, k):
    """Spec penalty of our trimmed mate k of pair i at its true interval (None: trimmed away)."""
    _, s, q = R[k][i]
    a, e = window(s, q)
    if e <= a: return None, 0
    t = s[a:e] if truth[i][1][k][2] == "+" else s[a:e].translate(RC)[::-1]
    o, (b, en, _) = off[truth[i][0]], truth[i][1][k]
    return -parasail.sg_dx_scan_16(t, G[o + max(0, b - 40):o + en + 40].decode().upper(), 8, 2, M).score, e - a
CAPA = lambda n: 16 if n >= 150 else 12 if n >= 100 else 11 if n >= 75 else None   # config A's pass-1 caps

def window(seq, qual):
    best, bs, be, cur, cs = None, 0, 0, 0, 0
    for i, (b, c) in enumerate(zip(seq, qual)):
        v = (ord(c) - 33 - Q) if b in "ACGT" else -10**6
        if cur <= 0: cur, cs = v, i
        else: cur += v
        if best is None or cur >= best: best, bs, be = cur, cs, i + 1
    return bs, be

for lab, path in dumps:
    ours, wrong = {}, []
    unm = {}
    for l in open(path):
        x = l.rstrip("\n").split("\t")
        if x[1] == "none":
            if lab in UNM:   # why unmapped, at A's caps: true locus beyond the cap or not
                pl = [truthPen(int(x[0][1:]) - 1, k) for k in (0, 1)]
                c = ("trimmed away / mate < 75 bp" if any(p is None or CAPA(n) is None for p, n in pl) else
                     "true locus within cap (tie / not proper / other)" if all(p <= CAPA(n) for p, n in pl) else
                     "true locus beyond cap")
                unm[c] = unm.get(c, 0) + 1
            continue
        i = int(x[0][1:]) - 1
        hs = [(CH[int(x[5 * m + 1])], int(x[5 * m + 2]), int(x[5 * m + 3]), -int(x[5 * m + 4]), x[5 * m + 5]) for m in (0, 1)]
        ours[i] = [(0, ok(i, k, c, s, s + n)) for k, (c, s, n, _, _) in enumerate(hs)]
        wrong += [(i, k, hs[k][3]) for k in (0, 1) if not ours[i][k][1]]
    pts = curve(lab, ours)
    cmp = {"truth worse": 0, "truth equal": 0, "truth better": 0}
    for i, k, pen in wrong:
        tp = truthPen(i, k)[0]
        cmp["truth worse" if tp > pen else "truth equal" if tp == pen else "truth better"] += 1
    pts[0]["wrong_vs_truth"] = cmp
    if unm: pts[0]["unmapped"] = unm
    res[lab] = pts
json.dump(dict(n_pairs=N, points=res), open(out, "w"), indent=1)
for lab, pts in res.items():
    for p in pts:
        print(f"{lab:>10} thr {str(p['thr']):>4}: reads {p['pct_reads']:6.2f}% wrong {p['reads_wrong']:5d} err {p['err_reads']:.2e} | "
              f"pairs {p['pct_pairs']:6.2f}% wrong {p['pairs_wrong']:5d} err {p['err_pairs']:.2e} {p.get('wrong_vs_truth', '')} {p.get('unmapped', '')}")
