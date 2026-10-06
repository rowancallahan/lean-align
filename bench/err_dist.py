#!/usr/bin/env python3
"""Benchmark only.  Where do real pairs go?  Joins the proved mapper's whole-genome dump
(p<i> = i-th pair of the cut FASTQ, 'none' = unmapped) with minibwa's alignments of the
trimmed reads re-scored by the spec scoring (bench/mb_penalty.py), and plots the share of
pairs whose mates' best penalties are within each cutoff.
   python3 bench/err_dist.py <cut_R1.fq> <our_dump.tsv> <mb.pen> <out.png>"""
import sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

cut1, dump, pen, png = sys.argv[1:5]
names = [l[1:].split()[0] for i, l in enumerate(open(cut1)) if i % 4 == 0]
ours = {}
for l in open(dump):
    f = l.split("\t")
    ours[int(f[0][1:]) - 1] = f[1].strip() != "none"
assert len(ours) == len(names), (len(ours), len(names))
mb = {}
for l in open(pen):
    f = l.split("\t")
    mb[f[0]] = (int(f[1]), int(f[2]), int(f[3]), int(f[4]), int(f[5]), int(f[6]), int(f[7]))

def capRun(n): return 16 if n >= 150 else 12 if n >= 100 else -1      # current dispatch
def capOld(n): return max(P for P in range(80) if max(P // 4, (P - 6) // 2) <= n // 25 - 1)
def capNew(n): return 4 * (n // 25) - 1                                # event-based: P/4 <= n/25 - 1

N = len(names)
cat = {}
def bump(k): cat[k] = cat.get(k, 0) + 1
need = []  # max over mates of penalty, for proper minibwa pairs with both mates >= 100
for i, nm in enumerate(names):
    m = mb.get(nm)
    if ours[i]: bump("ours: mapped");
    if m: need.append((m[2], m[3], m[0], m[1], m[4], m[5], m[6]))
    if ours[i]: continue
    if not m: bump("unmapped: trimmed away"); continue
    l1, l2, p1, p2, q1, q2, proper = m
    if min(l1, l2) < 100: bump("unmapped: mate < 100 bp after trimming"); continue
    if not proper or p1 < 0 or p2 < 0: bump("unmapped: minibwa not a proper pair"); continue
    if p1 > capRun(l1) or p2 > capRun(l2):
        bump("unmapped: beyond cap (16 / 12), new proved cap reaches" if p1 <= capNew(l1) and p2 <= capNew(l2)
             else "unmapped: beyond cap and beyond new proved cap"); continue
    bump("unmapped: within cap, minibwa MAPQ 0 (repeat tie)" if min(q1, q2) == 0
         else "unmapped: within cap, minibwa MAPQ > 0 (tie/insert/other)")
print(f"pairs: {N}")
for k in sorted(cat): print(f"{k}: {cat[k]} ({100 * cat[k] / N:.1f}%)")

ok = [x for x in need if min(x[2], x[3]) >= 100 and x[6] and x[0] >= 0 and x[1] >= 0]
uniq = [x for x in ok if min(x[4], x[5]) > 0]
for lab, f in (("run caps (16/12)", capRun), ("old proved caps", capOld), ("new proved caps", capNew)):
    print(f"minibwa proper pairs, both mates <= {lab}: {sum(x[0] <= f(x[2]) and x[1] <= f(x[3]) for x in ok)} / {N}"
          f";  MAPQ>0: {sum(x[0] <= f(x[2]) and x[1] <= f(x[3]) for x in uniq)}")
xs = list(range(0, 81))
ya = [100 * sum(max(x[0], x[1]) <= c for x in ok) / N for c in xs]
yu = [100 * sum(max(x[0], x[1]) <= c for x in uniq) / N for c in xs]
plt.figure(figsize=(8, 5))
plt.plot(xs, ya, label="minibwa proper pairs (both mates ≥ 100 bp)")
plt.plot(xs, yu, label="same, MAPQ > 0 both mates (not a repeat tie)")
for c, lab, st in ((16, "running cap 16", "-"), (25, "old proved cap @250bp", "--"), (39, "new proved cap @250bp", ":")):
    plt.axvline(c, color="k", ls=st, lw=1, label=lab)
plt.axhline(100 * cat["ours: mapped"] / N, color="r", lw=1, label=f"ours kept ({100 * cat['ours: mapped'] / N:.1f}%)")
plt.xlabel("penalty cutoff per mate (mismatch 4, gap 6+2L), worse mate of the pair")
plt.ylabel("% of all pairs")
plt.title(f"HG002, {N} trimmed pairs, whole genome")
plt.grid(alpha=.3); plt.legend(fontsize=8); plt.tight_layout(); plt.savefig(png, dpi=120)
print("wrote", png)
