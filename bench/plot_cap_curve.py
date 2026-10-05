#!/usr/bin/env python3
"""Benchmark only.  Error cap vs % of minibwa's unique proper pairs aligned (HG002 200k, Q25).
Ceiling lines from bench/cap_table.py output; our measured same-place points (mb_overlap.py)
are listed below.   python3 bench/plot_cap_curve.py <cap_table.txt> <out.png>"""
import sys, re
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

src, out = sys.argv[1:3]
tab, cur = {}, None
for l in open(src):
    m = re.search(r"MAPQ >= (\d+)", l)
    if m: cur = int(m.group(1)); tab[cur] = []; continue
    m = re.match(r"\s*(\d+) \|(.*)", l)
    if m and cur is not None and int(m.group(1)) < 999:
        tab[cur].append((int(m.group(1)), [float(v) for v in re.findall(r"([\d.]+)%", m.group(2))]))
# measured, same place as minibwa: (cap, % MAPQ>0, % MAPQ>=20)
ours100 = [(16, 88.75, 90.52)]                                           # mates >= 100 bp
ours75 = [(16, 89.53, 91.32)]                                            # + 75-99 bp (new default)
ours50 = [(16, 90.07, 91.87), (20, 91.02, 92.84), (24, 91.40, 93.22)]    # + 50-74 bp, pass 2
BLUE, ORANGE, AQUA, INK, MUTED = "#2a78d6", "#eb6834", "#1baf7a", "#1a1a19", "#6b6a62"
fig, axs = plt.subplots(1, 2, figsize=(12, 4.8), sharey=True)
for ax, mq, k in ((axs[0], 1, 1), (axs[1], 20, 2)):
    rows = tab[mq]
    x = [c for c, _ in rows]
    ax.plot(x, [v[2] for _, v in rows], color=BLUE, lw=2, ls="--", label="ceiling, mates ≥ 50 bp, any cap")
    ax.plot(x, [v[3] for _, v in rows], color=BLUE, lw=2, label="ceiling, mates ≥ 50 bp, within proved cap")
    ax.plot(x, [v[1] for _, v in rows], color=AQUA, lw=2, label="ceiling, mates ≥ 100 bp, within proved cap")
    for pts, col, mk, lab in ((ours100, AQUA, "s", "ours, mates ≥ 100 bp"),
                              (ours75, ORANGE, "D", "ours, mates ≥ 75 bp (default)"),
                              (ours50, ORANGE, "o", "ours, mates ≥ 50 bp (+ pass 2 at 20, 24)")):
        ax.plot([p[0] for p in pts], [p[k] for p in pts], mk, color=col, ms=8, mfc=col if mk != "o" else "white",
                mew=2, label=lab, ls="-" if len(pts) > 1 else "", lw=1.5)
    for c, t in ((16, "cap 16 (now)"), (28, "cap 28 (goal)")):
        ax.axvline(c, color=MUTED, lw=1, ls=":")
        ax.text(c + 0.5, 86.3, t, color=MUTED, fontsize=9)
    ax.set_title(f"minibwa proper pairs, both mates MAPQ {'> 0' if mq == 1 else '≥ 20'}  (n = {'188,963' if mq == 1 else '185,217'})",
                 fontsize=10, color=INK)
    ax.set_xlabel("per-mate error cap (spec penalty: mismatch 4, gap 6 + 2·len)", color=INK)
    ax.grid(color="#e4e3dc", lw=0.8); ax.set_axisbelow(True)
    for s in ("top", "right"): ax.spines[s].set_visible(False)
    ax.set_xlim(10, 82); ax.set_ylim(86, 99)
axs[0].set_ylabel("% aligned (same place as minibwa)", color=INK)
axs[1].legend(loc="lower right", fontsize=8.5, frameon=False)
fig.suptitle("HG002 200k pairs, hg38, Q25 trimming: error cap vs % of minibwa's unique proper pairs", fontsize=11, color=INK)
fig.tight_layout()
fig.savefig(out, dpi=130)
