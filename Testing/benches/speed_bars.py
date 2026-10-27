#!/usr/bin/env python3
"""Benchmark only.  minibwa paper Fig 3 style speed (Gbp/hr) and peak memory, minibwa vs our configs.
   python3 bench/speed_bars.py <out.png> <threads> <set>=<run_dir>=<R1.fq>,<R2.fq>=<cfg,cfg,...> ...
Gbp/hr = input bases / mapping wall time (index load excluded) and / total wall time (load included).
run_dir as in bench/sim_plot.py (mb.err; <cfg>.log).  Paper: minibwa 135.82 Gbp/hr on 32 threads
(4.24 / thread), 8.28 GB, full 30x HG002 NovaSeq; here 4 threads on 200k pairs, so compare the
minibwa / ours ratio within one session, and minibwa's per-thread rate with the paper's."""
import re, sys
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sim_common import BLUE, ORANGE, AQUA, NAMES, MARK, times
out, th = sys.argv[1], int(sys.argv[2])

def bases(p):
    with open(p) as h: return sum(len(l) - 1 for i, l in enumerate(h) if i % 4 == 1)

rows = []
print(f"| set | mapper | mapping s | total s | Gbp/hr (mapping) | Gbp/hr (total) | Gbp/hr/thread (mapping) | × minibwa (mapping) | peak RSS GB |")
print("|---|---|---|---|---|---|---|---|---|")
for a in sys.argv[3:]:
    s, d, fqs, cfgs = a.split("=")
    b = sum(bases(p) for p in fqs.split(","))
    mbt = times(d, "mb")[0]
    for c in ["mb"] + cfgs.split(","):
        t, tt, r = times(d, c)
        g, gt = b / t * 3600 / 1e9, b / tt * 3600 / 1e9
        rows.append((s, c, g, gt, r))
        print(f"| {s} | {'minibwa' if c == 'mb' else 'ours: ' + NAMES[c]} | {t:.1f} | {tt:.1f} | {g:.2f} | {gt:.2f} | {g / th:.2f} | {mbt / t:.2f} | {r:.2f} |")
print(f"paper (32 threads, 30x HG002 NovaSeq): minibwa 135.82 Gbp/hr = {135.82 / 32:.2f} / thread, 8.28 GB")

sets = list(dict.fromkeys(r[0] for r in rows))
cnt = [sum(r[0] == s for r in rows) for s in sets]
fig, axs = plt.subplots(len(sets), 2, figsize=(10, 1.2 + 0.42 * sum(cnt) + 0.6 * len(sets)), squeeze=False,
                        gridspec_kw=dict(height_ratios=cnt))
for i, s in enumerate(sets):
    rs = [r for r in rows if r[0] == s][::-1]
    lab = ["minibwa" if r[1] == "mb" else "ours: " + NAMES[r[1]] for r in rs]
    col = [ORANGE if r[1] == "mb" else BLUE for r in rs]
    for j, (k, xl) in enumerate([(2, "Gbp/hr, index load excluded (light: load included)"), (4, "peak RSS (GB)")]):
        ax = axs[i][j]
        if k == 2: ax.barh(lab, [r[3] for r in rs], color=col, alpha=0.35, height=0.7)
        ax.barh(lab, [r[k] for r in rs], color=col, height=0.7 if k == 4 else 0.4)
        for y, r in enumerate(rs): ax.text(r[k], y, f" {r[k]:.2f}", va="center", fontsize=7, color="#333")
        ax.set_xlabel(xl, fontsize=8); ax.tick_params(labelsize=7)
        ax.set_title(f"{s} ({th} threads)", fontsize=9)
        ax.grid(True, axis="x", color="#dddddd", lw=0.6); ax.set_axisbelow(True)
        for sp in ("top", "right"): ax.spines[sp].set_visible(False)
        if j == 1: ax.set_yticklabels([])
fig.text(0.01, 0.003, "Paper Fig 3 (32 threads, 30x HG002 NovaSeq): minibwa 135.82 Gbp/hr (4.24/thread), 8.28 GB. "
         "Here: 4 threads, 200k pairs; compare ratios within this session.", fontsize=7, color="#555")
fig.tight_layout(rect=(0, 0.03, 1, 1)); fig.savefig(out, dpi=150)
