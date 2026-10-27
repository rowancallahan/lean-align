#!/usr/bin/env python3
"""Benchmark only.  Plots for bench/sim_eval.py results.
   python3 bench/sim_plot.py <out_prefix> <set>=<eval.json>=<run_dir> ...
run_dir holds mb.txt / mb.err (minibwa; mapping time = Real time - index loaded) and <cfg>.log
(whole_genome RESULT line: mapping seconds; peak_rss_GB).  Writes <prefix>_roc_reads.png (Fig 2a
style, per read), <prefix>_roc_pairs.png (both mates), <prefix>_time.png (time vs % pairs aligned,
all and correct only), and prints the table."""
import json, re, sys
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sim_common import BLUE, ORANGE, AQUA, NAMES, MARK, times
pre, sets = sys.argv[1], [a.split("=") for a in sys.argv[2:]]
FLOOR = 1e-8

data = {s: (json.load(open(j)), d) for s, j, d in sets}
print("| set | mapper | MAPQ ≥ | reads aligned % | read err | pairs aligned % | pair err | wrong pairs | pairs correct % | mapping s | total s | RSS GB | our wrong mates: truth worse / equal / better |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for s, (J, d) in data.items():
    for lab, pts in J["points"].items():
        t, tt, r = times(d, lab)
        for p in pts:
            p["secs"], p["rss"] = t, r
            p["pct_ok_pairs"] = 100 * (p["pairs"] - p["pairs_wrong"]) / J["n_pairs"]
            w = p.get("wrong_vs_truth")
            print(f"| {s} | {'minibwa' if lab == 'minibwa' else NAMES.get(lab, lab)} | {'' if p['thr'] is None else p['thr']} | "
                  f"{p['pct_reads']:.2f} | {p['err_reads']:.1e} | {p['pct_pairs']:.2f} | {p['err_pairs']:.1e} | {p['pairs_wrong']} | "
                  f"{p['pct_ok_pairs']:.2f} | {t:.1f} | {tt:.1f} | {r:.2f} | {'' if not w else '%d / %d / %d' % tuple(w.values())} |")

def style(ax):
    ax.grid(True, color="#dddddd", lw=0.6); ax.set_axisbelow(True)
    for k in ("top", "right"): ax.spines[k].set_visible(False)

def roc(kind, path):
    fig, axs = plt.subplots(1, len(data), figsize=(5.2 * len(data), 4.6), squeeze=False)
    for ax, (s, (J, _)) in zip(axs[0], data.items()):
        mb = J["points"]["minibwa"]
        xs = [max(p[f"err_{kind}"], FLOOR) for p in mb]; ys = [p[f"pct_{kind}"] for p in mb]
        ax.plot(xs, ys, "-", color=ORANGE, lw=2, label="minibwa (MAPQ 60 … 0)")
        for x, y in zip(xs, ys):
            ax.plot(x, y, "o", ms=6, color=ORANGE, mec="white" if x > FLOOR else ORANGE, mfc=ORANGE if x > FLOOR else "white", mew=1.2)
        for p, x, y in zip(mb, xs, ys):
            if p["thr"] in (60, 20, 1, 0): ax.annotate(str(p["thr"]), (x, y), xytext=(4, -10), textcoords="offset points", fontsize=7, color="#555")
        groups = {}   # configs with identical results share one marker
        for lab, pts in J["points"].items():
            if lab != "minibwa": groups.setdefault((pts[0][kind], pts[0][f"{kind}_wrong"]), []).append(lab)
        for labs in groups.values():
            p = J["points"][labs[0]][0]; x = max(p[f"err_{kind}"], FLOOR)
            ax.plot(x, p[f"pct_{kind}"], MARK.get(labs[0], "o"), color=BLUE, ms=8, mew=1.2,
                    mec="white" if x > FLOOR else BLUE, mfc=BLUE if x > FLOOR else "white",
                    label="ours: " + " = ".join(NAMES.get(l, l) for l in labs))
        ax.set_xscale("log"); ax.set_xlim(FLOOR / 2, 1e-1)
        ax.set_xlabel(f"Accumulative error rate (#wrong / #aligned{', pairs' if kind == 'pairs' else ''})")
        ax.set_ylabel(f"% {'pairs' if kind == 'pairs' else 'reads'} aligned")
        style(ax)
        ax.set_title(s + "\nopen markers: no wrong placement (drawn at the axis edge)", fontsize=9)
    axs[0][0].legend(fontsize=7, loc="lower right", frameon=False)
    fig.tight_layout(); fig.savefig(path, dpi=150); plt.close(fig)

def tplot(path):
    fig, axs = plt.subplots(2, len(data), figsize=(5.2 * len(data), 8.4), squeeze=False)
    for col, (s, (J, _)) in enumerate(data.items()):
        mb = J["points"]["minibwa"]
        for row, (key, yl) in enumerate([("pct_pairs", "% pairs aligned"), ("pct_ok_pairs", "% pairs aligned correctly")]):
            ax = axs[row][col]
            ax.plot([p["secs"] for p in mb], [p[key] for p in mb], "o", color=ORANGE, ms=6, mec="white", mew=1, label="minibwa (one point per MAPQ threshold)")
            for p in mb:
                if p["thr"] in (60, 20, 0): ax.annotate(f"MAPQ≥{p['thr']}", (p["secs"], p[key]), xytext=(6, 0), textcoords="offset points", fontsize=7, color="#555", va="center")
            for lab, pts in J["points"].items():
                if lab != "minibwa":
                    ax.plot(pts[0]["secs"], pts[0][key], MARK.get(lab, "o"), color=BLUE, ms=8, mec="white", mew=1, label="ours: " + NAMES.get(lab, lab))
            ax.axvline(mb[0]["secs"] / 2, color=AQUA, lw=1.5, ls="--")
            ax.text(mb[0]["secs"] / 2, ax.get_ylim()[1], " 2× faster than minibwa", color="#333", fontsize=7, va="top")
            ax.set_xlim(left=0); ax.set_xlabel("mapping wall time, 4 threads (s)"); ax.set_ylabel(yl)
            ax.set_title(s, fontsize=10); style(ax)
    axs[0][0].legend(fontsize=7, loc="lower right", frameon=False)
    fig.tight_layout(); fig.savefig(path, dpi=150); plt.close(fig)

roc("reads", f"{pre}_roc_reads.png"); roc("pairs", f"{pre}_roc_pairs.png"); tplot(f"{pre}_time.png")
