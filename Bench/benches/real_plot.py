#!/usr/bin/env python3
"""Benchmark only.  Real pairs (no truth): mapping time vs share of minibwa's unique proper pairs that
we place at the same place (bench/mb_overlap.py), for minibwa MAPQ > 0 and >= 20 denominators.
   python3 bench/real_plot.py <out.png> <genome.1l.fa> <set>=<run_dir>=<minibwa.sam>=<R1.fq>,<R2.fq>=<cfg,...> ...
run_dir: mb.err (minibwa timing, same session) and <cfg>.log / RT_<cfg>.tsv (ours).  Prints a table."""
import re, subprocess, sys
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sim_common import NAMES, MARK, BLUE, ORANGE, AQUA, times
out, fa = sys.argv[1], sys.argv[2]
CN = ",".join("chr%s" % c for c in list(range(1, 23)) + ["X", "Y"])
sets = [a.split("=") for a in sys.argv[3:]]
fig, axs = plt.subplots(len(sets), 2, figsize=(10.4, 4.2 * len(sets)), squeeze=False)
print("| set | mapper | mapping s | total s | RSS GB | kept pairs | same place % of D0 (MAPQ>0) | same place % of D20 (MAPQ≥20) |")
print("|---|---|---|---|---|---|---|---|")
for row, (s, d, sam, fqs, cfgs) in enumerate(sets):
    mt, mtt, mr = times(d, "minibwa")
    print(f"| {s} | minibwa | {mt:.1f} | {mtt:.1f} | {mr:.2f} | | 100 | 100 |")
    pts = []
    for c in cfgs.split(","):
        o = subprocess.run([sys.executable, __file__.replace("real_plot.py", "mb_overlap.py"), fa, sam, *fqs.split(","),
                            f"{d}/RT_{c}.tsv", CN, "25"], capture_output=True, text=True, check=True).stdout
        sp = [float(x) for x in re.findall(r"D: same place: \d+ \(([\d.]+)% of D\)", o)]
        kept = re.search(r"ours: mapped: (\d+)", o)[1]
        t, tt, r = times(d, c)
        pts.append((c, t, sp))
        print(f"| {s} | ours: {NAMES[c]} | {t:.1f} | {tt:.1f} | {r:.2f} | {kept} | {sp[0]:.2f} | {sp[1]:.2f} |")
    for j, lab in enumerate(("minibwa proper, both MAPQ > 0", "minibwa proper, both MAPQ ≥ 20")):
        ax = axs[row][j]
        ax.plot(mt, 100, "o", color=ORANGE, ms=8, mec="white", mew=1, label="minibwa (reference = 100%)")
        for c, t, sp in pts: ax.plot(t, sp[j], MARK[c], color=BLUE, ms=8, mec="white", mew=1, label="ours: " + NAMES[c])
        ax.axvline(mt / 2, color=AQUA, lw=1.5, ls="--")
        ax.text(mt / 2, 100.3, " 2× faster than minibwa", fontsize=7, color="#333", va="top")
        ax.set_xlim(left=0); ax.set_xlabel("mapping wall time, 4 threads (s)")
        ax.set_ylabel("% of minibwa's unique proper pairs, same place")
        ax.set_title(f"{s}: {lab}", fontsize=9)
        ax.grid(True, color="#dddddd", lw=0.6); ax.set_axisbelow(True)
        for sp_ in ("top", "right"): ax.spines[sp_].set_visible(False)
axs[0][0].legend(fontsize=7, loc="lower right", frameon=False)
fig.tight_layout(); fig.savefig(out, dpi=150)
