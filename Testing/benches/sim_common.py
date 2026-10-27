"""Benchmark only.  Shared by bench/sim_plot.py, speed_bars.py, real_plot.py: config names, colors, timings."""
import re
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
NAMES = {"S0": "cap 16/12, <100 bp skipped", "A": "cap 16/12, 75-99 bp @11 (default)", "B": "short mates 50 bp",
         "P20": "short + pass 2 @20", "P23": "short + pass 2 @23/19/15", "C12": "cap 12", "C20": "cap 20/19/15",
         "C23": "cap 23/19/15"}
MARK = dict(S0="v", A="o", B="s", P20="D", P23="P", C12="<", C20=">", C23="^")

def times(d, cfg):
    """(mapping s, total s, peak RSS GB) of a run in run_dir d: minibwa from mb.err (mapping = Real time -
    index loaded), ours from <cfg>.log (RESULT line; wall_s and peak_rss_GB from the wrapper)."""
    if cfg in ("minibwa", "mb"):
        e = open(f"{d}/mb.err").read()
        load = float(re.search(r"main_map::([\d.]+)\*[\d.]+\] index loaded", e)[1])
        real = float(re.search(r"Real time: ([\d.]+)", e)[1])
        return real - load, real, float(re.search(r"Peak RSS: ([\d.]+)", e)[1])
    l = open(f"{d}/{cfg}.log").read()
    return (float(re.search(r"kept \d+, ([\d.]+) s", l)[1]), float(re.search(r"wall_s ([\d.]+)", l)[1]),
            float(re.search(r"peak_rss_GB ([\d.]+)", l)[1]))
