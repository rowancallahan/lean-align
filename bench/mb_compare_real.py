#!/usr/bin/env python3
"""Benchmark only.  minibwa paired SAM vs trim_map's pair dump on real reads (no truth).
   python3 bench/mb_compare_real.py <minibwa.sam> <trim_map.tsv> <chrom names in dump order...>
A minibwa pair "reports" when both primary records are mapped with the proper-pair flag;
MAPQ = min of the two.  Positions compared after removing a leading soft clip, within TOL
bp.  minibwa's own penalty (sc0: mismatch 4, gap 6 + 2L) from CIGAR + NM; soft clips count
as beyond the cap (the spec is global).  Pairs trim_map marks `unmapped: trimmed/length`
are counted apart."""
import re, sys
TOL = 5
sam, dump, names = sys.argv[1], sys.argv[2], sys.argv[3:]
CAP = int(__import__("os").environ.get("CAP", "12"))

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

sp, skip = {}, {}
for line in open(dump):
    f = line.rstrip("\n").split("\t")
    if f[1].startswith("unmapped"): skip[f[0]] = f[1]; continue
    if f[1] == "none": sp[f[0]] = None; continue
    sp[f[0]] = (names[int(f[1])], (int(f[2]), f[5]), (int(f[7]), f[10]))

def near(x, y): return x[1] == y[1] and abs(x[0] - y[0]) <= TOL
rows = {}
def bump(k): rows[k] = rows.get(k, 0) + 1
for p, s in sp.items():
    m = mb.get(p)
    mrep = m and m[0] and m[1] and not (m[0][0] & 4) and not (m[1][0] & 4) and m[0][0] & 2
    mq = min(m[0][4], m[1][4]) if mrep else -1
    bump("pairs compared")
    if s: bump("spec maps")
    if mrep: bump("mb proper pair")
    for q in (0, 20, 60):
        if not (mrep and mq >= q):
            if s: bump(f"q>={q}: spec maps, mb not")
            continue
        bump(f"q>={q}: mb reports")
        same = s and s[0] == m[0][1] and near(s[1], (m[0][2], m[0][3])) and near(s[2], (m[1][2], m[1][3]))
        if s: bump(f"q>={q}: both map, " + ("same place" if same else "DIFFERENT"))
        else:
            within = m[0][5] <= CAP and m[1][5] <= CAP
            bump(f"q>={q}: mb maps, spec unmapped: " + ("both mates within cap (spec tie/ambiguous or improper)" if within
                 else "beyond cap or clipped"))
print(f"dump pairs skipped by trim_map: {len(skip)}  (" + ", ".join(f"{v}: {list(skip.values()).count(v)}" for v in sorted(set(skip.values()))) + ")")
for k in sorted(rows): print(f"{k}: {rows[k]}")
