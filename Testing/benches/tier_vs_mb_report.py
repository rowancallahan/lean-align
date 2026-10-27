#!/usr/bin/env python3
"""Benchmark only.  Report on the joins written by bench/tier_vs_mb.py (one per set).

   python3 bench/tier_vs_mb_report.py G set=join.tsv ... > report.md

Penalties: spec scoring of OUR trimmed mate, end to end (see tier_vs_mb.py).  Ours on T2 = the
dumped ceilings (ceil1 + ceil2); minibwa = its placement re-scored.  Floors: per mate `fl` (proved,
genome-wide); per pair fl1 + fl2, and the pair guarantee (no proper pair with total <= G: floor
G + 1; suffix z: floor 1; suffix x: none) when minibwa's placements form a proper pair by our
definition (`properPairU 0`: same chromosome, facing, fragment in [WG_MIN, WG_MAX] = [100, 1000], no
dovetail), measured on the re-alignment windows (a margin within 3 letters is flagged borderline).
T1: each mate's pen is the proved unique best within cap: minibwa < pen is a violation, minibwa ==
pen at a non-overlapping place a tie (uniqueness) violation.  T1g: the proved unique best proper pair
with total <= G: a proper minibwa pair with total <= ours elsewhere is a violation (a second pair
within G).  T1gm (>= 2 pairs within G; the dumped pair is the first found, not the best): a proper
minibwa pair is only counted, no claim to check.  NB pairGX (the G guarantee) is marked "bench only,
unproved" in WholeGenome.lean; WG_PGK=1 (proved pairGK) is off by default."""
import sys
from collections import Counter

LO, HI, BORDER = 100, 1000, 3
G = int(sys.argv[1])


def load(path):
    rows = []
    with open(path) as h:
        hdr = h.readline().rstrip("\n").split("\t")
        for l in h:
            r = dict(zip(hdr, l.rstrip("\n").split("\t")))
            r["base"] = r["tier"].rstrip("xz")
            for k in "12":
                for x in ("cap", "fl", "pen", "ceil", "src", "ours", "mbpen", "len"):
                    r[x + k] = int(r[x + k])
                r["pl" + k] = None if r["pl" + k] == "-" else pl(r["pl" + k])
                r["mbpl" + k] = None if r["mbpl" + k] == "-" else pl(r["mbpl" + k])
                r["mapq" + k] = int(r["mapq" + k]) if r["mapq" + k] != "-" else -1
            r["both"] = r["mbpl1"] is not None and r["mbpl2"] is not None
            r["mbtot"] = r["mbpen1"] + r["mbpen2"] if r["both"] else None
            r["mq"] = min(r["mapq1"], r["mapq2"])
            rows.append(r)
    return rows


def pl(s):
    c, a, n, sd = s.split(":")
    return (c, int(a), int(n), sd)


def ov(a, b):
    return a is not None and b is not None and a[0] == b[0] and a[3] == b[3] and a[1] < b[1] + b[2] and b[1] < a[1] + a[2]


def proper(a, b):
    """(properPairU 0 LO HI, borderline: a margin within BORDER letters)"""
    if a is None or b is None or a[0] != b[0] or a[3] == b[3]:
        return False, False
    f, r = (a, b) if a[3] == "+" else (b, a)
    fr = r[1] + r[2] - f[1]
    m = [fr - LO, HI - fr, r[1] - f[1], r[1] + r[2] - f[1] - f[2]]
    return min(m) >= 0, min(abs(x) for x in m) <= BORDER


def pq(v, q):
    v = sorted(v)
    return v[min(len(v) - 1, len(v) * q // 100)] if v else "-"


def pct(a, b):
    return f"{100 * a / b:.1f}" if b else "-"


def same(r):
    return ov(r["pl1"], r["mbpl1"]) and ov(r["pl2"], r["mbpl2"])


def pfloor(r):
    f = r["fl1"] + r["fl2"]
    pr, bd = proper(r["mbpl1"], r["mbpl2"])
    if pr:
        t = r["tier"]
        gf = 1 if t.endswith("z") else 0 if t.endswith("x") else G + 1
        f = max(f, gf)
    return f, pr, bd


def section(name, R, out):
    P = lambda *a: print(*a, file=out)
    mason = R[0]["ok1"] != ""
    tc = Counter(r["base"] for r in R)
    P(f"\n## {name}: {len(R)} pairs; " + ", ".join(f"{t} {tc[t]} ({pct(tc[t], len(R))}%)" for t in ("T1", "T1g", "T1gm", "T2", "T3")))
    # sanity: our dumped scores re-score the same
    bad = Counter()
    for r in R:
        for k in "12":
            if r["pl" + k] is None:
                continue
            want = r["pen" + k] if r["base"] in ("T1", "T1g", "T1gm") or r["st" + k] == "U" else r["ceil" + k]
            bad["n"] += 1
            if r["ours" + k] > want:
                bad["bad"] += 1
                if bad["bad"] <= 5:
                    P(f"- **SELF-CHECK FAIL** {r['name']} mate{k} {r['tier']}: dumped {want}, re-scored {r['ours' + k]}")
            elif r["ours" + k] < want:
                bad["lower"] += 1
    P(f"\nSelf-check: our dumped placements re-scored by parasail (global on our window): {bad['n']} mates, "
      f"equal {bad['n'] - bad['bad'] - bad['lower']}, re-score lower (gapless ceiling, gaps help) {bad['lower']}, "
      f"**re-score higher (error) {bad['bad']}**.")

    # 1. T2
    T2 = [r for r in R if r["base"] == "T2"]
    P("\n### 1. T2: our pair ceiling vs minibwa's pair penalty at its placement")
    P("| minibwa MAPQ | T2 pairs | mb maps both | ours better | equal | worse | diff p10/p50/p90 (ours-mb) | min/max | same place |")
    P("|---|---|---|---|---|---|---|---|---|")
    for lab, sel in (("all", lambda r: True), ("≥20", lambda r: r["both"] and r["mq"] >= 20),
                     ("<20", lambda r: r["both"] and r["mq"] < 20)):
        S = [r for r in T2 if sel(r)]
        B = [r for r in S if r["both"]]
        d = [r["ceil1"] + r["ceil2"] - r["mbtot"] for r in B]
        P(f"| {lab} | {len(S)} | {len(B)} | {pct(sum(x < 0 for x in d), len(B))}% | {pct(sum(x == 0 for x in d), len(B))}% | "
          f"{pct(sum(x > 0 for x in d), len(B))}% | {pq(d, 10)}/{pq(d, 50)}/{pq(d, 90)} | {min(d) if d else '-'}/{max(d) if d else '-'} | "
          f"{pct(sum(same(r) for r in B), len(B))}% |")
    B = [r for r in T2 if r["both"]]
    h = Counter()
    for r in B:
        x = r["ceil1"] + r["ceil2"] - r["mbtot"]
        h["<-8" if x < -8 else "-8..-1" if x < 0 else "0" if x == 0 else "1..4" if x <= 4 else "5..8" if x <= 8 else
          "9..16" if x <= 16 else "17..32" if x <= 32 else ">32"] += 1
    P("\nDiff histogram (T2, mb maps both): " + ", ".join(f"{k}: {h[k]}" for k in ("<-8", "-8..-1", "0", "1..4", "5..8", "9..16", "17..32", ">32")))

    # 2. T3
    T3 = [r for r in R if r["base"] == "T3"]
    mp = [r for r in T3 if r["both"] and r["mbproper"] == "1"]
    m1 = [r for r in mp if r["mq"] >= 1]
    m20 = [r for r in mp if r["mq"] >= 20]
    P(f"\n### 2. T3 ({len(T3)} pairs): minibwa proper pair {pct(len(mp), len(T3))}%, MAPQ≥1 {pct(len(m1), len(T3))}%, MAPQ≥20 {pct(len(m20), len(T3))}%")
    P("| subset | n | mb pair pen p10/p50/p90/max | mb max-mate pen p50/p90 |")
    P("|---|---|---|---|")
    for lab, S in (("proper MAPQ≥1", m1), ("proper MAPQ≥20", m20)):
        v = [r["mbtot"] for r in S]
        w = [max(r["mbpen1"], r["mbpen2"]) for r in S]
        P(f"| {lab} | {len(S)} | {pq(v, 10)}/{pq(v, 50)}/{pq(v, 90)}/{max(v) if v else '-'} | {pq(w, 50)}/{pq(w, 90)} |")

    # 3. floors
    P("\n### 3. Floor sanity (T2/T3): minibwa's re-scored alignment vs our proved floor")
    viol, nm, npair, bord = [], 0, 0, 0
    for r in T2 + T3:
        for k in "12":
            if r["mbpl" + k] is None:
                continue
            nm += 1
            if r["mbpen" + k] < r["fl" + k]:
                viol.append(("mate" + k, r, r["mbpen" + k], r["fl" + k]))
        if r["both"]:
            npair += 1
            f, pr, bd = pfloor(r)
            if r["mbtot"] < f:
                viol.append(("pair" + (" BORDERLINE" if bd else ""), r, r["mbtot"], f))
    fpos = [(r["mbpen" + k], r["fl" + k]) for r in T2 + T3 for k in "12" if r["mbpl" + k] and r["fl" + k] > 0]
    pfa = [(r["mbtot"], pfloor(r)[0]) for r in T2 + T3 if r["both"] and pfloor(r)[1]]
    P(f"Teeth: mates with floor > 0 checked {len(fpos)} (minibwa exactly at the floor {sum(a == b for a, b in fpos)}); "
      f"pairs proper by properPairU 0 (pair guarantee applies) {len(pfa)} (minibwa exactly at the pair floor {sum(a == b for a, b in pfa)}).")
    gap = [min(r["mbpen" + k] - r["fl" + k] for k in "12" if r["mbpl" + k]) for r in T2 + T3 if r["mbpl1"] or r["mbpl2"]]
    P(f"Mates checked {nm}, pairs checked {npair}: **violations {len(viol)}**; "
      f"slack (mb pen - floor, min over mates) p0 {pq(gap, 0)} p10 {pq(gap, 10)} p50 {pq(gap, 50)}")
    for kind, r, a, b in viol[:50]:
        P(f"- **VIOLATION** {kind} {r['name']} tier {r['tier']}: minibwa {a} < floor {b} (floors {r['fl1']}/{r['fl2']}, "
          f"mb pens {r['mbpen1']}/{r['mbpen2']}; re-aligned {fmt(r['mbpl1'])}/{fmt(r['mbpl2'])}; minibwa {r['mbraw1']} "
          f"{r['cigar1']} / {r['mbraw2']} {r['cigar2']}; lens {r['len1']}/{r['len2']}; src {r['src1']}/{r['src2']})")

    # 4. T1 / T1g
    P("\n### 4. T1 / T1g: minibwa never strictly better than our proved best")
    v1, t1, n1 = [], [], 0
    for r in R:
        if r["base"] != "T1":
            continue
        for k in "12":
            if r["mbpl" + k] is None:
                continue
            n1 += 1
            if r["mbpen" + k] < r["pen" + k]:
                v1.append((k, r))
            elif r["mbpen" + k] == r["pen" + k] and not ov(r["pl" + k], r["mbpl" + k]):
                t1.append((k, r))
    vg, tg, ng, nm4, ngm = [], [], 0, 0, 0
    for r in R:
        if r["base"] not in ("T1g", "T1gm") or not r["both"]:
            continue
        pr, bd = proper(r["mbpl1"], r["mbpl2"])
        if not pr:
            continue
        if r["base"] == "T1gm":
            ngm += 1
            nm4 += r["mbtot"] <= G
            continue
        ng += 1
        ours = r["pen1"] + r["pen2"]
        if r["mbtot"] < ours:
            vg.append((r, bd))
        elif r["mbtot"] == ours and not same(r):
            tg.append((r, bd))
    P(f"T1 mates checked {n1}: **strictly better {len(v1)}**, equal at another place {len(t1)}.  "
      f"T1g pairs with a proper minibwa pair {ng}: **strictly better {len(vg)}**, **equal elsewhere {len(tg)}**.  "
      f"T1gm with a proper minibwa pair {ngm}, of which total <= G {nm4}.")
    for k, r in v1[:30]:
        P(f"- **VIOLATION T1** {r['name']} mate{k}: minibwa {r['mbpen' + k]} at {r['mbpl' + k]} < ours {r['pen' + k]} at {r['pl' + k]}")
    for k, r in t1[:10]:
        P(f"- tie T1 {r['name']} mate{k}: {r['pen' + k]} ours {r['pl' + k]} vs mb {r['mbpl' + k]} {r['cigar' + k]}")
    for r, bd in vg[:30]:
        P(f"- **VIOLATION T1g**{' (borderline fragment)' if bd else ''} {r['name']}: minibwa {r['mbtot']} < ours {r['pen1'] + r['pen2']}")
    for r, bd in tg[:30]:
        P(f"- **VIOLATION T1g (second pair within G)**{' (borderline)' if bd else ''} {r['name']}: {r['mbtot']} ours {r['pl1']},{r['pl2']} vs mb {r['mbpl1']},{r['mbpl2']}")

    # 5. mason
    if mason:
        P("\n### 5. mason: % pairs correct (both mates overlap the truth, same strand)")
        P("| subset | n | ours (T2 ceilings) | minibwa |")
        P("|---|---|---|---|")
        for lab, S in (("T2", T2), ("T2, mb MAPQ≥20", [r for r in T2 if r["both"] and r["mq"] >= 20]),
                       ("T3", T3)):
            oc = sum(r["ok1"] == "1" and r["ok2"] == "1" for r in S)
            mc = sum(r["mbok1"] == "1" and r["mbok2"] == "1" for r in S)
            P(f"| {lab} | {len(S)} | {pct(oc, len(S)) if lab != 'T3' else '- (unmapped)'}% | {pct(mc, len(S))}% |")

    # classes
    P("\n### 6. T2+T3 by read class (minibwa's view)")
    TT = T2 + T3
    xa = lambda r: r["xa1"] == "1" or r["xa2"] == "1"
    uniq = lambda r: r["both"] and r["mbproper"] == "1" and r["mq"] >= 20 and not xa(r)
    multi = lambda r: r["both"] and (r["mq"] < 20 or xa(r))
    hi = lambda r: r["both"] and max(r["mbpen1"], r["mbpen2"]) > 16
    short = lambda r: min(r["len1"], r["len2"]) < 75
    indel = lambda r: any(c in r["cigar" + k] for k in "12" for c in "ID")
    clip = lambda r: any("S" in r["cigar" + k] for k in "12")
    classes = [("(a) unique: proper, MAPQ≥20, no XA", uniq),
               ("(a) and not c/d/e/f", lambda r: uniq(r) and not hi(r) and not short(r) and not indel(r) and not clip(r)),
               ("(a') unique but not proper", lambda r: r["both"] and r["mbproper"] != "1" and r["mq"] >= 20 and not xa(r)),
               ("(b) multimapper: MAPQ<20 or XA", multi),
               ("(c) high-error: mb mate pen > 16", hi),
               ("(d) short: a mate < 75 bp", short),
               ("(e) indel in mb CIGAR", indel),
               ("(f) soft-clipped by mb", clip),
               ("mb maps < 2 mates", lambda r: not r["both"])]
    P("| class | n | % of T2+T3 | T2 % | T3 % | gap ours-mb p50/p90/max (T2) | same place (T2) | mason ours/mb correct |")
    P("|---|---|---|---|---|---|---|---|")
    for lab, sel in classes:
        S = [r for r in TT if sel(r)]
        s2 = [r for r in S if r["base"] == "T2"]
        b2 = [r for r in s2 if r["both"]]
        d = [r["ceil1"] + r["ceil2"] - r["mbtot"] for r in b2]
        mc = ""
        if mason:
            oc = sum(r["base"] == "T2" and r["ok1"] == "1" and r["ok2"] == "1" for r in S)
            mm = sum(r["mbok1"] == "1" and r["mbok2"] == "1" for r in S)
            mc = f"{pct(oc, len(S))}/{pct(mm, len(S))}%"
        P(f"| {lab} | {len(S)} | {pct(len(S), len(TT))}% | {pct(len(s2), len(S))} | {pct(len(S) - len(s2), len(S))} | "
          f"{pq(d, 50)}/{pq(d, 90)}/{max(d) if d else '-'} | {pct(sum(same(r) for r in b2), len(b2))}% | {mc} |")
    A = [r for r in TT if uniq(r)]
    d = [r["ceil1"] + r["ceil2"] - r["mbtot"] if r["base"] == "T2" else None for r in A]
    n = len(A)
    c0 = sum(x is not None and x <= 0 for x in d)
    c4 = sum(x is not None and x <= 4 for x in d)
    c8 = sum(x is not None and x <= 8 for x in d)
    f3 = sum(x is None for x in d)
    P(f"\n**Headline, class (a), {n} pairs: ours within 0 of minibwa {pct(c0, n)}%, ≤4 {pct(c4, n)}%, ≤8 {pct(c8, n)}%; "
      f"> 8 worse {pct(n - c8 - f3, n)}%; T3 (fails entirely while minibwa maps uniquely) {pct(f3, n)}%.**")
    P("\nClass (a), per mate (T2+T3): what our ceiling is, against minibwa's mate")
    P("| mate ceiling | all mates | mb mate gapless | mb mate has indel |")
    P("|---|---|---|---|")
    cat = Counter()
    for r in A:
        for k in "12":
            c = r["ceil" + k]
            g = "indel" if any(x in r["cigar" + k] for x in "ID") else "gapless"
            if c >= 1000000:
                key = "none (no ceiling)"
            elif r["pl" + k] is None:
                key = "value only (RT cap, no placement)"
            elif ov(r["pl" + k], r["mbpl" + k]):
                key = "at mb's place, <= mb" if c <= r["mbpen" + k] else "at mb's place, worse"
            else:
                key = "elsewhere, <= mb" if c <= r["mbpen" + k] else "elsewhere, worse"
            cat[(key, g)] += 1
            cat[(key, "all")] += 1
    tot = {g: sum(v for (kk, gg), v in cat.items() if gg == g) for g in ("all", "gapless", "indel")}
    for key in ("at mb's place, <= mb", "at mb's place, worse", "elsewhere, <= mb", "elsewhere, worse",
                "value only (RT cap, no placement)", "none (no ceiling)"):
        P(f"| {key} | " + " | ".join(f"{cat[(key, g)]} ({pct(cat[(key, g)], tot[g])}%)" for g in ("all", "gapless", "indel")) + " |")
    P("\nWorst class (a) T2 (largest ours - mb):")
    P("| name | tier | len | floor | ours ceil (pl) | mb pen (pl, MAPQ, CIGAR) |")
    P("|---|---|---|---|---|---|")
    W = sorted((r for r in A if r["base"] == "T2"), key=lambda r: -(r["ceil1"] + r["ceil2"] - r["mbtot"]))[:10]
    for r in W:
        P(f"| {r['name']} | {r['tier']} | {r['len1']}/{r['len2']} | {r['fl1']}/{r['fl2']} | "
          f"{r['ceil1']} ({fmt(r['pl1'])}) / {r['ceil2']} ({fmt(r['pl2'])}) | "
          f"{r['mbpen1']} ({fmt(r['mbpl1'])}, {r['mapq1']}, {r['cigar1']}) / {r['mbpen2']} ({fmt(r['mbpl2'])}, {r['mapq2']}, {r['cigar2']}) |")
    P("\nClass (a) T3 with the lowest minibwa pair penalty (failures):")
    P("| name | tier | len | floor | ceil | mb pen (pl, MAPQ, CIGAR) |")
    P("|---|---|---|---|---|---|")
    for r in sorted((r for r in A if r["base"] == "T3"), key=lambda r: r["mbtot"])[:10]:
        P(f"| {r['name']} | {r['tier']} | {r['len1']}/{r['len2']} | {r['fl1']}/{r['fl2']} | {cl(r['ceil1'])}/{cl(r['ceil2'])} | "
          f"{r['mbpen1']} ({fmt(r['mbpl1'])}, {r['mapq1']}, {r['cigar1']}) / {r['mbpen2']} ({fmt(r['mbpl2'])}, {r['mapq2']}, {r['cigar2']}) |")
    return len(viol) + len(v1) + len(vg) + len(tg)


def fmt(p):
    return f"{p[0]}:{p[1]}{p[3]}" if p else "-"


def cl(x):
    return "-" if x >= 1000000 else str(x)


def main():
    nv = 0
    print(f"# RTX tiers vs minibwa (G = {G}; scoring: our trimmed mate end to end, both mappers)")
    for a in sys.argv[2:]:
        name, path = a.split("=", 1)
        nv += section(name, load(path), sys.stdout)
    print(f"\n**Total floor / T1 violations: {nv}**")


if __name__ == "__main__":
    main()
