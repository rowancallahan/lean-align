#!/usr/bin/env python3
"""Unmapped breakdown.   analyze.py ours.sam minibwa.sam LABEL
Pairs are matched by name (both files in input order). Primary records only, plus a flag for "has a supplementary record".
Our class: unique = both mates mapped and XU:Z:unique on both; unknown = both mapped, not unique; unmapped = not both mates mapped.
minibwa class: unmapped = no mate mapped; single = one mate mapped; else both mapped with min MAPQ of the mates (bins) and the proper-pair flag."""
import collections, itertools, statistics as st, sys, pysam
def groups(path):
    for name, recs in itertools.groupby(pysam.AlignmentFile(path, check_sq=False), key=lambda r: r.query_name):
        recs = list(recs); prim = [r for r in recs if not (r.is_secondary or r.is_supplementary)]
        assert len(prim) == 2 and prim[0].is_read1 and prim[1].is_read2, name
        yield name, prim[0], prim[1], any(r.is_supplementary for r in recs)
def tag(r, t):
    return r.get_tag(t) if r.has_tag(t) else None
def xb_bin(v):
    return "none" if v is None else ">=-16" if v >= -16 else "-17..-40" if v >= -40 else "<-40"
def mq_bin(q):
    return "MAPQ0" if q == 0 else "MAPQ1-9" if q < 10 else "MAPQ10-29" if q < 30 else "MAPQ30-59" if q < 60 else "MAPQ60"
def clipped(r): return sum(n for op, n in r.cigartuples if op == 4) if r.cigartuples else 0
def nm(r): return tag(r, "NM") or 0
def our_class(o1, o2):
    if o1.is_unmapped or o2.is_unmapped:
        t = "single mate" if not (o1.is_unmapped and o2.is_unmapped) else "unmapped"
        trimmed = any((tag(r, "XT") or "").startswith("trimmedAway") for r in (o1, o2))
        xu = tag(o1, "XU") or tag(o2, "XU") or "no XU"
        xb = tag(o1, "XB"); xb = tag(o2, "XB") if xb is None else xb
        return f"{t}: " + ("XT trimmedAway" if trimmed else f"XU {xu}") + f", XB {xb_bin(xb)}"
    if tag(o1, "XU") == "unique" and tag(o2, "XU") == "unique": return "mapped unique"
    xb = tag(o1, "XB"); xu = tag(o1, "XU")
    return f"mapped {xu}, XB {xb_bin(xb)}"
def mb_class(m1, m2):
    if m1.is_unmapped and m2.is_unmapped: return "unmapped", None
    if m1.is_unmapped or m2.is_unmapped: return "single mate", None
    return mq_bin(min(m1.mapping_quality, m2.mapping_quality)), m1.is_proper_pair and m2.is_proper_pair
n = 0; tab = collections.defaultdict(collections.Counter); sub = []; head = collections.Counter()
for (name, o1, o2, _), (name2, m1, m2, supp) in zip(groups(sys.argv[1]), groups(sys.argv[2]), strict=True):
    assert name == name2
    n += 1; oc = our_class(o1, o2); mc, proper = mb_class(m1, m2)
    col = mc if proper is None else f"{mc} {'proper' if proper else 'not proper'}"
    tab[oc][col] += 1
    ours_cls = "unique" if oc == "mapped unique" else "mapped unknown" if oc.startswith("mapped") else "unmapped"
    mb_mapped = proper is not None; minq = min(m1.mapping_quality, m2.mapping_quality) if mb_mapped else -1
    good30 = mb_mapped and proper and minq >= 30; good60 = mb_mapped and proper and minq == 60
    if good30: head[("mb MAPQ>=30 & proper", ours_cls)] += 1
    if good60: head[("mb MAPQ==60 & proper", ours_cls)] += 1
    if not good30: head[("mb NOT (MAPQ>=30 & proper)", ours_cls)] += 1
    if ours_cls == "unmapped" and mb_mapped:
        c1, c2 = clipped(m1), clipped(m2); fwd = m2 if m1.is_reverse else m1; rev = m1 if m1.is_reverse else m2
        wrong = m1.is_reverse == m2.is_reverse or fwd.reference_start > rev.reference_end
        sub.append(dict(minq=minq, proper=proper, c1=c1, c2=c2, nm1=nm(m1), nm2=nm(m2), supp=supp,
                        chrom=m1.reference_id != m2.reference_id, far=m1.reference_id == m2.reference_id and abs(m1.template_length) > 1000, wrong=wrong))
pct = lambda v: f"{100 * v / n:6.2f}%"
print(f"=== {sys.argv[3]}: {n:,} pairs\n")
cols = ["unmapped", "single mate"] + [f"{b} {p}" for b in ("MAPQ0", "MAPQ1-9", "MAPQ10-29", "MAPQ30-59", "MAPQ60") for p in ("proper", "not proper")]
print("1. our class (rows) x minibwa class (columns); counts; % of all pairs in the last column")
for oc in sorted(tab, key=lambda k: -sum(tab[k].values())):
    tot = sum(tab[oc].values()); print(f"\n  {oc}: {tot:,} ({pct(tot)})")
    print("    " + "  ".join(f"{c}={tab[oc][c]:,}" for c in cols if tab[oc][c]))
s = sub; m = len(s)
print(f"\n2. pairs we leave unmapped (both mates not mapped) that minibwa maps (both mates): {m:,} ({pct(m)})")
if m:
    for b in ("MAPQ0", "MAPQ1-9", "MAPQ10-29", "MAPQ30-59", "MAPQ60"): print(f"   min MAPQ {b}: {sum(mq_bin(x['minq']) == b for x in s):,} ({100*sum(mq_bin(x['minq']) == b for x in s)/m:.1f}% of these)")
    f = lambda k: 100 * sum(bool(x[k]) for x in s) / m
    print(f"   proper pair: {f('proper'):.1f}%   supplementary alignment present: {f('supp'):.1f}%   different chromosomes: {f('chrom'):.1f}%   same chrom but |TLEN|>1000: {f('far'):.1f}%   wrong orientation (same strand or outward): {f('wrong'):.1f}%")
    print(f"   soft-clipped bases per mate: median {st.median([x['c1'] for x in s] + [x['c2'] for x in s])}; pairs with >=10 clipped on either mate: {100*sum(max(x['c1'], x['c2']) >= 10 for x in s)/m:.1f}%")
    print(f"   NM per mate: median {st.median([x['nm1'] for x in s] + [x['nm2'] for x in s])}")
print("\n3. headline (% of all pairs):")
for gate in ("mb MAPQ>=30 & proper", "mb MAPQ==60 & proper", "mb NOT (MAPQ>=30 & proper)"):
    tot = sum(head[(gate, c)] for c in ("unique", "mapped unknown", "unmapped"))
    print(f"   {gate}: {tot:,} ({pct(tot)}): ours unique {head[(gate,'unique')]:,} ({pct(head[(gate,'unique')])}), mapped unknown {head[(gate,'mapped unknown')]:,} ({pct(head[(gate,'mapped unknown')])}), unmapped {head[(gate,'unmapped')]:,} ({pct(head[(gate,'unmapped')])})")
g = "mb NOT (MAPQ>=30 & proper)"; tot = sum(head[(g, c)] for c in ("unique", "mapped unknown", "unmapped"))
print(f"   reverse: of the {tot:,} pairs where minibwa has MAPQ<30, not proper or is unmapped, we map {head[(g,'unique')]+head[(g,'mapped unknown')]:,} ({100*(head[(g,'unique')]+head[(g,'mapped unknown')])/tot:.1f}%), of which unique {head[(g,'unique')]:,}")
