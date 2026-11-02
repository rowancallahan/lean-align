#!/usr/bin/env python3
"""Per-mate comparison of our SAM vs minibwa's on the unique-genome pairs.   compare_unique.py ours.sam mb.sam
Compares chromosome, POS, strand, CIGAR, proper-pair flag, TLEN (plus FLAG, RNEXT, PNEXT, MAPQ, SEQ), checks
ours says XU:Z:unique, and checks both against the truth in the read name. Prints every difference."""
import sys, collections
def load(path):
    recs, extra = {}, collections.Counter()
    for line in open(path):
        if line[0] == "@": continue
        f = line.rstrip("\n").split("\t"); flag = int(f[1])
        if flag & 0x900: extra[flag & 0x900] += 1; continue
        key = (f[0], 1 if flag & 0x40 else 2)
        assert key not in recs, key
        recs[key] = dict(flag=flag, chrom=f[2], pos=int(f[3]), mapq=int(f[4]), cigar=f[5], rnext=f[6],
                         pnext=int(f[7]), tlen=int(f[8]), seq=f[9], strand="-" if flag & 16 else "+",
                         proper=bool(flag & 2), tags=dict((t[:2], t[5:]) for t in f[11:]))
    return recs, extra
ours, ox = load(sys.argv[1]); mb, mx = load(sys.argv[2])
assert set(ours) == set(mb), "different read sets"
def truth(name, mate):
    _, c, s, F, st, _, _ = name.split("_"); s, F = int(s), int(F)
    first = (mate == 1) == (st == "+")          # this mate is the fragment's left end
    return dict(chrom=c, pos=s + 1 if first else s + F - 149, strand="+" if first else "-", cigar="150M",
                proper=True, tlen=F if first else -F)
FIELDS = ["chrom", "pos", "strand", "cigar", "proper", "tlen"]
EXTRA = ["flag", "rnext", "pnext", "mapq", "seq"]
diff, ext, nonuniq, off = collections.Counter(), collections.Counter(), [], collections.Counter()
examples = collections.defaultdict(list)
for k in sorted(ours):
    a, b, t = ours[k], mb[k], truth(*k)
    if a["tags"].get("XU") != "unique": nonuniq.append(k)
    for x in FIELDS:
        if a[x] != b[x]: diff[x] += 1; examples[x].append((k, a[x], b[x]))
        if a[x] != t[x]: off["ours " + x] += 1
        if b[x] != t[x]: off["minibwa " + x] += 1
    for x in EXTRA:
        if a[x] != b[x]: ext[x] += 1; examples[x].append((k, a[x], b[x]))
n = len(ours)
print(f"mates compared: {n} ({n // 2} pairs); minibwa extra records (secondary/supplementary): {dict(mx)}; ours: {dict(ox)}")
print(f"ours not XU:Z:unique: {len(nonuniq)}", nonuniq[:10])
print("ours XT values:", dict(collections.Counter(r["tags"].get("XT") for r in ours.values())))
print("ours vs minibwa, mates differing per field:", {x: diff[x] for x in FIELDS})
print("other fields differing:", {x: ext[x] for x in EXTRA})
print("vs truth (mates off):", dict(off) or "none")
print("ours FLAGs:", dict(collections.Counter(r["flag"] for r in ours.values())),
      " minibwa FLAGs:", dict(collections.Counter(r["flag"] for r in mb.values())))
print("ours MAPQ:", dict(collections.Counter(r["mapq"] for r in ours.values())),
      " minibwa MAPQ:", dict(collections.Counter(r["mapq"] for r in mb.values())))
print("minibwa NM:", dict(collections.Counter(r["tags"].get("NM") for r in mb.values())))
print("by substitution class (pairs, both mates identical in all 6 fields):")
cls = collections.Counter(); same = collections.Counter()
for (q, m) in ours:
    if m != 1: continue
    c = tuple(q.split("_")[5:7]); cls[c] += 1
    same[c] += all(ours[(q, i)][x] == mb[(q, i)][x] for i in (1, 2) for x in FIELDS)
for c in sorted(cls): print(f"  subs {c}: {same[c]}/{cls[c]}")
for x, ex in examples.items():
    print(f"examples {x}:"); [print("  ", e) for e in ex[:20]]
