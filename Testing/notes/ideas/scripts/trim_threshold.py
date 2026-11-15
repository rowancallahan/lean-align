#!/usr/bin/env python3
"""One row for one trim-threshold build.   python3 -I trim_threshold.py LABEL ours.sam mb.sam
trimmed length = SEQ length of our SAM record (0 when '*': the mate was dropped as shorter than 25);
pair mapped = both mates mapped; proper = both flag 0x2; unique = both XU:Z:unique (ours) / both MAPQ 60 (minibwa);
agree = our unique pair, minibwa maps both mates, same chromosome and mate-1 start within 300 bp (all other cases counted apart)."""
import statistics, sys
label, ours_p, mb_p = sys.argv[1:4]
def load(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        k = (r[0], 1 if f & 64 else 2); assert k not in d, k
        d[k] = (f, r[2], int(r[3]), int(r[4]), 0 if r[9] == '*' else len(r[9]), next((t[5:] for t in r[11:] if t.startswith('XU:Z:')), ''))
    return d
o, m = load(ours_p), load(mb_p)
names = sorted({k[0] for k in o}); assert names == sorted({k[0] for k in m}) and all((n, 1) in o and (n, 2) in o for n in names)
lens = [o[(n, i)][4] for n in names for i in (1, 2)]; kept = [x for x in lens if x]
def pct(a, b): return f'{100 * a / b:.2f}'
def stats(d, uniq):
    P = len(names); mp = pr = un = 0
    for n in names:
        a, b = d[(n, 1)], d[(n, 2)]
        mp += not a[0] & 4 and not b[0] & 4; pr += bool(a[0] & 2 and b[0] & 2); un += uniq(a) and uniq(b)
    return pct(mp, P), pct(pr, P), pct(un, P)
ago = dis = nomb = 0
for n in names:
    a, b = o[(n, 1)], o[(n, 2)]
    if a[5].strip() == 'unique' and b[5].strip() == 'unique':
        x, y = m[(n, 1)], m[(n, 2)]
        if x[0] & 4 or y[0] & 4: nomb += 1
        elif x[1] == a[1] and y[1] == b[1] and abs(x[2] - a[2]) <= 300 and abs(y[2] - b[2]) <= 300: ago += 1
        else: dis += 1
U = ago + dis + nomb
print(f'{label}\tpairs {len(names)}\ttrimmed len mean {statistics.mean(kept):.1f} median {statistics.median(kept)} (kept mates)\t<50 {pct(sum(1 for x in lens if 0 < x < 50), len(lens))} %\tdropped(<25) {pct(sum(1 for x in lens if x == 0), len(lens))} %'
      f'\tours mapped/proper/unique % {" / ".join(stats(o, lambda r: r[5].strip() == "unique"))}\tminibwa mapped/proper/MAPQ60 % {" / ".join(stats(m, lambda r: r[3] == 60))}'
      f'\tours-unique pairs {U}: agree {ago} ({pct(ago, U)} %), different place {dis}, minibwa unmapped {nomb}')
