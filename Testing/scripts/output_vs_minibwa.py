#!/usr/bin/env python3
"""lean-align SAM vs minibwa SAM on the same read pairs (used by output_vs_minibwa.sh).
   python3 -I output_vs_minibwa.py SET OURS.sam MINIBWA.sam    -> markdown on stdout
Pairs are matched by order and QNAME. Percentages are of all pairs in the set.
 (1) mapped / unique / proper / MAPQ>=30 / MAPQ 60, ours vs minibwa (a pair counts by its LOWER mate MAPQ)
 (2) our XU:Z:unique pairs: placement (chrom, pos, strand) and CIGAR equal to minibwa's on both mates; disagreements
     categorised; mason/low names carry the true position, so who is right is counted too
 (4) pairs we place badly (mapped with uniqueness unknown, split by XB; or unmapped): what minibwa does with them
 (3) field-by-field on mates both tools place at the same chrom/pos/strand: FLAG, MAPQ, RNEXT, PNEXT, TLEN, tags."""
import re, sys, collections
name, ours_p, mb_p = sys.argv[1:]
def parse(path, strict2):
    pairs, cur = [], []
    for l in open(path):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        d = dict(qname=r[0], flag=f, chr=r[2], pos=int(r[3]), mapq=int(r[4]), cigar=r[5], rnext=r[6], pnext=int(r[7]),
                 tlen=int(r[8]), tags={t[:2]: t[5:] for t in r[11:]}, mate=1 if f & 64 else 2)
        d['rev'] = bool(f & 16); d['mapped'] = not f & 4
        cur.append(d)
        if len(cur) == 2:
            a, b = cur; cur = []
            assert a['qname'] == b['qname'] and {a['mate'], b['mate']} == {1, 2}, (a['qname'], b['qname'])
            pairs.append((a, b) if a['mate'] == 1 else (b, a))
    assert not cur
    return pairs
ours, mb = parse(ours_p, True), parse(mb_p, False)
assert len(ours) == len(mb) and all(o[0]['qname'] == m[0]['qname'] for o, m in zip(ours, mb)), 'pair order differs'
N = len(ours)
pct = lambda n, d=None: f'{n} ({100 * n / (d or N):.2f}%)'
both = lambda p: p[0]['mapped'] and p[1]['mapped']
mq = lambda p: min(p[0]['mapq'], p[1]['mapq'])
proper = lambda p: bool(p[0]['flag'] & 2 and p[1]['flag'] & 2)
uniq = lambda p: p[0]['tags'].get('XU') == 'unique'
print(f'## {name}: {N} pairs\n')
print('### (1) pairs mapped / unique\n')
print('| | ours | minibwa |\n|---|---|---|')
print(f'| both mates mapped | {pct(sum(map(both, ours)))} | {pct(sum(map(both, mb)))} |')
print(f'| proper pair flag (0x2 on both) | {pct(sum(map(proper, ours)))} | {pct(sum(map(proper, mb)))} |')
print(f'| marked unique (XU:Z:unique) | {pct(sum(map(uniq, ours)))} | n/a |')
print(f'| min-mate MAPQ >= 30 | {pct(sum(both(p) and mq(p) >= 30 for p in ours))} | {pct(sum(both(p) and mq(p) >= 30 for p in mb))} |')
print(f'| min-mate MAPQ = 60 | {pct(sum(both(p) and mq(p) == 60 for p in ours))} | {pct(sum(both(p) and mq(p) == 60 for p in mb))} |')
print(f'| mapped, uniqueness unknown (MAPQ 0 ours) | {pct(sum(both(p) and not uniq(p) for p in ours))} | n/a |')
print(f'| unmapped pair (neither mate) | {pct(sum(not p[0]["mapped"] and not p[1]["mapped"] for p in ours))} | {pct(sum(not p[0]["mapped"] and not p[1]["mapped"] for p in mb))} |')
mb30 = [i for i, p in enumerate(mb) if both(p) and mq(p) >= 30]
print(f'\nOf minibwa\'s {len(mb30)} pairs with MAPQ >= 30: we map {pct(sum(both(ours[i]) for i in mb30), len(mb30))}, mark unique {pct(sum(uniq(ours[i]) for i in mb30), len(mb30))}.')
print(f'Of our {sum(map(uniq, ours))} unique pairs: minibwa MAPQ >= 30 for {pct(sum(both(mb[i]) and mq(mb[i]) >= 30 for i, p in enumerate(ours) if uniq(p)), sum(map(uniq, ours)))}; minibwa MAPQ < 30 or unmapped for the rest.\n')

def truth(qn):
    m = re.match(r's\d+:([^:]+):(\d+)-\d+([+-]):(\d+)-\d+([+-])', qn)
    return None if not m else {1: (m[1], int(m[2]) + 1, m[3] == '-'), 2: (m[1], int(m[4]) + 1, m[5] == '-')}
def clip(c):
    m = re.match(r'(?:(\d+)[SH])?', c); l = int(m[1]) if m[1] else 0
    m = re.search(r'(\d+)[SH]$', c); return l, int(m[1]) if m else 0
cat, cat_truth = collections.Counter(), collections.defaultdict(collections.Counter)
same_pl = same_cig = 0
mate_n = collections.Counter()   # field mismatches on same-placement mates
tagsets = [collections.Counter(), collections.Counter()]
examples = collections.defaultdict(list)
U = [i for i, p in enumerate(ours) if uniq(p)]
for i in U:
    o, m = ours[i], mb[i]; t = truth(o[0]['qname'])
    for a, b in zip(o, m):
        tagsets[0].update(a['tags'].keys()); tagsets[1].update(b['tags'].keys())
    if not both(m): c = 'minibwa: a mate unmapped'
    else:
        d = [(a['chr'] == b['chr'], a['rev'] == b['rev'], abs(a['pos'] - b['pos'])) for a, b in zip(o, m)]
        if not all(x[0] for x in d): c = 'different locus (other chromosome)'
        elif not all(x[1] for x in d): c = 'different strand'
        elif max(x[2] for x in d) > 50: c = 'different locus (> 50 bp apart)'
        elif max(x[2] for x in d) == 0:
            c = 'same placement, same CIGAR' if all(a['cigar'] == b['cigar'] for a, b in zip(o, m)) else 'same placement, CIGAR differs'
        elif max(x[2] for x in d) <= 2 and not any(sum(clip(b['cigar'])) for b in m): c = 'off by 1-2 bases (no clipping)'
        elif any(sum(clip(b['cigar'])) for b in m): c = 'minibwa clips an end (S/H); ours end-to-end'
        else: c = 'near (3-50 bp), no clipping'
    cat[c] += 1
    if len(examples[c]) < 3 and not c.startswith('same placement, same'): examples[c].append(i)
    if t and both(m):
        ok = lambda p: all((a['chr'], a['pos'], a['rev']) == t[a['mate']] for a in p)
        cat_truth[c][('ours at truth' if ok(o) else 'ours off truth', 'minibwa at truth' if ok(m) else 'minibwa off truth')] += 1
    if both(m):
        for a, b in zip(o, m):
            if (a['chr'], a['pos'], a['rev']) == (b['chr'], b['pos'], b['rev']):
                same_pl += 1
                same_cig += a['cigar'] == b['cigar']
                for f in ('flag', 'mapq', 'rnext', 'pnext', 'tlen'):
                    mate_n[f] += a[f] != b[f]
                mate_n['mates'] += 1
print('### (2) our unique pairs vs minibwa\n')
nu = len(U)
print('| category (both mates) | pairs | % of our unique |\n|---|---|---|')
for c, n in sorted(cat.items(), key=lambda x: -x[1]):
    print(f'| {c} | {n} | {100 * n / max(nu, 1):.2f}% |')
eq = cat['same placement, same CIGAR']
print(f'\nIdentical placement AND CIGAR on both mates: {pct(eq, nu)} of our unique pairs; identical placement (any CIGAR): {pct(eq + cat["same placement, CIGAR differs"], nu)}.\n')
if cat_truth:
    print('Against the true position in the read name (simulated sets), pairs where minibwa maps both mates:\n')
    print('| category | ours at truth, minibwa at truth | ours at truth, minibwa off | ours off, minibwa at truth | both off |\n|---|---|---|---|---|')
    for c, cn in sorted(cat_truth.items(), key=lambda x: -sum(x[1].values())):
        g = lambda a, b: cn[(a, b)]
        print(f'| {c} | {g("ours at truth", "minibwa at truth")} | {g("ours at truth", "minibwa off truth")} | {g("ours off truth", "minibwa at truth")} | {g("ours off truth", "minibwa off truth")} |')
    print()
print('Examples (pair index; ours / minibwa CHR:POS STRAND CIGAR, mate 1 | mate 2):\n')
for c, idx in examples.items():
    for i in idx:
        f = lambda p: ' | '.join(f"{a['chr']}:{a['pos']}{'-' if a['rev'] else '+'} {a['cigar']}" for a in p)
        print(f'- {c}: #{i} {ours[i][0]["qname"][:40]}: ours {f(ours[i])} / minibwa {f(mb[i])}')
print('\n### (3) fields on mates placed identically by both tools\n')
print(f'{mate_n["mates"]} mates (from our unique pairs); mismatching fields (ours vs minibwa):\n')
print('| field | mismatches |\n|---|---|')
for f in ('flag', 'mapq', 'rnext', 'pnext', 'tlen'):
    print(f'| {f.upper()} | {mate_n[f]} |')
print(f'| CIGAR | {mate_n["mates"] - same_cig} |')
fl = lambda ps, which: collections.Counter(p[which]['flag'] for p in ps)
print(f'\nFLAG values, all pairs, mate 1: ours {dict(fl(ours, 0))}, minibwa {dict(fl(mb, 0))}')
print(f'MAPQ values on ours (mapped mates): {dict(sorted(collections.Counter(a["mapq"] for p in ours for a in p if a["mapped"]).items()))}')
print(f'MAPQ values on minibwa (mapped mates, top 8): {dict(collections.Counter(a["mapq"] for p in mb for a in p if a["mapped"]).most_common(8))}')
print(f'Tags on our unique pairs: {dict(tagsets[0])}; minibwa on the same pairs: {dict(tagsets[1])}')

print('\n### (4) pairs we place badly: what minibwa does with the same reads\n')
xb0 = lambda p: p[0]['tags'].get('XB') == '0'
groups = [('mapped by us, uniqueness unknown, XB:i:0 (fallback/last resort)', [i for i, p in enumerate(ours) if both(p) and not uniq(p) and xb0(p)]),
          ('mapped by us, uniqueness unknown, XB < 0', [i for i, p in enumerate(ours) if both(p) and not uniq(p) and not xb0(p)]),
          ('unmapped by us, XB:i:0', [i for i, p in enumerate(ours) if not both(p) and xb0(p)]),
          ('unmapped by us, XB < 0', [i for i, p in enumerate(ours) if not both(p) and not xb0(p)])]
print('| our pairs | n | minibwa maps both mates | minibwa proper | min-mate MAPQ 0 | 1-9 | 10-29 | 30-59 | 60 | XA on a mate | SA on a mate | same placement as ours (both mates) |\n|---|---|---|---|---|---|---|---|---|---|---|---|')
for gname, idx in groups:
    n = len(idx)
    if n == 0:
        print(f'| {gname} | 0 | | | | | | | | | | |'); continue
    ms = [mb[i] for i in idx]; mapped = [p for p in ms if both(p)]
    b = lambda lo, hi: sum(lo <= mq(p) <= hi for p in mapped)
    xa = sum(any('XA' in a['tags'] for a in p) for p in ms); sa = sum(any('SA' in a['tags'] for a in p) for p in ms)
    same = sum(both(ours[i]) and both(mb[i]) and all((a['chr'], a['pos'], a['rev']) == (c['chr'], c['pos'], c['rev']) for a, c in zip(ours[i], mb[i])) for i in idx)
    print(f'| {gname} | {n} | {pct(len(mapped), n)} | {pct(sum(map(proper, ms)), n)} | {pct(b(0, 0), n)} | {pct(b(1, 9), n)} | {pct(b(10, 29), n)} | {pct(b(30, 59), n)} | {pct(b(60, 60), n)} | {pct(xa, n)} | {pct(sa, n)} | {pct(same, n)} |')
print('\n(Percentages in this table are of the group. Pairs with only one mate mapped by minibwa are in no MAPQ column.)')
