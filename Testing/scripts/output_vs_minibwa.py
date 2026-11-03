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
nom = lambda a: a['mapped'] and not re.search(r'\d+[M=X]', a['cigar'])   # alignment without any aligned base (placeholder)
placeholder = lambda p: nom(p[0]) or nom(p[1])
proper = lambda p: bool(p[0]['flag'] & 2 and p[1]['flag'] & 2)
uniq = lambda p: p[0]['tags'].get('XU') == 'unique'
print(f'## {name}: {N} pairs\n')
print('### (1) pairs mapped / unique\n')
print('| | ours | minibwa |\n|---|---|---|')
print(f'| both mates mapped | {pct(sum(map(both, ours)))} | {pct(sum(map(both, mb)))} |')
print(f'| proper pair flag (0x2 on both) | {pct(sum(map(proper, ours)))} | {pct(sum(map(proper, mb)))} |')
print(f'| of which a placeholder alignment (CIGAR without M, e.g. 150I at chr1:1) | {pct(sum(map(placeholder, ours)))} | {pct(sum(map(placeholder, mb)))} |')
print(f'| both mates mapped with an aligned base | {pct(sum(both(p) and not placeholder(p) for p in ours))} | {pct(sum(both(p) and not placeholder(p) for p in mb))} |')
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
def refspan(c):   # reference bases covered by a CIGAR (soft clips and insertions excluded)
    return sum(int(n) for n, o in re.findall(r'(\d+)([MIDNSHP=X])', c) if o in 'MDN=X')
REL = ['identical (position and CIGAR)', 'same reference interval, CIGAR differs', 'ours inside minibwa\'s interval (we trim/clip more)',
       'minibwa inside ours (minibwa clips more)', 'shifted overlap (>= 50 % of the shorter)', 'overlap < 50 %', 'different chromosome/strand or disjoint']
def rel(a, b):    # relation of one of our mates to minibwa's mate (aligned reference intervals; clipped/trimmed ends excluded)
    if a['chr'] != b['chr'] or a['rev'] != b['rev']: return 6
    la, lb = refspan(a['cigar']), refspan(b['cigar']); sa, sb = a['pos'], b['pos']; ea, eb = sa + la, sb + lb
    if (sa, la) == (sb, lb): return 0 if a['cigar'] == b['cigar'] else 1
    if sb <= sa and ea <= eb: return 2
    if sa <= sb and eb <= ea: return 3
    ov = min(ea, eb) - max(sa, sb)
    if ov <= 0: return 6
    return 4 if ov * 2 >= min(la, lb) else 5
def span_overlap(a, tr):   # fraction of our aligned interval inside the true interval (from the read name)
    la = refspan(a['cigar']); t = tr[a['mate']]
    return 0 if (a['chr'], a['rev']) != (t[0], t[2]) else max(0, min(a['pos'] + la, t[1] + 150 + 1000) - max(a['pos'], t[1])) / max(la, 1)
cat, cat_truth = collections.Counter(), collections.defaultdict(collections.Counter)
same_pl = same_cig = 0
mate_n = collections.Counter()   # field mismatches on same-placement mates
tagsets = [collections.Counter(), collections.Counter()]
examples = collections.defaultdict(list)
U = [i for i, p in enumerate(ours) if uniq(p)]
def truth_iv(qn):   # true reference interval of each mate (chrom, start 1-based, strand-is-reverse, end) from the read name
    m = re.match(r's\d+:([^:]+):(\d+)-(\d+)([+-]):(\d+)-(\d+)([+-])', qn)
    return None if not m else {1: (m[1], int(m[2]) + 1, m[4] == '-', int(m[3])), 2: (m[1], int(m[5]) + 1, m[7] == '-', int(m[6]))}
def at_truth(a, t):   # our/minibwa aligned interval inside the true interval (+-10) on the true strand
    x = t[a['mate']]
    return (a['chr'], a['rev']) == (x[0], x[2]) and a['pos'] >= x[1] - 10 and a['pos'] + refspan(a['cigar']) - 1 <= x[3] + 10
for i in U:
    o, m = ours[i], mb[i]; t = truth_iv(o[0]['qname'])
    for a, b in zip(o, m):
        tagsets[0].update(a['tags'].keys()); tagsets[1].update(b['tags'].keys())
    if not both(m): c = 'minibwa: a mate unmapped'
    else: c = REL[max(rel(a, b) for a, b in zip(o, m))]
    cat[c] += 1
    if len(examples[c]) < 3 and not c.startswith('identical'): examples[c].append(i)
    if t and both(m):
        cat_truth[c][('ours at truth' if all(at_truth(a, t) for a in o) else 'ours off truth', 'minibwa at truth' if all(at_truth(b, t) for b in m) else 'minibwa off truth')] += 1
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
same_locus = sum(cat[REL[k]] for k in range(5))
print(f'\nSame strand and overlapping aligned interval on both mates: {pct(same_locus, nu)} of our unique pairs; identical position and CIGAR: {pct(cat[REL[0]], nu)}.\n')
if cat_truth:
    print('Against the true position in the read name (simulated sets), pairs where minibwa maps both mates:\n')
    print('| category | ours at truth, minibwa at truth | ours at truth, minibwa off | ours off, minibwa at truth | both off |\n|---|---|---|---|---|')   # at truth = aligned interval inside the true one (+-10)
    for c, cn in sorted(cat_truth.items(), key=lambda x: -sum(x[1].values())):
        g = lambda a, b: cn[(a, b)]
        print(f'| {c} | {g("ours at truth", "minibwa at truth")} | {g("ours at truth", "minibwa off truth")} | {g("ours off truth", "minibwa at truth")} | {g("ours off truth", "minibwa off truth")} |')
    print()
bu = [i for i in U if both(mb[i]) and mq(mb[i]) >= 30]
if bu:
    k = lambda c: sum(max(rel(a, b) for a, b in zip(ours[i], mb[i])) == c for i in bu)
    print(f'Pairs both tools call unique (ours XU:Z:unique and minibwa MAPQ >= 30 on both mates): {len(bu)}. Identical position and CIGAR: {pct(k(0), len(bu))}; same strand and overlapping aligned interval: {pct(sum(k(c) for c in range(5)), len(bu))}; ours inside minibwa\'s interval: {pct(k(2), len(bu))}; minibwa inside ours: {pct(k(3), len(bu))}; different locus or disjoint: {pct(k(6) + k(5), len(bu))}.\n')
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
groups = [('placeholder pair (CIGAR without M), any XB', [i for i, p in enumerate(ours) if placeholder(p)]),
          ('mapped by us, real alignment, uniqueness unknown, XB:i:0', [i for i, p in enumerate(ours) if both(p) and not placeholder(p) and not uniq(p) and xb0(p)]),
          ('mapped by us, real alignment, uniqueness unknown, XB < 0', [i for i, p in enumerate(ours) if both(p) and not placeholder(p) and not uniq(p) and not xb0(p)]),
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
