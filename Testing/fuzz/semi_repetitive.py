#!/usr/bin/env python3
"""Pairs that reach the expensive complete search without being highly repetitive (real reads).
   python3 -I semi_repetitive.py SET ours.sam mb.sam trace.err [N_EXAMPLES=12] > report.md
trace.err = stderr of a LOCAL debug build (gaveUpRepeats=200, gaveUpSeeds=2, one `SEMI` line per pair that reaches `lookAtG`:
SEMI <read1> <read2> <seed counts mate1> <seed counts mate2> <|hits mate1| within the cap> <|hits mate2 near them|> <req>,
reads are letters shifted by 33). Pairs are matched to the SAM by their trimmed letters (revcomp for reverse-strand records)."""
import re, sys, collections
name, ours_p, mb_p, tr_p = sys.argv[1:5]; NEX = int(sys.argv[5]) if len(sys.argv) > 5 else 12
RC = str.maketrans('ACGTN', 'TGCAN'); rc = lambda s: s.translate(RC)[::-1]
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
def parse(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        ops = [(int(n), o) for n, o in OPS.findall(r[5])] if r[5] != '*' else []
        seq = r[9] if r[9] != '*' else ''
        d[(r[0], 1 if f & 64 else 2)] = dict(chr=r[2], pos=int(r[3]), strand='-' if f & 16 else '+', mapq=int(r[4]), cigar=r[5], seq=seq,
            read=(rc(seq) if f & 16 else seq), tags={t[:2]: t[5:] for t in r[11:]}, mapped=not f & 4, flag=f,
            deg=bool(ops) and all(o == 'I' for _, o in ops), reflen=sum(n for n, o in ops if o in 'MDN=X'))
    return d
ours, mb = parse(ours_p), parse(mb_p)
bykey = {}
for (q, m), r in ours.items():
    if m == 1: bykey[(r['read'], ours[(q, 2)]['read'])] = q
dec = lambda s: ''.join(chr(ord(c) - 33) for c in s)
rows, seen = [], set()
for l in open(tr_p):
    if not l.startswith('SEMI'): continue
    f = l.rstrip('\n').split('\t')
    r1, r2 = dec(f[1]), dec(f[2])
    if (r1, r2) in seen: continue
    seen.add((r1, r2))
    q = bykey.get((r1, r2))
    assert q is not None, 'trace pair not found in SAM'
    c1 = [int(x) for x in f[3].split(',') if x != '']; c2 = [int(x) for x in f[4].split(',') if x != '']
    rows.append(dict(q=q, r1=r1, r2=r2, c1=c1, c2=c2, hx=int(f[5]), hy=int(f[6]), req=int(f[7])))
N = len(rows)
pct = lambda n, d=None: f'{n} ({100 * n / (d or N):.1f}%)'
print(f'## {name}: {N} pairs reach the complete search and are not highly repetitive (fewer than 2 grid seeds at >= 200 occurrences in either mate)\n')

def pair_ours(q):
    a, b = ours[(q, 1)], ours[(q, 2)]
    return a, b
def outcome(q):
    a, b = pair_ours(q)
    t = a['tags']; xu, xt = t.get('XU'), t.get('XT', '').strip()
    if a['mapped'] and b['mapped'] and not a['deg'] and not b['deg']:
        sc = int(t['AS']) + int(b['tags']['AS'])
        return 'pair found >= -100' if sc >= -100 else 'pair found < -100'
    if a['deg'] or b['deg']: return 'last-resort all-insertion pair'
    if xu == 'gaveUp': return 'gave up (places rule), unmapped'
    return f'unmapped: {xt} (bound below the floor = proved none)' if xt == 'boundsOnly' else f'unmapped: {xt or xu}'
for r in rows:
    r['out'] = outcome(r['q']); r['xu'] = ours[(r['q'], 1)]['tags'].get('XU'); r['xt'] = ours[(r['q'], 1)]['tags'].get('XT', '').strip()
    r['mx1'], r['mx2'] = max(r['c1'] or [0]), max(r['c2'] or [0])
    r['n200_1'] = sum(c >= 200 for c in r['c1']); r['n200_2'] = sum(c >= 200 for c in r['c2'])
    r['len1'], r['len2'] = len(r['r1']), len(r['r2'])
    m1, m2 = mb[(r['q'], 1)], mb[(r['q'], 2)]
    r['mbmapq'] = min(m1['mapq'], m2['mapq']) if m1['mapped'] and m2['mapped'] else None
    o1, o2 = pair_ours(r['q'])
    near = lambda a, b: a['mapped'] and b['mapped'] and (a['chr'], a['strand']) == (b['chr'], b['strand']) and abs(a['pos'] - b['pos']) <= 400
    r['same'] = near(o1, m1) and near(o2, m2)
    r['mbxa'] = 'XA' in m1['tags'] or 'XA' in m2['tags']

def hist(vals, edges):
    c = collections.Counter()
    for v in vals:
        for lo, hi in zip(edges, edges[1:] + [10**9]):
            if lo <= v < hi: c[(lo, hi)] += 1; break
    return ', '.join(f'{lo}-{hi - 1 if hi < 10**9 else "+"}: {c[(lo, hi)]}' for lo, hi in zip(edges, edges[1:] + [10**9]))
print('### Outcome of the pair\n')
for k, v in collections.Counter(r['out'] for r in rows).most_common(): print(f'- {k}: {pct(v)}')
print('\nOur label (XU): ' + ', '.join(f'{k}: {v}' for k, v in collections.Counter(r['xu'] for r in rows).most_common()) +
      '; tier (XT): ' + ', '.join(f'{k}: {v}' for k, v in collections.Counter(r['xt'] for r in rows).most_common(5)))
print('\n### Max seed occurrence count per mate (over the 25-mer grid seeds, genome both strands)\n')
mx = [m for r in rows for m in (r['mx1'], r['mx2'])]
print(hist(mx, [0, 1, 2, 5, 10, 20, 50, 100, 150, 200]))
print('\n### Grid seeds at >= 200 per mate (0 or 1 by selection)\n')
n2 = [n for r in rows for n in (r['n200_1'], r['n200_2'])]
print(', '.join(f'{k} seed(s): {v}' for k, v in sorted(collections.Counter(n2).items())))
print('\n### Mate length after trimming\n')
print(hist([r[k] for r in rows for k in ('len1', 'len2')], [0, 50, 100, 140, 151, 200, 250]))
print('\n### Candidate places within the error cap (hits of mate 1; then mate 2 hits near them)\n')
print('mate 1: ' + hist([r['hx'] for r in rows], [0, 1, 2, 5, 10, 20, 50]))
print('mate 2 near mate 1: ' + hist([r['hy'] for r in rows], [0, 1, 2, 5, 10, 20, 50]))
print('\n### minibwa on the same pairs\n')
mm = collections.Counter('unmapped/one mate' if r['mbmapq'] is None else 'MAPQ 0' if r['mbmapq'] == 0 else 'MAPQ 1-29' if r['mbmapq'] < 30 else 'MAPQ 30-59' if r['mbmapq'] < 60 else 'MAPQ 60' for r in rows)
print(', '.join(f'{k}: {pct(v)}' for k, v in mm.most_common()))
print(f'\nminibwa places the pair within 400 bp of ours (both mates): {pct(sum(r["same"] for r in rows))}; minibwa has XA: {pct(sum(r["mbxa"] for r in rows))}')
print('\nOutcome x minibwa MAPQ:\n\n| our outcome | pairs | minibwa MAPQ >= 30 | same place | minibwa MAPQ 0 |\n|---|---|---|---|---|')
for o in sorted({r['out'] for r in rows}):
    rr = [r for r in rows if r['out'] == o]
    print(f'| {o} | {len(rr)} | {sum((r["mbmapq"] or 0) >= 30 for r in rr)} | {sum(r["same"] for r in rr)} | {sum(r["mbmapq"] == 0 for r in rr)} |')

# ---- examples: ASCII drawings, spread over (max count, outcome) ------------------------------------------------------------
def draw(r):
    m1, m2 = mb[(r['q'], 1)], mb[(r['q'], 2)]; o1, o2 = pair_ours(r['q'])
    def bar(cs, L):
        return ''.join(f'[s{i}:{c}]' for i, c in enumerate(cs))
    out = [f'### `{r["q"]}`', '```',
           f'mate1 {r["len1"]:>3} bp {bar(r["c1"], r["len1"])}   (occurrences per 25-mer grid seed)',
           f'mate2 {r["len2"]:>3} bp {bar(r["c2"], r["len2"])}',
           f'complete search: {r["hx"]} candidate places for mate 1 within the cap, {r["hy"]} for mate 2 near them',
           f'ours:    {o1["chr"]}:{o1["pos"]}{o1["strand"]} {o1["cigar"]} / {o2["chr"]}:{o2["pos"]}{o2["strand"]} {o2["cigar"]}  AS {o1["tags"].get("AS")}+{o2["tags"].get("AS")}  {r["xu"]} {r["xt"]}',
           f'minibwa: {m1["chr"]}:{m1["pos"]}{m1["strand"]} {m1["cigar"]} / {m2["chr"]}:{m2["pos"]}{m2["strand"]} {m2["cigar"]}  MAPQ {m1["mapq"]}/{m2["mapq"]}{"  XA" if r["mbxa"] else ""}',
           '```']
    why = []
    hi = max(r['c1'] + r['c2'] + [0])
    if hi >= 20:
        which = ('mate 1' if r['mx1'] >= r['mx2'] else 'mate 2')
        why.append(f'the busiest seed of {which} hits {hi} places and each hit needs a banded check')
    if r['hx'] >= 10: why.append(f'{r["hx"]} candidate places for mate 1 inside the cap')
    if not why: why.append('no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate)' if r['hx'] < 10 else '')
    out.append('Why expensive: ' + '; '.join(w for w in why if w) + '.')
    return '\n'.join(out)
semi = [r for r in rows if max(r['mx1'], r['mx2']) >= 20]
print(f'\n### The semi-repetitive subset (max seed occurrence >= 20 in some mate): {pct(len(semi))}\n')
for k, v in collections.Counter(r['out'] for r in semi).most_common(): print(f'- {k}: {pct(v, len(semi))}')
print('\nmax seed occurrence in the subset: ' + hist([max(r['mx1'], r['mx2']) for r in semi], [20, 50, 100, 150, 200]))
print('mate-1 candidate places in the subset: ' + hist([r['hx'] for r in semi], [0, 1, 2, 5, 10, 20, 50]))
print('minibwa MAPQ in the subset: ' + ', '.join(f'{k}: {v}' for k, v in collections.Counter('unmapped/one mate' if r['mbmapq'] is None else 'MAPQ 0' if r['mbmapq'] == 0 else 'MAPQ 1-29' if r['mbmapq'] < 30 else 'MAPQ 30-59' if r['mbmapq'] < 60 else 'MAPQ 60' for r in semi).most_common()))
picks = []
outs = sorted({r['out'] for r in semi})
per = max(1, (NEX - 3) // max(len(outs), 1))
for o in outs:
    rr = sorted((r for r in semi if r['out'] == o), key=lambda r: (max(r['mx1'], r['mx2']), r['hx']))
    picks += rr[::max(1, len(rr) // per)][:per]
rest = sorted((r for r in rows if max(r['mx1'], r['mx2']) < 20), key=lambda r: (r['hx'], r['len1'] + r['len2']))
picks = picks[:NEX - 3] + rest[::max(1, len(rest) // 3)][:3]
print('\n## Examples (first the semi-repetitive pairs, last three are non-repetitive for contrast)\n')
for r in picks[:NEX]: print(draw(r) + '\n')
