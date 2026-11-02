#!/usr/bin/env python3
"""Real reads (no truth): classify every mate of ours.sam against minibwa.sam. Fails on any surprise (asserts).
   python3 -I real_vs_minibwa.py SET ours.sam mb.sam [N_EXAMPLES=20] > report.md   (examples also in SET.examples.tsv)
Scoring model of ours: match 0, mismatch -4, gap of k: -(6+2k), end to end. minibwa score recomputed in that model from
CIGAR+NM when it has no S/H (mismatches = NM - gap bases; N bases count as mismatches in NM, as in ours)."""
import re, sys, collections
name, ours_p, mb_p = sys.argv[1:4]; NEX = int(sys.argv[4]) if len(sys.argv) > 4 else 20
OPS = re.compile(r'(\d+)([MIDNSHP=X])')

def load(path):
    out = {}
    for l in open(path):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        k = (r[0], 1 if f & 64 else 2); assert k not in out, k
        tags = {t[:2]: t[5:] for t in r[11:]}
        cig = r[5]; ops = [(int(n), o) for n, o in OPS.findall(cig)] if cig != '*' else []
        assert ''.join(f'{n}{o}' for n, o in ops) == (cig if cig != '*' else '')
        lead = ops[0][0] if ops and ops[0][1] in 'SH' else 0
        qlen = sum(n for n, o in ops if o in 'MIS=X')
        d = dict(line=l.rstrip('\n'), flag=f, mapped=not f & 4, chr=r[2], pos=int(r[3]), strand='-' if f & 16 else '+',
                 mapq=int(r[4]), cigar=cig, lead=lead, tags=tags, proper=bool(f & 2), qlen=qlen,
                 clip=any(o in 'SH' for _, o in ops),
                 degenerate=bool(ops) and all(o == 'I' for _, o in ops))  # e.g. 150I: the "no pair" last resort
        d['diag'] = d['pos'] - lead
        gaps = [n for n, o in ops if o in 'ID']
        d['gapbases'] = sum(gaps); d['ngaps'] = len(gaps)
        d['AS'] = int(tags['AS']) if 'AS' in tags and d['mapped'] else None
        d['NM'] = int(tags['NM']) if 'NM' in tags else None
        out[k] = d
    return out

def my_score(m):
    """minibwa alignment scored in OUR model; None when clipped (or no NM)."""
    if not m['mapped'] or m['clip'] or m['NM'] is None: return None
    gaps = [int(n) for n, o in OPS.findall(m['cigar']) if o in 'ID']
    mm = m['NM'] - sum(gaps); assert mm >= 0, m['line']
    return -(4 * mm + sum(6 + 2 * n for n in gaps))

ours, mb = load(ours_p), load(mb_p)
assert ours.keys() == mb.keys(), 'the two files have different reads'
keys = sorted(ours)                      # (qname, mate)
N = len(keys)
pct = lambda n, d=N: f'{n} ({100 * n / d:.2f}%)'

def classify(a, b):
    if a['degenerate']: return 'degenerate (ours all-insertion)'
    if not a['mapped'] and not b['mapped']: return 'unmapped by both'
    if not a['mapped']: return 'mapped by minibwa only'
    if not b['mapped']: return 'mapped by ours only'
    if (a['chr'], a['strand']) == (b['chr'], b['strand']):
        if a['pos'] == b['pos']: return 'same pos+strand, same CIGAR' if a['cigar'] == b['cigar'] else 'same pos+strand, CIGAR differs'
        if a['diag'] == b['diag'] or a['pos'] - a['lead'] == b['pos'] - b['lead']:
            return 'same diagonal (POS shifted by clipping), CIGAR differs'
    if a['mapq'] == 60 and b['mapq'] >= 30: return 'DIFFERENT pos: ours unique (60), minibwa MAPQ>=30  [ALARMING]'
    if a['mapq'] == 0 or b['mapq'] == 0: return 'different pos, repeats (either MAPQ 0)'
    return 'different pos, other'

cls = collections.Counter(); byclass = collections.defaultdict(list)
for k in keys:
    c = classify(ours[k], mb[k]); cls[c] += 1; byclass[c].append(k)

def near(a, b):  # for 'different pos' classes: same chr+strand within 50 bp?
    return (a['chr'], a['strand']) == (b['chr'], b['strand']) and abs(a['pos'] - b['pos']) <= 50

print(f'## {name}: {N // 2} pairs, {N} mates\n')
print('### 1. Per-mate classification (percent of all mates)\n\n| class | mates |\n|---|---|')
for c, n in sorted(cls.items(), key=lambda x: -x[1]): print(f'| {c} | {pct(n)} |')
for c in cls:
    if c.startswith('DIFFERENT') or c.startswith('different'):
        ks = byclass[c]; nn = sum(near(ours[k], mb[k]) for k in ks)
        print(f'\n- {c}: {nn} of {len(ks)} are on the same chromosome+strand within 50 bp (indel/clip/trim shifts); '
              f'minibwa has XA on {sum("XA" in mb[k]["tags"] for k in ks)}; ours XT/XU: ' +
              ', '.join(f'{u}={n}' for u, n in collections.Counter(ours[k]["tags"].get("XU") for k in ks).most_common(4)))

print('\n### 1b. Our degenerate all-insertion mates: what minibwa did\n')
dk = byclass['degenerate (ours all-insertion)']
if dk:
    rows = collections.Counter()
    for k in dk:
        b = mb[k]
        rows['unmapped' if not b['mapped'] else f'mapped, MAPQ {"0" if b["mapq"] == 0 else "1-29" if b["mapq"] < 30 else "30-59" if b["mapq"] < 60 else "60"}'] += 1
    print(f'{len(dk)} mates ({len(dk) // 2}+ pairs). minibwa: ' + ', '.join(f'{c}: {pct(n, len(dk))}' for c, n in sorted(rows.items())))
    print(f'minibwa has XA on {pct(sum("XA" in mb[k]["tags"] for k in dk), len(dk))}; proper flag {pct(sum(mb[k]["proper"] for k in dk), len(dk))}; '
          f'clipped {pct(sum(mb[k]["clip"] for k in dk), len(dk))}.')
else: print('none')

print('\n### 2. Score check: mates at the same place (same pos+strand or same diagonal), minibwa unclipped\n')
same = [k for k in keys if classify(ours[k], mb[k]).startswith('same')]
better = []; tab = collections.Counter()
for k in same:
    a, b = ours[k], mb[k]; s = my_score(b)
    if s is None: tab['minibwa clipped: not comparable'] += 1; continue
    g = 'same query length' if a['qlen'] == b['qlen'] else 'ours trimmed/shorter query'
    assert a['AS'] is not None
    rel = 'minibwa strictly better' if s > a['AS'] else 'equal' if s == a['AS'] else 'ours better'
    tab[(g, rel)] += 1
    if rel == 'minibwa strictly better': better.append((k, s, g))
print(f'{len(same)} mates at the same place.\n\n| group | minibwa strictly better | equal | ours better |\n|---|---|---|---|')
for g in ('same query length', 'ours trimmed/shorter query'):
    t = sum(v for (gg, _), v in tab.items() if gg == g)
    print(f'| {g} ({t}) | ' + ' | '.join(pct(tab[(g, r)], max(t, 1)) for r in ('minibwa strictly better', 'equal', 'ours better')) + ' |')
print(f'\nminibwa clipped, not comparable: {pct(tab["minibwa clipped: not comparable"], len(same))}.')
gain = collections.Counter(s - ours[k]['AS'] for k, s, g in better if g == 'same query length')
print('Gain (minibwa score - ours, same query length) histogram: ' + ', '.join(f'+{d}: {n}' for d, n in sorted(gain.items())[:12]))
print('Note: "ours better" or "minibwa better" with same query length at the same place both indicate scoring/NM-convention issues '
      'if frequent; an optimal end-to-end aligner never loses at the same placement.')

print('\n### 3. Pair score AS1+AS2 where minibwa maps the pair confidently (both mapped, min MAPQ >= 30)\n')
pairs = sorted({k[0] for k in keys})
conf = [];
for q in pairs:
    m1, m2, o1, o2 = mb[(q, 1)], mb[(q, 2)], ours[(q, 1)], ours[(q, 2)]
    if m1['mapped'] and m2['mapped'] and min(m1['mapq'], m2['mapq']) >= 30: conf.append(q)
ps = {}
for q in conf:
    o1, o2 = ours[(q, 1)], ours[(q, 2)]
    if o1['mapped'] and o2['mapped']: ps[q] = o1['AS'] + o2['AS']
print(f'minibwa confident pairs: {len(conf)}; we map both mates of {pct(len(ps), len(conf))}; unmapped by us: {len(conf) - len(ps)}.\n')
print('| our pair score | pairs | of which our pair degenerate | same place as minibwa (both mates) | minibwa unclipped both, its score in our model < -50 |\n|---|---|---|---|---|')
bins = [(-10**9, -100), (-100, -50), (-50, -32), (-32, -16), (-16, 1)]
low = []
for lo, hi in bins:
    qs = [q for q, s in ps.items() if s < hi and (lo == -10**9 or s >= lo)]
    deg = sum(ours[(q, 1)]['degenerate'] or ours[(q, 2)]['degenerate'] for q in qs)
    sp = sum(all(classify(ours[(q, m)], mb[(q, m)]).startswith('same') for m in (1, 2)) for q in qs)
    mbs = [(my_score(mb[(q, 1)]), my_score(mb[(q, 2)])) for q in qs]
    unc = [a + b for a, b in mbs if a is not None and b is not None]
    print(f'| [{"-inf" if lo == -10**9 else lo}, {hi}) | {len(qs)} | {deg} | {sp} | {sum(u < -50 for u in unc)} of {len(unc)} unclipped |')
    if hi <= -50: low += qs
tot = len(ps)
print('\nCumulative over minibwa-confident pairs that we map: ' + ', '.join(f'score < {t}: {pct(sum(s < t for s in ps.values()), max(tot, 1))}' for t in (-16, -32, -50, -100)))
print(f'A floor of -50 would unmap {len(low)} pairs that minibwa maps with MAPQ>=30 (plus the {len(conf) - len(ps)} we already do not map).')
mbsc = [(my_score(mb[(q, 1)]), my_score(mb[(q, 2)])) for q in conf]
unc = [a + b for a, b in mbsc if a is not None and b is not None]
print(f'minibwa\'s own pair score in our model (unclipped on both mates, {pct(len(unc), max(len(conf), 1))} of confident pairs): '
      + ', '.join(f'< {t}: {sum(u < t for u in unc)}' for t in (-16, -32, -50, -100)) + '.')
print('\nExamples of pairs below the floor: see ' + name + '.examples.tsv (section LOW_PAIR).')

# ---- examples (raw records of both tools) ------------------------------------------------------------------
def hint(a, b):
    h = []
    if a['degenerate']: h.append('ours degenerate')
    if b['clip']: h.append(f'minibwa clip ({re.sub(r"[0-9]+M", "M", b["cigar"])})')
    if a['clip']: h.append('ours clip')
    if a['qlen'] != b['qlen']: h.append(f'ours trimmed (qlen {a["qlen"]} vs {b["qlen"]})')
    if 'XA' in b['tags']: h.append('minibwa XA (repeat)')
    if near(a, b): h.append(f'{abs(a["pos"] - b["pos"])} bp apart')
    if a['ngaps'] != b['ngaps']: h.append('gap count differs (indel)')
    return '; '.join(h)

def dump(f, title, picks):
    f.write(f'## {title}\n')
    for k in picks:
        a, b = ours[k], mb[k]
        f.write(f'# {k[0]} mate{k[1]}  hint: {hint(a, b)}\nOURS\t{a["line"]}\nMINIBWA\t{b["line"]}\n')
step = lambda ks: ks[::max(1, len(ks) // NEX)][:NEX]            # evenly spread, deterministic
alarm = byclass.get('DIFFERENT pos: ours unique (60), minibwa MAPQ>=30  [ALARMING]', [])
with open(f'{name}.examples.tsv', 'w') as f:
    dump(f, 'ALARMING', step(alarm))
    dump(f, 'MINIBWA_BETTER', step(sorted(b[0] for b in better if b[2] == 'same query length')))
    dump(f, 'LOW_PAIR', [(q, m) for q in step(sorted(low)) for m in (1, 2)])
