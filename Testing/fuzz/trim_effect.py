#!/usr/bin/env python3
"""Effect of quality trimming on placement: the same shim built with and without trimming (Spec.trimRecord = identity).
   python3 -I trim_effect.py SET trim.sam notrim.sam R1.fq R2.fq genome.fa > report.md
Pairs are matched by name. unique = XU:Z:unique; mapped = both mates mapped and not an all-insertion (degenerate) mate."""
import re, sys, collections
name, tp, np_, fq1, fq2, fa = sys.argv[1:7]
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
RC = str.maketrans('ACGTNacgtn', 'TGCANtgcan'); rc = lambda s: s.translate(RC)[::-1]

def load(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        ops = [(int(n), o) for n, o in OPS.findall(r[5])] if r[5] != '*' else []
        tags = {t[:2]: t[5:] for t in r[11:]}
        d[(r[0], 1 if f & 64 else 2)] = dict(mapped=not f & 4, chr=r[2], pos=int(r[3]), strand='-' if f & 16 else '+', seq=r[9], ops=ops, tags=tags,
            reflen=sum(n for n, o in ops if o in 'MDN=X'), lead=ops[0][0] if ops and ops[0][1] in 'SH' else 0,
            degenerate=bool(ops) and all(o == 'I' for _, o in ops), AS=int(tags['AS']) if 'AS' in tags else None, line=l.rstrip('\n'))
    return d
T, N = load(tp), load(np_)
assert T.keys() == N.keys()
pairs = sorted({k[0] for k in T}); P = len(pairs)
pm = lambda d, q: [d[(q, 1)], d[(q, 2)]]
mapped = lambda d, q: all(x['mapped'] and not x['degenerate'] for x in pm(d, q))
anymapped = lambda d, q: all(x['mapped'] for x in pm(d, q))
uniq = lambda d, q: anymapped(d, q) and all(x['tags'].get('XU') == 'unique' for x in pm(d, q))
score = lambda d, q: sum(x['AS'] for x in pm(d, q))
def sameplace(q):
    return all((a['chr'], a['strand']) == (b['chr'], b['strand']) and a['pos'] < b['pos'] + b['reflen'] + a['lead'] + 300 and b['pos'] < a['pos'] + a['reflen'] + 300 for a, b in zip(pm(T, q), pm(N, q)))
pct = lambda n, d=P: f'{n} ({100 * n / d:.2f}%)'

print(f'## {name}: {P} pairs, trimming vs no trimming (same shim otherwise)\n')
print('| | trimming | no trimming |\n|---|---|---|')
print(f'| both mates mapped (incl. all-insertion) | {pct(sum(anymapped(T, q) for q in pairs))} | {pct(sum(anymapped(N, q) for q in pairs))} |')
print(f'| mapped, not degenerate | {pct(sum(mapped(T, q) for q in pairs))} | {pct(sum(mapped(N, q) for q in pairs))} |')
print(f'| unique | {pct(sum(uniq(T, q) for q in pairs))} | {pct(sum(uniq(N, q) for q in pairs))} |')
print(f'| unmapped mates (trimmed away entirely, or no result) | {pct(sum(not x["mapped"] for q in pairs for x in pm(T, q)), 2 * P)} of mates | {pct(sum(not x["mapped"] for q in pairs for x in pm(N, q)), 2 * P)} of mates |')
for lo in (-50, -100):
    for lab, f in (('all mapped incl. degenerate', anymapped), ('non-degenerate mapped', mapped)):
        a = [score(T, q) for q in pairs if f(T, q)]; b = [score(N, q) for q in pairs if f(N, q)]
        print(f'| share of {lab} pairs with pair score < {lo} | {pct(sum(s < lo for s in a), max(len(a), 1))} | {pct(sum(s < lo for s in b), max(len(b), 1))} |')
print('\n(no-trim scores are over the full reads, trimmed scores over the kept bases, so score shares are not like for like.)\n')

both = [q for q in pairs if uniq(T, q) and uniq(N, q)]
same = [q for q in both if sameplace(q)]; diff = [q for q in both if not sameplace(q)]
only_t = [q for q in pairs if uniq(T, q) and not uniq(N, q)]; only_n = [q for q in pairs if uniq(N, q) and not uniq(T, q)]
print('### Unique pairs\n\n| class | pairs |\n|---|---|')
print(f'| unique in both builds, same place | {pct(len(same))} |\n| unique in both builds, different place | {pct(len(diff))} |')
print(f'| unique only with trimming | {pct(len(only_t))} |\n| unique only without trimming | {pct(len(only_n))} |')
ot = collections.Counter(('unmapped/degenerate' if not mapped(N, q) else N[(q, 1)]['tags'].get('XU')) for q in only_t)
on = collections.Counter(('unmapped/degenerate' if not mapped(T, q) else T[(q, 1)]['tags'].get('XU')) for q in only_n)
print(f'\nOnly with trimming: the no-trim build says {dict(ot)}. Only without trimming: the trim build says {dict(on)}.')
otx = collections.Counter(N[(q, 1)]['tags'].get('XT', '').strip() for q in only_t); onx = collections.Counter(T[(q, 1)]['tags'].get('XT', '').strip() for q in only_n)
print(f'No-trim tier for "only with trimming": {dict(otx)}; trim tier for "only without trimming": {dict(onx)}.')

# ---- different place: rescore on the FULL read at both places -----------------------------------------------------------
def fastq(p):
    d = {}; it = iter(open(p))
    for h in it: d[h[1:].split()[0].split('/')[0]] = next(it).strip(); next(it); next(it)
    return d
fq = {1: fastq(fq1), 2: fastq(fq2)}
need = {x['chr'] for q in diff for d in (T, N) for x in pm(d, q)}
genome, cur = {}, None
for l in open(fa):
    if l[0] == '>': cur = l[1:].split()[0]; genome[cur] = [] if cur in need else None
    elif genome[cur] is not None: genome[cur].append(l.strip().upper())
genome = {k: ''.join(v) for k, v in genome.items() if v is not None}

def align(read, ref):
    NEG = -10**9; n, m = len(read), len(ref)
    H = [[NEG] * (m + 1) for _ in range(n + 1)]; I = [[NEG] * (m + 1) for _ in range(n + 1)]; D = [[NEG] * (m + 1) for _ in range(n + 1)]
    H[0] = [0] * (m + 1)
    for i in range(1, n + 1):
        for j in range(m + 1):
            best = NEG
            if j > 0:
                best = H[i - 1][j - 1] + (0 if read[i - 1] == ref[j - 1] and read[i - 1] != 'N' else -4)
                D[i][j] = max(H[i][j - 1] - 8, D[i][j - 1] - 2); best = max(best, D[i][j])
            I[i][j] = max(H[i - 1][j] - 8, I[i - 1][j] - 2); H[i][j] = max(best, I[i][j])
    return max(H[n])

def full_score(q, i, rec, off):
    """full original read aligned end to end near rec (rec's SEQ starts `off` bases into the read, alignment orientation)."""
    full = fq[i][q]; seq = full if rec['strand'] == '+' else rc(full)
    diag = rec['pos'] - 1 - rec['lead'] - off
    slack = 10 + sum(n for n, o in rec['ops'] if o in 'ID') + 20
    lo = max(0, diag - slack); hi = min(len(genome[rec['chr']]), diag + len(seq) + slack)
    return align(seq, genome[rec['chr']][lo:hi])
def offset(q, i, rec):
    full = fq[i][q]; o = full if rec['strand'] == '+' else rc(full)
    s0 = o.find(rec['seq']); assert s0 >= 0; return s0
print(f'\n### Unique in both builds, different place: {len(diff)} pairs (FULL-read score at each build\'s placement, both mates summed; end to end, 0/-4/-(6+2k))\n')
verdict = collections.Counter()
for q in diff:
    tot = {}
    for lab, d in (('trim', T), ('notrim', N)):
        tot[lab] = 0
        for i in (1, 2):
            tot[lab] += full_score(q, i, d[(q, i)], offset(q, i, d[(q, i)]))
    # score of each placement on the full read: trim placement vs no-trim placement
    v = 'trim placement better' if tot['trim'] > tot['notrim'] else 'no-trim placement better' if tot['notrim'] > tot['trim'] else 'tie'
    verdict[v] += 1
    print(f'- `{q}`: trim build {[(x["chr"], x["strand"], x["pos"], x["line"].split(chr(9))[5]) for x in pm(T, q)]} full-read score {tot["trim"]}; '
          f'no-trim build {[(x["chr"], x["strand"], x["pos"], x["line"].split(chr(9))[5]) for x in pm(N, q)]} full-read score {tot["notrim"]}; **{v}**')
print(f'\nVerdicts: {dict(verdict)}')

# ---- placement agreement beyond "unique in both" --------------------------------------------------------------------------
for lab, qs, other in (('unique only with trimming', only_t, N), ('unique only without trimming', only_n, T)):
    mp = [q for q in qs if mapped(other, q)]
    ok = sum(sameplace(q) for q in mp)
    print(f'\n{lab}: {len(qs)} pairs; the other build maps {len(mp)} of them (non-degenerate), same place for {ok}, different place for {len(mp) - ok}.')
