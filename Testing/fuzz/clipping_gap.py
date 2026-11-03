#!/usr/bin/env python3
"""Why do we give `none` (both mates unmapped) where minibwa maps the pair with MAPQ >= 30 on both mates?
   python3 -I clipping_gap.py SET ours.sam mb.sam R1.fq R2.fq [N_EXAMPLES=10] > report.md
Per pair (from minibwa's alignment and the original FASTQ; ours has no alignment, only the trimmed SEQ):
  fragment : not a proper pair in the Spec's sense: other chromosome, same strand, end-to-end fragment (clips included) outside 100..1000, or a dovetail/containment (forward start > reverse start or forward stop > reverse stop)
  clip     : minibwa soft-clips >= 10 bases in some mate (5'/3' end of the read, counted in bases)
  trimmed  : our trimmer removed >= 10 bases of some mate (or the whole mate)
  indel    : some mate has >= 2 gap events or >= 5 gap bases
  smallclip: minibwa soft-clips 1..9 bases in some mate (and no cause above)
  gaveup   : none of the above and our label is gaveUp (the places / repeat rule)
  errors   : none of the above, and minibwa's alignment scores < -16 in our model (pair penalty beyond the bound a `none` must beat), clip 0
  unexplained: none of the above, minibwa's alignment scores >= -16 end to end and we still say none
Primary class = first match in the order above; the overlap table counts every flag.
Score if the clipped part were excluded: minibwa's aligned part scored in our model (0 / -4 / -(6+2k)) from CIGAR + NM."""
import re, sys, collections
name, ours_p, mb_p, fq1, fq2 = sys.argv[1:6]; NEX = int(sys.argv[6]) if len(sys.argv) > 6 else 10
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
def parse(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        ops = [(int(n), o) for n, o in OPS.findall(r[5])] if r[5] != '*' else []
        tags = {t[:2]: t[5:] for t in r[11:]}
        d[(r[0], 1 if f & 64 else 2)] = dict(flag=f, mapped=not f & 4, chr=r[2], pos=int(r[3]), mapq=int(r[4]), cigar=r[5], ops=ops, strand='-' if f & 16 else '+',
            seqlen=0 if r[9] == '*' else len(r[9]), tags=tags, line=l.rstrip('\n'))
    return d
ours, mb = parse(ours_p), parse(mb_p)
def fastq(p):
    d = {}; it = iter(open(p))
    for h in it: d[h[1:].split()[0].split('/')[0]] = len(next(it).strip()); next(it); next(it)
    return d
L = {1: fastq(fq1), 2: fastq(fq2)}
pairs = sorted({k[0] for k in ours})
pop = [q for q in pairs if all(not ours[(q, i)]['mapped'] for i in (1, 2)) and all(mb[(q, i)]['mapped'] for i in (1, 2))
       and min(mb[(q, i)]['mapq'] for i in (1, 2)) >= 30]

def info(q, i):
    m = mb[(q, i)]; ops = m['ops']
    lead = ops[0][0] if ops[0][1] in 'SH' else 0; trail = ops[-1][0] if ops[-1][1] in 'SH' else 0
    gaps = [n for n, o in ops if o in 'ID']
    nm = int(m['tags']['NM'])
    five, three = (lead, trail) if m['strand'] == '+' else (trail, lead)      # clip at the read's 5' / 3' end
    aligned_pen = 4 * (nm - sum(gaps)) + sum(6 + 2 * n for n in gaps)
    reflen = sum(n for n, o in ops if o in 'MDN=X'); start = m['pos'] - lead; end = m['pos'] + reflen + trail
    return dict(lead=lead, trail=trail, five=five, three=three, ngaps=len(gaps), gapbases=sum(gaps), nm=nm, pen=aligned_pen, start=start, end=end, astart=m['pos'], aend=m['pos'] + reflen,
                lost=L[i][q] - ours[(q, i)]['seqlen'], qlen=sum(n for n, o in ops if o in 'MIS=X'), clip=lead + trail)
rows = []
for q in pop:
    a, b = info(q, 1), info(q, 2); m1, m2 = mb[(q, 1)], mb[(q, 2)]
    why = None
    if m1['chr'] != m2['chr']: frag, why = None, 'different chromosome'
    elif m1['strand'] == m2['strand']: frag, why = None, 'same strand'
    else:
        frag = max(a['end'], b['end']) - min(a['start'], b['start'])
        f, rv = (a, b) if m1['strand'] == '+' else (b, a)     # Spec/Mapping.lean: forward start <= reverse start, forward stop <= reverse stop
        f, rv = (a, b) if m1['strand'] == '+' else (b, a)
        okx = f['start'] <= rv['start'] and f['end'] <= rv['end']
        oka = f['astart'] <= rv['astart'] and f['aend'] <= rv['aend'] and 100 <= max(a['aend'], b['aend']) - min(a['astart'], b['astart']) <= 1000
        why = 'fragment < 100' if frag < 100 else 'fragment > 1000' if frag > 1000 else None if okx else \
              'read-through: proper only once the clipped ends (adapter) are excluded' if oka else 'dovetail / containment even without the clipped ends'
    fl = why is not None
    fl_ = dict(fragment=fl, clip=a['clip'] >= 10 or b['clip'] >= 10, trimmed=a['lost'] >= 10 or b['lost'] >= 10,
               indel=any(x['ngaps'] >= 2 or x['gapbases'] >= 5 for x in (a, b)))
    sc = -(a['pen'] + b['pen']); fl_['smallclip'] = 1 <= max(a['clip'], b['clip']) and not fl_['clip']
    gu = ours[(q, 1)]['tags'].get('XU') == 'gaveUp'
    prim = next((k for k in ('fragment', 'clip', 'trimmed', 'indel', 'smallclip') if fl_[k]), 'gaveup' if gu else 'errors' if sc < -16 else 'unexplained')
    rows.append(dict(q=q, a=a, b=b, frag=frag, flags=fl_, prim=prim, why=why, over=((max(0, f['astart'] - rv['astart'], f['aend'] - rv['aend']) if (why or '').startswith('dovetail') else 0) if m1['chr'] == m2['chr'] and m1['strand'] != m2['strand'] else 0), pair=-(a['pen'] + b['pen']), clipbases=a['clip'] + b['clip']))
N = len(pop)
pct = lambda n, d=None: f'{n} ({100 * n / (d or max(N, 1)):.1f}%)'
print(f'## {name}: {N} pairs where we give `none` (both mates unmapped) and minibwa maps both mates with MAPQ >= 30\n')
print('### Primary class (first match: fragment, clip >= 10, trimmed >= 10, indel, small clip, then gave up / errors / unexplained)\n\n| class | pairs |\n|---|---|')
for k in ('fragment', 'clip', 'trimmed', 'indel', 'smallclip', 'gaveup', 'errors', 'unexplained'): print(f'| {k} | {pct(sum(r["prim"] == k for r in rows))} |')
print('\n### Overlap (a pair counts in every class it has)\n\n| flag | pairs |\n|---|---|')
for k in ('fragment', 'clip', 'trimmed', 'indel', 'smallclip'): print(f'| {k} | {pct(sum(r["flags"][k] for r in rows))} |')
print(f'| none of the five | {pct(sum(r["prim"] in ("gaveup", "errors", "unexplained") for r in rows))} |')
print(f'| two or more | {pct(sum(sum(r["flags"].values()) >= 2 for r in rows))} |')
cl = [r for r in rows if r['flags']['clip']]
print(f'\n### Clipped pairs ({len(cl)})\n')
cb = [x for r in cl for x in (r['a'], r['b']) if x['clip'] >= 10]
print('clipped mates:', len(cb), '; clip at the read\'s 5\' end: %d, 3\' end: %d, both ends: %d' % (sum(x['five'] >= 10 and x['three'] < 10 for x in cb), sum(x['three'] >= 10 and x['five'] < 10 for x in cb), sum(x['five'] >= 10 and x['three'] >= 10 for x in cb)))
def hist(vals, edges):
    c = collections.Counter()
    for v in vals:
        for lo, hi in zip(edges, edges[1:] + [10**9]):
            if lo <= v < hi: c[(lo, hi)] += 1; break
    return ', '.join(f'{lo}-{hi - 1 if hi < 10**9 else "+"}: {c[(lo, hi)]}' for lo, hi in zip(edges, edges[1:] + [10**9]))
print('clipped bases per clipped mate: ' + hist([x['clip'] for x in cb], [10, 20, 30, 50, 75, 100]))
print('\nPair score of the ALIGNED part (clipped part excluded), our model; thresholds: -16 = the bound a `none` answer must beat (junkScore), -50 = report floor, -100:\n')
print('| clipped pairs with aligned-part score | >= -16 | >= -50 | >= -100 | < -100 |\n|---|---|---|---|---|')
print('| count | ' + ' | '.join(str(sum(r['pair'] >= t for r in cl)) for t in (-16, -50, -100)) + f' | {sum(r["pair"] < -100 for r in cl)} |')
est = [r['pair'] - 3 * r['clipbases'] for r in cl]
print(f'\nRough end-to-end score if the clipped bases were forced in as mismatches at 3 per base (random sequence: 4 x 3/4): >= -16: {sum(e >= -16 for e in est)}, >= -50: {sum(e >= -50 for e in est)}, >= -100: {sum(e >= -100 for e in est)} of {len(cl)}.')
print('\n### Not clipped\n')
nc = [r for r in rows if not r['flags']['clip']]
print(f'{len(nc)} pairs. Aligned score >= -16: {sum(r["pair"] >= -16 for r in nc)}, >= -50: {sum(r["pair"] >= -50 for r in nc)}, >= -100: {sum(r["pair"] >= -100 for r in nc)}.')
ot = [r for r in rows if r['prim'] in ('gaveup', 'errors', 'unexplained')]
print(f'no-cause pairs ({len(ot)}): minibwa NM per mate: ' + hist([x['nm'] for r in ot for x in (r['a'], r['b'])], [0, 2, 4, 6, 8, 12, 20]) + '; ours trimmed bases per mate: ' + hist([x['lost'] for r in ot for x in (r['a'], r['b'])], [0, 1, 5, 10]))
print('fragment class by reason: ' + ', '.join(f'{k}: {v}' for k, v in collections.Counter(r['why'] for r in rows if r['why']).most_common()))

dv = [r['over'] for r in rows if (r['why'] or '').startswith('dovetail')]
print('dovetail overshoot (bases the forward mate starts after / ends after the reverse mate, aligned part): ' + hist(dv, [1, 2, 3, 5, 10, 20, 50]) + f' of {len(dv)}')
print(f'\n## Examples ({NEX}, spread over the primary classes)\n')
classes = ('clip', 'trimmed', 'indel', 'fragment', 'smallclip', 'gaveup', 'errors', 'unexplained')
lists = {k: [r for r in rows if r['prim'] == k] for k in classes}
lists = {k: v[::max(1, len(v) // 2)][:2] for k, v in lists.items()}
picks = [lists[k][j] for j in (0, 1) for k in classes if len(lists[k]) > j]
for r in picks[:NEX]:
    m1, m2 = mb[(r['q'], 1)], mb[(r['q'], 2)]
    print(f'- `{r["q"]}` **{r["prim"]}**: minibwa {m1["chr"]}:{m1["pos"]}{m1["strand"]} {m1["cigar"]} / {m2["chr"]}:{m2["pos"]}{m2["strand"]} {m2["cigar"]} MAPQ {m1["mapq"]}/{m2["mapq"]}; '
          f'NM {r["a"]["nm"]}/{r["b"]["nm"]}; fragment {r["frag"]}; our trimmer removed {r["a"]["lost"]}/{r["b"]["lost"]} bases; aligned-part pair score {r["pair"]}; '
          f'ours: `{ours[(r["q"], 1)]["tags"].get("XU")}` {ours[(r["q"], 1)]["tags"].get("XT", "").strip()} XB {ours[(r["q"], 1)]["tags"].get("XB")}')
