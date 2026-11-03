#!/usr/bin/env python3
"""How often does our trimmer cut away a mate (or >= 30 bases of it) that minibwa aligns well?
   python3 -I trim_overcut.py SET ours.sam mb.sam R1.fq R2.fq hg38.1l.fa > report.md
Overcut mate: minibwa MAPQ >= 30, and in the region we cut (the whole mate, or >= 30 bases at the ends) minibwa has >= 30 aligned (M) bases
whose mismatch rate against the reference is <= 5 %.  Our kept window is found by locating our SAM SEQ in the original read; the quality
trimmer is replicated (best window of sum(Q_i - Q), N = -1e6, Q = 25) to check it against the shim and to sweep Q."""
import mmap, re, sys, collections
name, ours_p, mb_p, fq1, fq2, fa = sys.argv[1:7]
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
RC = str.maketrans('ACGTN', 'TGCAN'); rc = lambda s: s.translate(RC)[::-1]
def parse(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        d[(r[0], 1 if f & 64 else 2)] = dict(flag=f, mapped=not f & 4, chr=r[2], pos=int(r[3]), mapq=int(r[4]), cigar=r[5], strand='-' if f & 16 else '+',
            seq=r[9], ops=[(int(n), o) for n, o in OPS.findall(r[5])] if r[5] != '*' else [], tags={t[:2]: t[5:] for t in r[11:]})
    return d
ours, mb = parse(ours_p), parse(mb_p)
def fastq(p):
    d = {}; it = iter(open(p))
    for h in it: d[h[1:].split()[0].split('/')[0]] = (next(it).strip(), (next(it), next(it).strip())[1])
    return d
fq = {1: fastq(fq1), 2: fastq(fq2)}
fh = open(fa, 'rb'); G = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ); chrom, i = {}, 0
while i < len(G):
    j = G.find(b'\n', i); k = G.find(b'\n', j + 1); k = len(G) if k < 0 else k
    chrom[G[i + 1:j].split()[0].decode()] = (j + 1, k - j - 1); i = k + 1
def ref(c, a, n):
    o, L = chrom[c]
    return G[o + a:o + a + n].decode().upper() if 0 <= a and a + n <= L else None

def window(seq, qual, Q):
    """best-scoring window of sum(min(q,93) - Q) (N = -1e6); returns (s, e) or None (first maximum, shortest on ties)."""
    best, bs, be, cur, cs = None, 0, 0, 0, 0
    for i, (c, q) in enumerate(zip(seq, qual)):
        v = (min(ord(q) - 33, 93) - Q) if c in 'ACGT' else -10**6
        if cur <= 0: cur, cs = v, i
        else: cur += v
        if best is None or cur > best: best, bs, be = cur, cs, i + 1
    return (bs, be) if best is not None and best > -10**5 else None

rows, sweep = [], collections.Counter(); tot = ok = mism = 0
for (q, m), o in sorted(ours.items()):
    orig, qual = fq[m][q]; L = len(orig); mr = mb[(q, m)]
    # our kept window in read coordinates
    if o['seq'] == '*': ws = we = 0
    else:
        s_al = o['seq'] if o['strand'] == '+' else rc(o['seq']); s0 = orig.find(s_al); assert s0 >= 0 or o['seq'] == '*', (q, m); ws, we = s0, s0 + len(s_al)
    tot += 1
    w = window(orig, qual, 25)
    if w == (ws, we): ok += 1
    cut = L - (we - ws)
    if cut < 30 and we > ws: continue
    if not mr['mapped'] or mr['mapq'] < 30: continue
    # minibwa-aligned bases inside the cut regions, mismatches against the reference
    sa = mr['seq']; strand = mr['strand']; readal = sa
    cutal = [(0, ws), (we, L)] if strand == '+' else [(L - we, L), (0, L - ws)]
    cutal = [(a, b) for a, b in cutal if b > a]
    qp, rp, aligned = 0, mr['pos'] - 1, []
    for n, op in mr['ops']:
        if op in 'M=X':
            aligned.append((qp, rp, n)); qp += n; rp += n
        elif op in 'IS': qp += n
        elif op in 'DN': rp += n
    nal = nmm = 0
    for qs, rs, n in aligned:
        refseq = ref(mr['chr'], rs, n)
        if refseq is None: continue
        for a, b in cutal:
            lo, hi = max(a, qs), min(b, qs + n)
            for x in range(lo, hi):
                nal += 1; nmm += readal[x] != refseq[x - qs] or readal[x] == 'N'
    if nal < 30 or nmm > 0.05 * nal: continue
    # quality of the cut bases (read orientation), and the largest Q whose window keeps >= 90 % of the aligned cut bases
    cutrd = [(0, ws), (we, L)]; cutrd = [(a, b) for a, b in cutrd if b > a]
    qs_ = [ord(qual[x]) - 33 for a, b in cutrd for x in range(a, b)]
    need = set(x for a, b in cutrd for x in range(a, b))
    keepQ = None
    for Qt in range(25, -1, -1):
        wq = window(orig, qual, Qt)
        if wq and sum(1 for x in need if wq[0] <= x < wq[1]) >= 0.9 * len(need): keepQ = Qt; break
    rows.append(dict(q=q, m=m, L=L, cut=cut, whole=we == ws, meanq=sum(qs_) / len(qs_), nal=nal, nmm=nmm, keepQ=keepQ, mapq=mr['mapq'], ends=('5\'' if (ws > 0) else '') + ('3\'' if we < L else '')))
print(f'## {name}: trimmer overcut vs minibwa\n')
print(f'Replica check: my best-window replica (Q=25) equals the shim\'s kept window on {ok} of {tot} mates ({100 * ok / tot:.2f} %); the rest are adapter cuts (`AdapterTrim.cutTruSeq`) and `dropShort`, which the replica does not do.\n')
pairs_ = {r['q'] for r in rows}
nm_ = len(rows)
print(f'**Overcut mates** (cut >= 30 bases or the whole mate; minibwa MAPQ >= 30; >= 30 aligned bases in the cut region with <= 5 % mismatches): **{nm_}** mates in {len(pairs_)} pairs, of {tot} mates.\n')
print(f'- whole mate cut away: {sum(r["whole"] for r in rows)}; partial cuts: {sum(not r["whole"] for r in rows)} (5\'/3\' end: ' + ', '.join(f'{k or "?"}: {v}' for k, v in collections.Counter(r["ends"] for r in rows if not r["whole"]).most_common()) + ')')
def hist(vals, edges):
    c = collections.Counter()
    for v in vals:
        for lo, hi in zip(edges, edges[1:] + [10**9]):
            if lo <= v < hi: c[(lo, hi)] += 1; break
    return ', '.join(f'{lo}-{hi - 1 if hi < 10**9 else "+"}: {c[(lo, hi)]}' for lo, hi in zip(edges, edges[1:] + [10**9]))
print('- bases cut per overcut mate: ' + hist([r['cut'] for r in rows], [30, 50, 75, 100, 150, 200]))
print('- mean Q of the cut bases: ' + hist([int(r['meanq']) for r in rows], [0, 10, 15, 20, 25, 30, 35]))
print('- mismatch rate of minibwa in the cut region: ' + hist([int(100 * r['nmm'] / r['nal']) for r in rows], [0, 1, 2, 3, 4, 5]) + ' (percent)')
print('- largest Q that would keep >= 90 % of the cut bases (current Q = 25): ' + ', '.join(f'Q={k}: {v}' for k, v in sorted(collections.Counter(r["keepQ"] for r in rows).items(), key=lambda x: -(x[0] if x[0] is not None else -1))))
print(f'\nPairs affected: {len(pairs_)} ({100 * len(pairs_) / (tot / 2):.2f} % of pairs).')
print('\n### Sample of overcut mates\n')
for r in rows[::max(1, len(rows) // 10)][:10]:
    print(f'- `{r["q"]}` mate{r["m"]}: length {r["L"]}, cut {r["cut"]}{" (whole mate)" if r["whole"] else ""} at {r["ends"]}, mean Q of the cut bases {r["meanq"]:.1f}, minibwa MAPQ {r["mapq"]}, {r["nmm"]}/{r["nal"]} mismatches in the cut region, would be kept at Q={r["keepQ"]}')
