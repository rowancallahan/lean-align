#!/usr/bin/env python3
"""Rescore minibwa's placement in OUR model for pairs where we say unique but minibwa is confident elsewhere.
   python3 -I rescore_unique.py SET ours.sam mb.sam R1.fq R2.fq genome.fa > report.md
In scope: both mates mapped by both tools, ours XU:Z:unique, minibwa MAPQ >= 30 on both mates, and at least one mate whose
reference interval is disjoint from minibwa's (other chromosome/strand counts as disjoint).
For each mate: our TRIMMED SEQ (and the FULL original read) is aligned end to end (match 0, mismatch -4, gap k -(6+2k); ends free in
the reference) in a window of +-10 around where minibwa puts it. Pair score = sum; proper = opposite strands, fragment 100..1000
(outer coordinates). Verdict BUG if minibwa's placement is proper and scores >= ours (our unique claim would be false)."""
import re, sys
name, ours_p, mb_p, fq1, fq2, fa = sys.argv[1:7]
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
RC = str.maketrans('ACGTNacgtn', 'TGCANtgcan')
rc = lambda s: s.translate(RC)[::-1]

def load(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        ops = [(int(n), o) for n, o in OPS.findall(r[5])] if r[5] != '*' else []
        d[(r[0], 1 if f & 64 else 2)] = dict(line=l.rstrip('\n'), mapped=not f & 4, chr=r[2], pos=int(r[3]), strand='-' if f & 16 else '+',
            mapq=int(r[4]), seq=r[9], ops=ops, tags={t[:2]: t[5:] for t in r[11:]},
            reflen=sum(n for n, o in ops if o in 'MDN=X'), lead=ops[0][0] if ops and ops[0][1] in 'SH' else 0,
            degenerate=bool(ops) and all(o == 'I' for _, o in ops))
    return d
ours, mb = load(ours_p), load(mb_p)

def fastq(p):
    d = {}; it = iter(open(p))
    for h in it: d[h[1:].split()[0].split('/')[0]] = next(it).strip(); next(it); next(it)
    return d
fq = {1: fastq(fq1), 2: fastq(fq2)}

pairs = sorted({k[0] for k in ours})
scope = []
for q in pairs:
    o, m = [ours[(q, i)] for i in (1, 2)], [mb[(q, i)] for i in (1, 2)]
    if not all(x['mapped'] for x in o + m) or any(x['degenerate'] for x in o): continue
    if not all(x['tags'].get('XU') == 'unique' for x in o) or min(x['mapq'] for x in m) < 30: continue
    disjoint = lambda a, b: (a['chr'], a['strand']) != (b['chr'], b['strand']) or a['pos'] + a['reflen'] <= b['pos'] or b['pos'] + b['reflen'] <= a['pos']
    # same-locus test used by real_vs_minibwa.py is diagonal based; here plain interval overlap, widened by the trimmed/clipped bases
    if any(disjoint(a, b) for a, b in zip(o, m)): scope.append(q)

need = {mb[(q, i)]['chr'] for q in scope for i in (1, 2)} | {ours[(q, i)]['chr'] for q in scope for i in (1, 2)}
genome, cur = {}, None
for l in open(fa):
    if l[0] == '>':
        cur = l[1:].split()[0]; genome[cur] = [] if cur in need else None
    elif genome[cur] is not None: genome[cur].append(l.strip().upper())
genome = {k: ''.join(v) for k, v in genome.items() if v is not None}
assert need <= genome.keys(), need - genome.keys()

def align(read, ref):
    """end-to-end in read, free ref ends, affine; returns (score, ref_start_offset, ref_end_offset exclusive)."""
    NEG = -10**9; n, m = len(read), len(ref)
    H = [[NEG] * (m + 1) for _ in range(n + 1)]; I = [[NEG] * (m + 1) for _ in range(n + 1)]; D = [[NEG] * (m + 1) for _ in range(n + 1)]
    S = [[0] * (m + 1) for _ in range(n + 1)]                # start column of the best path
    for j in range(m + 1): H[0][j] = 0; S[0][j] = j
    for i in range(1, n + 1):
        for j in range(0, m + 1):
            best, bs = NEG, 0
            if j > 0:
                sc = H[i - 1][j - 1] + (0 if read[i - 1] == ref[j - 1] and read[i - 1] != 'N' else -4)
                best, bs = sc, S[i - 1][j - 1]
                d = max(H[i][j - 1] - 8, D[i][j - 1] - 2); D[i][j] = d
                if d > best: best, bs = d, S[i][j - 1]
            ins = max(H[i - 1][j] - 8, I[i - 1][j] - 2); I[i][j] = ins
            if ins > best: best, bs = ins, S[i - 1][j]
            H[i][j] = best; S[i][j] = bs
    j = max(range(m + 1), key=lambda j: H[n][j])
    return H[n][j], S[n][j], j

def score_at(read_fwd, strand, fwd_start, fwd_len, rec, off):
    """Score read_fwd[fwd_start:fwd_start+fwd_len] aligned end to end near minibwa/our placement `rec` in orientation `strand`.
    Returns (score, ref_lo, ref_hi) 0-based half open."""
    L = len(read_fwd)
    seq = read_fwd[fwd_start:fwd_start + fwd_len]
    if strand == '-': seq = rc(seq); start = L - (fwd_start + fwd_len)      # offset in alignment orientation
    else: start = fwd_start
    diag = rec['pos'] - 1 - rec['lead'] - off                                          # ref pos of read base 0 along minibwa's first M segment
    # rec's ops: use the diagonal of its first M segment; indels in the clipped/trimmed part shift it, window +-10 + indel total covers most
    slack = 10 + sum(n for n, o in rec['ops'] if o in 'ID')
    lo = max(0, diag + start - slack); hi = diag + start + len(seq) + slack
    g = genome[rec['chr']]; hi = min(len(g), hi)
    sc, a, b = align(seq, g[lo:hi])
    return sc, lo + a, lo + b

def mate_info(q, i):
    o = ours[(q, i)]; full = fq[i][q]
    seq_al = o['seq']                                                      # SAM SEQ is in alignment orientation
    orig_al = full if o['strand'] == '+' else rc(full)
    s0 = orig_al.find(seq_al); assert s0 >= 0
    fwd_start = s0 if o['strand'] == '+' else len(full) - (s0 + len(seq_al))
    o['off'] = s0                                                          # trimmed bases before SEQ, alignment orientation
    return o, full, fwd_start, len(seq_al)

out = []
print(f'## {name}: {len(scope)} pairs in scope (ours unique both mates, minibwa MAPQ>=30 both, some mate disjoint)\n')
bug = 0
for q in scope:
    row = {}
    for i in (1, 2):
        o, full, fs, ln = mate_info(q, i); m = mb[(q, i)]
        # ours at our own placement (sanity): must reach at least our AS
        so, lo_o, hi_o = score_at(full, o['strand'], fs, ln, o, o['off'])
        assert so >= int(o['tags']['AS']), (q, i, so, o['tags']['AS'])
        sm, lo_m, hi_m = score_at(full, m['strand'], fs, ln, m, 0)
        fo, _, _ = score_at(full, o['strand'], 0, len(full), o, o['off'])
        fm, _, _ = score_at(full, m['strand'], 0, len(full), m, 0)
        row[i] = dict(ours_as=int(o['tags']['AS']), ours_re=so, mb_trim=sm, ours_full=fo, mb_full=fm, ours=(o['chr'], o['strand'], lo_o, hi_o),
                      mb=(m['chr'], m['strand'], lo_m, hi_m), trim=(fs, len(full) - fs - ln), mbmapq=m['mapq'], xa='XA' in m['tags'], mbcig=m['line'].split('\t')[5],
                      ocig=o['line'].split('\t')[5])
    mbp = [row[1]['mb'], row[2]['mb']]
    proper = mbp[0][0] == mbp[1][0] and mbp[0][1] != mbp[1][1] and 100 <= max(x[3] for x in mbp) - min(x[2] for x in mbp) <= 1000
    frag = max(x[3] for x in mbp) - min(x[2] for x in mbp) if mbp[0][0] == mbp[1][0] else None
    ours_pair = row[1]['ours_as'] + row[2]['ours_as']; mb_pair = row[1]['mb_trim'] + row[2]['mb_trim']
    verdict = 'BUG? minibwa placement >= ours' if proper and mb_pair >= ours_pair else ('consistent: lower' if proper else 'consistent: not a proper pair')
    bug += verdict.startswith('BUG')
    print(f'- `{q}` ours pair {ours_pair} (mates {row[1]["ours_as"]},{row[2]["ours_as"]}); minibwa placement in our model {mb_pair} '
          f'(mates {row[1]["mb_trim"]},{row[2]["mb_trim"]}); proper={proper} frag={frag}; **{verdict}**')
    for i in (1, 2):
        r = row[i]
        print(f'  - mate{i}: trimmed (left,right)={r["trim"]}; ours {r["ours"]} {r["ocig"]}; minibwa {r["mb"]} {r["mbcig"]} MAPQ {r["mbmapq"]}{" XA" if r["xa"] else ""}; '
              f'trimmed read: ours {r["ours_re"]} vs minibwa-place {r["mb_trim"]}; FULL read: ours-place {r["ours_full"]} vs minibwa-place {r["mb_full"]}')
print(f'\nBUG? count: {bug} of {len(scope)}')
