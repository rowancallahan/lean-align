#!/usr/bin/env python3
"""Audit lean-align's SAM against the reference and against minibwa's placements, using the spec's own scoring.
   python3 audit_vs_minibwa.py ours.sam minibwa.sam GENOME_ONE_LINE.fa [label]
Scoring (Spec/Alignment.lean): match 0, mismatch -4, a gap of k letters -(6 + 2k), whole trimmed read against the reference letters.
Properness (Spec/Mapping.lean, insert range 100..1000, slack 0): same chromosome, opposite strands, forward start <= reverse stop,
fragment = reverse stop - forward start within range, forward start <= reverse start, forward stop <= reverse stop.
Checks (a HARD line means a proof/spec hole or a bug):
  A  HARD  AS of a mapped record != the score recomputed from CIGAR + SEQ + the reference
  B  HARD  XB < AS1 + AS2 on a mapped pair (the bound is below the pair it reports)
  C  HARD  XB < the score, under our scoring, of a proper pair built from minibwa's placement (the bound would be false)
  D  HARD  XU:Z:unique but minibwa's proper pair is at another placement scoring >= ours, or the same placement scoring higher
  E  info  XU:Z:unique, minibwa MAPQ 60 on both mates elsewhere, and the true origin agrees with minibwa (the thing to report at once)
  F  info  degenerate CIGARs: only insertions (^[0-9]+I$), or without any M
  G  info  mates that differ from minibwa, by category, and mates within 10 bp of the true origin (as Testing/fuzz/compare_sam.py)
minibwa's alignment is turned into an end-to-end alignment of OUR (trimmed) window of the read: soft-clipped letters inside the window
continue the diagonal; a pair is skipped if the window is not found in minibwa's SEQ or leaves the chromosome."""
import mmap, re, sys, collections
ours_p, mb_p, fa = sys.argv[1:4]
label = sys.argv[4] if len(sys.argv) > 4 else ''
fh = open(fa, 'rb'); G = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ)
chrom, i = {}, 0
while i < len(G):                                   # one-line FASTA: header line, sequence line
    j = G.find(b'\n', i); k = G.find(b'\n', j + 1); k = len(G) if k < 0 else k
    chrom[G[i + 1:j].split()[0].decode()] = (j + 1, k - j - 1); i = k + 1
def ref(c, a, b):                                   # letters [a, b) of chromosome c, or None if outside
    s, n = chrom[c]
    return G[s + a:s + b].decode() if 0 <= a <= b <= n else None
RC = str.maketrans('ACGTN', 'TGCAN'); rc = lambda s: s.translate(RC)[::-1]
def load(p):
    out = {}
    for l in open(p):
        if l[0] == '@': continue
        f = l.rstrip('\n').split('\t'); fl = int(f[1])
        if fl & 0x900: continue
        out[(f[0], 1 if fl & 64 else 2)] = dict(flag=fl, chr=f[2], pos=int(f[3]) - 1, mapq=int(f[4]), cigar=f[5], seq=f[9],
                                               tags={t[:2]: t[5:] for t in f[11:]}, mapped=not fl & 4, rev=bool(fl & 16))
    return out
ours, mb = load(ours_p), load(mb_p)
assert ours.keys() == mb.keys()
names = list(dict.fromkeys(n for n, _ in ours))
def cols(cigar, pos, clip=True):                    # CIGAR -> columns ('d', read i, ref r) / ('I', i, None) / ('D', None, r); soft clips continue the diagonal
    ops = [(int(n), o) for n, o in re.findall(r'(\d+)([MIDSHX=])', cigar)]
    out, r, i = [], pos, 0
    if ops and ops[0][1] == 'S':
        n = ops[0][0]; out += [('d', j, pos - n + j) for j in range(n)]; i = n; ops = ops[1:]
    tail = ops[-1][0] if ops and ops[-1][1] == 'S' else 0
    if tail: ops = ops[:-1]
    for n, o in ops:
        for _ in range(n):
            if o in 'M=X': out.append(('d', i, r)); i += 1; r += 1
            elif o == 'I': out.append(('I', i, None)); i += 1
            elif o == 'D': out.append(('D', None, r)); r += 1
    out += [('d', i + j, r + j) for j in range(tail)]
    return out
def score(c, S, columns):                           # spec score of the columns (read letters S, chromosome c); None if outside
    rs = [r for _, _, r in columns if r is not None]
    X = ref(c, min(rs), max(rs) + 1) if rs else ''
    if X is None: return None
    lo = min(rs) if rs else 0
    s, prev = 0, None
    for kind, ri, rr in columns:
        if kind == 'd': s += 0 if S[ri] == X[rr - lo] else -4; prev = 'd'
        else: s += -2 if prev == kind else -8; prev = kind
    return s
def span(columns):                                  # placement start/stop on the reference
    rs = [r for k, _, r in columns if r is not None]
    return (min(rs), max(rs) + 1) if rs else None
def proper(a, b, lo=100, hi=1000):                  # a, b = (chromosome, start, stop, reverse?)
    if a[0] != b[0] or a[3] == b[3]: return False
    f, r = (a, b) if not a[3] else (b, a)
    return f[1] <= r[2] and lo <= r[2] - f[1] <= hi and f[1] <= r[1] and f[2] <= r[2]
def truth(n):
    m = re.match(r'[^:]+:([^:]+):(\d+)-(\d+)([+-]):(\d+)-(\d+)([+-])', n)
    return {1: (m[1], int(m[2]), int(m[3]), m[4] == '-'), 2: (m[1], int(m[5]), int(m[6]), m[7] == '-')} if m else None
def mb_window(o, m):                                # minibwa's alignment of OUR window of the read: (columns restricted to the window, S) or None
    if o['seq'] == '*' or not m['mapped'] or m['seq'] == '*': return None
    rw = rc(o['seq']) if o['mapped'] and o['rev'] else o['seq']      # the window as in the read
    want = rc(rw) if m['rev'] else rw
    t0 = m['seq'].find(want)
    if t0 < 0: return None
    allc = cols(m['cigar'], m['pos'])
    idx = [k for k, (kind, ri, _) in enumerate(allc) if ri is not None and t0 <= ri < t0 + len(want)]
    if not idx: return None
    sub = [c for c in allc[idx[0]:idx[-1] + 1] if c[0] == 'D' or (c[1] is not None and t0 <= c[1] < t0 + len(want))]
    return sub, m['seq']
hard, info, ex = collections.Counter(), collections.Counter(), collections.defaultdict(list)
def note(rule, msg, kind=hard):
    kind[rule] += 1
    if len(ex[rule]) < 5: ex[rule].append(msg)
cat = collections.Counter(); n = same = same_cig = ot = mt = 0
for name in names:
    O = {1: ours[(name, 1)], 2: ours[(name, 2)]}; M = {1: mb[(name, 1)], 2: mb[(name, 2)]}
    T = truth(name)
    # F: degenerate CIGARs; A: AS recomputation
    for mt_ in (1, 2):
        o = O[mt_]
        if o['mapped']:
            if re.fullmatch(r'\d+I', o['cigar']): info['F: CIGAR only insertions (^[0-9]+I$)'] += 1
            if not re.search(r'\d+[M=X]', o['cigar']): info['F: CIGAR without any M'] += 1
            c = cols(o['cigar'], o['pos']); sc = score(o['chr'], o['seq'], c)
            if sc is None or sc != int(o['tags']['AS']): note('A: AS != recomputed score', f"{name} m{mt_} {o['chr']}:{o['pos'] + 1} {o['cigar']} AS {o['tags']['AS']} recomputed {sc}")
    # B: bound below the reported pair
    if 'XB' not in O[1]['tags']: continue                                   # a pair with a trimmed-away mate carries no bound
    if O[1]['mapped'] and O[2]['mapped'] and int(O[1]['tags']['XB']) < int(O[1]['tags']['AS']) + int(O[2]['tags']['AS']):
        note('B: XB < AS1 + AS2', f"{name} XB {O[1]['tags']['XB']} AS {O[1]['tags']['AS']}+{O[2]['tags']['AS']}")
    # C, D, E: minibwa's pair under our scoring
    W = [mb_window(O[k], M[k]) for k in (1, 2)]
    if all(W) and M[1]['chr'] == M[2]['chr']:
        sc = [score(M[k]['chr'], W[k - 1][1], W[k - 1][0]) for k in (1, 2)]
        sp = [span(W[k - 1][0]) for k in (1, 2)]
        if None not in sc and None not in sp:
            mbp = [(M[k]['chr'], sp[k - 1][0], sp[k - 1][1], M[k]['rev']) for k in (1, 2)]
            if proper(*mbp):
                total = sc[0] + sc[1]; info['C: pairs where minibwa gives a proper pair we could score'] += 1
                xb = int(O[1]['tags']['XB'])
                if O[1]['mapped'] and O[2]['mapped'] and all((O[k]['chr'], O[k]['pos'], O[k]['rev']) == (M[k]['chr'], M[k]['pos'], M[k]['rev']) for k in (1, 2)) and 'AS' in O[1]['tags']:
                    ok = total == int(O[1]['tags']['AS']) + int(O[2]['tags']['AS'])   # self-test of the rebuilt minibwa alignment: same start, so equal unless the CIGARs differ
                    info['self-test, same start both mates: rebuilt minibwa score == our AS1+AS2' if ok else 'self-test, same start both mates: rebuilt minibwa score != our AS1+AS2 (CIGARs differ)'] += 1
                if total > xb: note('C: XB below a minibwa proper pair score', f"{name} XB {xb} minibwa-pair score {total} {M[1]['chr']}:{M[1]['pos'] + 1} {M[1]['cigar']} / {M[2]['pos'] + 1} {M[2]['cigar']}")
                if O[1]['tags']['XU'] == 'unique' and O[1]['mapped'] and O[2]['mapped']:
                    ours_pair = [(O[k]['chr'], O[k]['pos'], O[k]['pos'] + sum(int(x) for x, o in re.findall(r'(\d+)([MD])', O[k]['cigar'])), O[k]['rev']) for k in (1, 2)]
                    s_ours = int(O[1]['tags']['AS']) + int(O[2]['tags']['AS'])
                    if mbp == ours_pair and total > s_ours or mbp != ours_pair and total >= s_ours:
                        note('D: unique but minibwa has a proper pair elsewhere scoring >= ours', f"{name} ours {s_ours} {O[1]['chr']}:{O[1]['pos'] + 1} / minibwa {total} {M[1]['chr']}:{M[1]['pos'] + 1} {M[1]['cigar']}")
    # E
    if O[1]['tags'].get('XU') == 'unique' and T and all(M[k]['mapped'] for k in (1, 2)) and all(M[k]['mapq'] == 60 for k in (1, 2)):
        elsewhere = any((M[k]['chr'], M[k]['rev']) != (O[k]['chr'], O[k]['rev']) or abs(M[k]['pos'] - O[k]['pos']) > 400 for k in (1, 2))
        near = lambda x, t: x['mapped'] and x['chr'] == t[0] and x['rev'] == t[3] and abs(x['pos'] - t[1]) <= 10
        if elsewhere and all(near(M[k], T[k]) for k in (1, 2)): note('E: ours unique, minibwa MAPQ 60 elsewhere, truth = minibwa', f"{name} ours {O[1]['chr']}:{O[1]['pos'] + 1} minibwa {M[1]['chr']}:{M[1]['pos'] + 1}", info)
    # H: our unique pairs against the true origin
    if T and O[1]['tags'].get('XU') == 'unique':
        nr = lambda x, k: x['mapped'] and x['chr'] == T[k][0] and x['rev'] == T[k][3] and abs(x['pos'] - T[k][1]) <= 10
        ok_o = all(nr(O[k], k) for k in (1, 2)); ok_m = all(nr(M[k], k) for k in (1, 2))
        info['H: our unique pairs'] += 1
        if not ok_o:
            info['H: our unique pairs with a mate not within 10 bp of the true origin'] += 1
            info['H:   of these, minibwa has both mates at the origin' if ok_m else 'H:   of these, minibwa also not at the origin (both mates)'] += 1
            if ok_m and len(ex['H']) < 3: ex['H'].append(f"{name} ours {O[1]['chr']}:{O[1]['pos'] + 1} {O[1]['cigar']} AS {O[1]['tags']['AS']}+{O[2]['tags']['AS']} XB {O[1]['tags']['XB']}; minibwa {M[1]['chr']}:{M[1]['pos'] + 1} {M[1]['cigar']} mapq {M[1]['mapq']}")
    # G: mate differences and truth
    for k in (1, 2):
        o, m = O[k], M[k]; n += 1
        key = lambda x: (x['chr'], x['pos'], x['rev']) if x['mapped'] else None
        near = lambda x: bool(T) and x['mapped'] and x['chr'] == T[k][0] and x['rev'] == T[k][3] and abs(x['pos'] - T[k][1]) <= 10
        ot += near(o); mt += near(m)
        if o['mapped'] and m['mapped'] and key(o) == key(m): same += 1; same_cig += o['cigar'] == m['cigar']; continue
        if not o['mapped'] and not m['mapped']: cat['both unmapped'] += 1; continue
        if not o['mapped']: cat['ours unmapped, minibwa maps'] += 1; continue
        if not m['mapped']: cat['minibwa unmapped, ours maps'] += 1; continue
        who = lambda: ('ours is a placeholder (no M)' if not re.search(r'\d+[M=X]', o['cigar']) else
                       'ours at truth' if T and near(o) else 'minibwa at truth' if T and near(m) else 'neither at truth')
        if (o['chr'], o['rev']) != (m['chr'], m['rev']): cat['different chromosome or strand: ' + who()] += 1; continue
        la = sum(int(x) for x, op in re.findall(r'(\d+)([MD])', o['cigar'])); lb = sum(int(x) for x, op in re.findall(r'(\d+)([MD])', m['cigar']))
        a0, a1, b0, b1 = o['pos'], o['pos'] + la, m['pos'], m['pos'] + lb
        cat['ours inside minibwa (trimmed/clipped more)' if b0 <= a0 and a1 <= b1 else
            'minibwa inside ours (it clips more)' if a0 <= b0 and b1 <= a1 else 'shifted overlap' if min(a1, b1) > max(a0, b0) else 'same chromosome, disjoint: ' + who()] += 1
print(f'== {label}: {len(names)} pairs, {n} mates')
for r in sorted(set(hard) | {'A: AS != recomputed score', 'B: XB < AS1 + AS2', 'C: XB below a minibwa proper pair score', 'D: unique but minibwa has a proper pair elsewhere scoring >= ours'}):
    print(f"  HARD {r}: {hard[r]}" + (f"   e.g. {ex[r][:3]}" if hard[r] else ''))
for r, v in sorted(info.items()): print(f'  info {r}: {v}' + (f"   e.g. {ex[r][:3]}" if r in ex else ''))
if ex['H']: print(f"  info H e.g. {ex['H']}")
print(f'  mates {n}: same position {same}, same position+CIGAR {same_cig}; within 10 bp of truth: ours {ot}, minibwa {mt}')
for r, v in cat.most_common(): print(f'    differs: {r}: {v}')
