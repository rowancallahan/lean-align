#!/usr/bin/env python3
"""Side-by-side table for Testing/examples/sam_compare (called by compare_sam_example.sh).
   python3 -I sam_example_table.py DIR CHROMOSOMES
DIR holds shim.sam, minibwa.sam, bench_pairs.tsv (whole_genome WG_OUT RTX dump), bench_tiers.tsv (WG_TIEROUT dump).
CHROMOSOMES is shim.idx.chromosomes (name TAB length).
One row per mate. truth = the position in the simulated read name (mason pairs only; 0-based half-open there, shown 1-based).
The bench reads the FASTA as ONE record: every header line after the first stays in the stream as letters, so its
positions are global offsets that include 1+len(name) bytes per record from the second on; undone here."""
import re, sys
d, chrfile = sys.argv[1:]
chroms = [(l.split('\t')[0], int(l.split('\t')[1])) for l in open(chrfile).read().split('\n') if l]
starts, g = [], 0   # global offset of each chromosome's first letter in the bench's stream
for i, (n, L) in enumerate(chroms):
    if i: g += 1 + len(n)
    starts.append(g); g += L
def chrpos(off):   # global 0-based offset -> (chromosome, 1-based position)
    i = max(j for j in range(len(chroms)) if starts[j] <= off)
    assert off - starts[i] < chroms[i][1], off
    return chroms[i][0], off - starts[i] + 1
def sam(p):
    out = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900 == 0: out.setdefault(r[0], {})[1 if f & 64 else 2] = r
    return out
def span(cigar):   # reference length of a CIGAR
    return sum(int(n) for n, op in re.findall(r'(\d+)([MIDNSHP=X])', cigar) if op in 'MDN=X')
shim, mb = sam(d + '/shim.sam'), sam(d + '/minibwa.sam')
bench = [l.rstrip('\n').split('\t') for l in open(d + '/bench_pairs.tsv')]
tiers = [l.rstrip('\n').split('\t') for l in open(d + '/bench_tiers.tsv')]
names = list(mb)                  # minibwa keeps the input order
assert len(names) == len(bench) == len(tiers) == len(shim) == len(set(names)), (len(names), len(bench), len(tiers))
head = ['pair', 'kind', 'm', 'truth', 'minibwa chr:pos str CIGAR MAPQ proper', 'bench chr:pos str pen', 'bench=mb', 'shim flag XB XT']
rows = []
for i, n in enumerate(names):
    t = re.match(r's\d+:([^:]+):(\d+)-\d+([+-]):(\d+)-\d+([+-])', n)
    truth = {1: f'{t[1]}:{int(t[2]) + 1} {t[3]}', 2: f'{t[1]}:{int(t[4]) + 1} {t[5]}'} if t else {1: '-', 2: '-'}
    q = [mb[n][1], mb[n][2]]
    mq = min(int(x[4]) for x in q)
    kind = 'unmapped' if all(int(x[1]) & 4 for x in q) else 'half-mapped' if any(int(x[1]) & 4 for x in q) else \
           'unique' if mq >= 30 else 'non-unique'
    b = bench[i]; assert b[0] == f'p{i + 1}'
    why = tiers[i][-3]
    for m in (1, 2):
        r = mb[n][m]; f = int(r[1])
        mbtxt = '*  unmapped' if f & 4 else f"{r[2]}:{r[3]} {'-' if f & 16 else '+'} {r[5]} {r[4]} {'yes' if f & 2 else 'no'}"
        if b[1] == 'none':
            bt, same = f'none ({tiers[i][1]} {why})', ('-' if f & 4 else 'no pair')
        else:
            o = 1 + 5 * (m - 1)   # chromosome index, global start, length, penalty, strand
            c, p = chrpos(int(b[o + 1])); bt = f'{c}:{p} {b[o + 4]} {b[o + 3]}'
            if f & 4: same = 'mb unmapped'
            elif (c, b[o + 4]) != (r[2], '-' if f & 16 else '+'): same = 'differs'
            elif p == int(r[3]): same = 'same pos'
            elif p < int(r[3]) + span(r[5]) and int(r[3]) < p + int(b[o + 2]): same = 'overlap'
            else: same = 'differs'
        s = shim[n][m]
        rows.append([n.split(':')[0] if t else n.split(':')[-2] + ':' + n.split(':')[-1].split()[0], kind, str(m), truth[m], mbtxt, bt, same,
                     f"{s[1]} " + ' '.join(x[3:] for x in s[11:] if x[:2] in ('XB', 'XT'))])
w = [max(len(x[j]) for x in rows + [head]) for j in range(len(head))]
for r in [head] + rows:
    print('  '.join(c.ljust(w[j]) for j, c in enumerate(r)).rstrip())
