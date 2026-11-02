#!/usr/bin/env python3
"""Pick the pairs of Testing/examples/sam_compare from two minibwa SAMs (run once; the picked FASTQ is committed).
   python3 sam_example_pick.py MASON.sam MASON_R1 MASON_R2 HG002.sam HG002_R1 HG002_R2 OUT_PREFIX
unique: 20 mason pairs, MAPQ>=30 on both mates, proper, both mates at the true position, one per chromosome first
nonunique: 5 mason pairs with a mate MAPQ<30      unmapped: 2 HG002 pairs with both mates unmapped, 1 with one mate unmapped"""
import re, sys
msam, m1, m2, hsam, h1, h2, out = sys.argv[1:]
def sam(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t')
        if int(r[1]) & 0x900 == 0: d.setdefault(r[0], []).append(r)
    return d
def fq(p):
    L = open(p).read().split('\n'); return {L[i][1:].split()[0]: '\n'.join(L[i:i+4]) for i in range(0, len(L) - 3, 4)}
M, H = sam(msam), sam(hsam)
def true_ok(n, a, b):
    c, b1, _, _, b2 = re.match(r's\d+:([^:]+):(\d+)-(\d+)([+-]):(\d+)-', n).groups()
    return a[2] == c and int(a[3]) == int(b1) + 1 and int(b[3]) == int(b2) + 1
uniq, seen = [], set()
for n, (a, b) in M.items():
    chrom = a[2]
    if min(int(a[4]), int(b[4])) >= 30 and int(a[1]) & 2 and true_ok(n, a, b) and chrom not in seen:
        seen.add(chrom); uniq.append(n)
    if len(uniq) == 20: break
assert len(uniq) == 20, len(uniq)
low = sorted((n for n, (a, b) in M.items() if min(int(a[4]), int(b[4])) < 30), key=lambda n: int(n.split(':')[0][1:]))
nonu = [low[i] for i in (0, 1, 2, 7, 11)]
both = [n for n, (a, b) in H.items() if int(a[1]) & 4 and int(b[1]) & 4][:2]
half = [n for n, (a, b) in H.items() if (int(a[1]) & 4) != (int(b[1]) & 4)][:1]
assert len(both) == 2 and len(half) == 1
f = [(fq(m1), fq(m2), uniq + nonu), (fq(h1), fq(h2), both + half)]
with open(out + '_R1.fq', 'w') as o1, open(out + '_R2.fq', 'w') as o2:
    for q1, q2, names in f:
        for n in names: o1.write(q1[n] + '\n'); o2.write(q2[n] + '\n')
print(len(uniq + nonu + both + half), 'pairs')
