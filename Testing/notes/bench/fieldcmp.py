"""fieldcmp.py OURS.sam MB.sam LABEL: on pairs where both tools report the same proper pair (both mates flag 0x2,
same RNAME+POS for each mate), compare FLAG RNAME POS MAPQclass CIGAR RNEXT PNEXT TLEN SEQ QUAL per record."""
import sys, collections
def load(p):
    d = {}
    for l in open(p):
        if l[0] == '@': continue
        f = l.rstrip('\n').split('\t')
        if int(f[1]) & 0x900: continue
        d[(f[0], int(f[1]) & 0xC0)] = f
    return d
o, m = load(sys.argv[1]), load(sys.argv[2])
assert len(o) == len(m), (len(o), len(m))
names = {k[0] for k in o}
cols = ['QNAME','FLAG','RNAME','POS','MAPQ','CIGAR','RNEXT','PNEXT','TLEN','SEQ','QUAL']
bad = collections.Counter(); ex = collections.defaultdict(list); pairs = 0
for n in names:
    a = [o[(n, 0x40)], o[(n, 0x80)]]; b = [m[(n, 0x40)], m[(n, 0x80)]]
    if not all(int(x[1]) & 2 for x in a + b): continue
    if any((x[2], x[3]) != (y[2], y[3]) for x, y in zip(a, b)): continue
    pairs += 1
    for x, y in zip(a, b):
        for i in range(1, 11):
            u, v = x[i], y[i]
            if i == 4: u, v = u == '60', v == '60'
            if u != v:
                bad[cols[i]] += 1
                if len(ex[cols[i]]) < 3: ex[cols[i]].append(('ours', '\t'.join(x[:11])[:300], 'mb', '\t'.join(y[:11])[:300]))
print(f'{sys.argv[3]}: same proper pairs {pairs}, records {2*pairs}; disagreeing fields: {dict(bad) or "none"}')
for c in ex:
    for e in ex[c]: print(f'  {c}:', *e, sep='\n    ')
