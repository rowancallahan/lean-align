#!/usr/bin/env python3
"""Synthetic non-human genomes (one-line FASTA, as sim_pairs.py reads them).  python3 -I gen_genomes.py OUT_DIR
ecoli_like  4.6 Mb, 1 chr, GC 51%, 7 rRNA operons (5 kb, exact-ish), 30 IS elements (1.3 kb)
yeast_like  12 Mb, 16 chr (0.2-1.5 Mb), GC 38%, 50 Ty elements (6 kb, 1% div), 30 kb of 'CCCACACACC' repeats at each end
at_rich     20 Mb, 5 chr, GC 20%, microsatellites/homopolymer runs (Plasmodium-like)
gc_rich     10 Mb, 3 chr, GC 70%
plant_like  30 Mb, 5 chr, GC 36%, 180 bp satellite arrays (500 kb each, 10% div), 5% interspersed 300 bp families
unit_repeat 5 Mb, 1 chr: 2 kb unit, each copy 1% diverged from it
many_contigs 24000 contigs of 250 bp + 3000 of 2 kb (reads come from many_contigs_reads.fa = the 2 kb ones only)"""
import numpy as np, os, sys
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
rng = np.random.default_rng(5)
def rnd(n, gc):
    return rng.choice(np.frombuffer(b'ACGT', np.uint8), size=n, p=[(1 - gc) / 2, gc / 2, gc / 2, (1 - gc) / 2])
def mutate(s, rate):
    s = s.copy(); m = rng.random(len(s)) < rate; s[m] = rng.choice(np.frombuffer(b'ACGT', np.uint8), size=int(m.sum())); return s
def paste(g, s):
    p = int(rng.integers(0, len(g) - len(s))); g[p:p + len(s)] = s
def write(name, chroms):
    with open(f'{out}/{name}.fa', 'wb') as f:
        for i, c in enumerate(chroms): f.write(b'>chr%d\n' % (i + 1) + c.tobytes() + b'\n')
    print(name, sum(len(c) for c in chroms), 'bases', len(chroms), 'contigs')
# ecoli_like
g = rnd(4_600_000, .51); rr = rnd(5000, .52); is_ = [rnd(1300, .5) for _ in range(4)]
for _ in range(7): paste(g, mutate(rr, .001))
for _ in range(30): paste(g, mutate(is_[int(rng.integers(4))], .002))
write('ecoli_like', [g])
# yeast_like
sizes = np.linspace(200_000, 1_500_000, 16).astype(int); ty = rnd(6000, .39); cs = []
for n in sizes:
    c = rnd(int(n), .38); tel = np.frombuffer((b'CCCACACACC' * 3000)[:30000], np.uint8)
    c[:30000] = tel; c[-30000:] = tel[::-1]; cs.append(c)
for _ in range(50): paste(cs[int(rng.integers(16))], mutate(ty, .01))
write('yeast_like', cs)
# at_rich
cs = [rnd(4_000_000, .20) for _ in range(5)]
for c in cs:
    for _ in range(3000):
        u = rnd(int(rng.integers(1, 5)), .1); paste(c, np.tile(u, int(rng.integers(10, 60)) // len(u) + 1))
write('at_rich', cs)
write('gc_rich', [rnd(n, .70) for n in (4_000_000, 3_500_000, 2_500_000)])
# plant_like
cs = [rnd(6_000_000, .36) for _ in range(5)]; sat = rnd(180, .35); fam = [rnd(300, .4) for _ in range(30)]
for c in cs:
    a = np.concatenate([mutate(sat, .10) for _ in range(2800)]); c[2_000_000:2_000_000 + len(a)] = a
    for _ in range(3000): paste(c, mutate(fam[int(rng.integers(30))], .1))
write('plant_like', cs)
u = rnd(2000, .5); write('unit_repeat', [np.concatenate([mutate(u, .01) for _ in range(2500)])])
big = [rnd(2000, .45) for _ in range(3000)]
with open(f'{out}/many_contigs.fa', 'wb') as f, open(f'{out}/many_contigs_reads.fa', 'wb') as r:
    for i in range(24000): f.write(b'>tiny%d\n' % i + rnd(250, .45).tobytes() + b'\n')
    for i, c in enumerate(big):
        for o in (f, r): o.write(b'>chr%d\n' % i + c.tobytes() + b'\n')
