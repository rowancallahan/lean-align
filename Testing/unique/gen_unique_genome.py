#!/usr/bin/env python3
"""Random genome in which every K-mer (K odd) occurs once on both strands.   gen_unique_genome.py OUT.fa [SEED]
Greedy walk: each next base is drawn at random among those whose new K-mer (and so its reverse
complement) is still unused; a dead end (all four used) aborts. K-mers do not span chromosomes."""
import random, sys
K = 15
LENGTHS = [1_200_000, 900_000, 800_000, 600_000, 500_000]   # 4.0 Mb, chrU1..chrU5
assert K % 2 == 1  # odd K: no K-mer is its own reverse complement
out, seed = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(seed)
mask = (1 << 2 * K) - 1
used = bytearray(1 << (2 * K - 3))   # bitmap over all 4^K codes
def test(x): return used[x >> 3] >> (x & 7) & 1
def mark(x): used[x >> 3] |= 1 << (x & 7)
seqs = []
for L in LENGTHS:
    s = [rng.randrange(4) for _ in range(K - 1)]
    f = r = 0
    for b in s: f = (f << 2 | b) & mask; r = r >> 2 | (3 - b) << 2 * (K - 1)
    for _ in range(L - K + 1):
        order = [0, 1, 2, 3]; rng.shuffle(order)
        for b in order:
            nf = (f << 2 | b) & mask; nr = r >> 2 | (3 - b) << 2 * (K - 1)
            if not test(nf): break
        else:
            sys.exit("dead end")
        assert nf != nr and not test(nr)
        mark(nf); mark(nr); f, r = nf, nr; s.append(b)
    seqs.append("".join("ACGT"[b] for b in s))
with open(out, "w") as fh:
    for i, q in enumerate(seqs):
        fh.write(f">chrU{i+1}\n")
        for j in range(0, len(q), 60): fh.write(q[j:j+60] + "\n")
