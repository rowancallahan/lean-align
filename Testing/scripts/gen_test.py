#!/usr/bin/env python3
"""Random genome + reads with known origins.
   python3 scripts/gen_test.py <out_prefix> <n_chromosomes> <chromosome_length> <n_reads> [read_length] [seed]
Writes <prefix>.genome.txt, <prefix>.reads.txt, <prefix>.truth.tsv.  Forward strand only.
Each read gets 0-3 edits (mismatch, 1-base insertion, or 1-base deletion)."""
import random, sys
prefix, nchr, L, nreads = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
RL = int(sys.argv[5]) if len(sys.argv) > 5 else 100
random.seed(int(sys.argv[6]) if len(sys.argv) > 6 else 1)
chrs = [("chr%d" % (i + 1), "".join(random.choice("ACGT") for _ in range(L))) for i in range(nchr)]
sub = {"A": "C", "C": "G", "G": "T", "T": "A"}
with open(prefix + ".genome.txt", "w") as f:
    for c in chrs: f.write(">%s\n%s\n" % c)
with open(prefix + ".reads.txt", "w") as fr, open(prefix + ".truth.tsv", "w") as ft:
    ft.write("read\tchromosome\tposition_1based\tedits\n")
    for i in range(nreads):
        name, seq = random.choice(chrs)
        pos = random.randrange(0, L - RL - 4)
        r = list(seq[pos:pos + RL + 4])
        edits = []
        for _ in range(random.randrange(0, 4)):
            j = random.randrange(5, RL - 5)          # keep edits away from the ends
            kind = random.choice("XXID")
            if kind == "X": r[j] = sub[r[j]]
            elif kind == "I": r.insert(j, random.choice("ACGT"))
            else: del r[j]
            edits.append(kind)
        r = "".join(r[:RL])
        fr.write(">read%d\n%s\n" % (i + 1, r))
        ft.write("read%d\t%s\t%d\t%s\n" % (i + 1, name, pos + 1, "".join(edits) or "-"))
