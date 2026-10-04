#!/usr/bin/env python3
"""Forward-strand reads from a one-line FASTA, with Illumina-like errors.
   python3 scripts/sim_reads.py <genome.fa> <out_prefix> <n_reads> [read_len=100] [err=0.005] [indel_frac=0.1] [seed=1]
Each base: substitution with prob err*(1-indel_frac); insertion or deletion
(length 1 + geometric(0.3)) with prob err*indel_frac/2 each.  Reads touching N
are redrawn.  Writes <prefix>.reads.txt (>name / seq lines, the Lean format),
<prefix>.fq (for minibwa), <prefix>.truth.tsv."""
import random, sys
fa, prefix, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
RL = int(sys.argv[4]) if len(sys.argv) > 4 else 100
err = float(sys.argv[5]) if len(sys.argv) > 5 else 0.005
ifrac = float(sys.argv[6]) if len(sys.argv) > 6 else 0.1
random.seed(int(sys.argv[7]) if len(sys.argv) > 7 else 1)
chrs, name = [], None
for line in open(fa):
    line = line.strip()
    if line.startswith(">"): name = line[1:].split()[0]
    elif line: chrs.append((name, line.upper()))
assert chrs and all(len(s) > RL + 50 for _, s in chrs)
glen = lambda: 1 + (int(random.expovariate(0.3)) if random.random() < 0.3 else 0)
with open(prefix + ".reads.txt", "w") as fr, open(prefix + ".fq", "w") as fq, open(prefix + ".truth.tsv", "w") as ft:
    ft.write("read\tchromosome\tposition_1based\tedits\n")
    i = 0
    while i < n:
        cname, seq = random.choice(chrs)
        pos = random.randrange(0, len(seq) - RL - 40)
        if "N" in seq[pos:pos + RL + 40]: continue
        r, j, edits = [], pos, []
        while len(r) < RL:
            u = random.random()
            if u < err * (1 - ifrac):
                r.append(random.choice([b for b in "ACGT" if b != seq[j]])); j += 1; edits.append("X")
            elif u < err * (1 - ifrac / 2):
                L = glen(); r.extend(random.choice("ACGT") for _ in range(L)); edits.append("I%d" % L)
            elif u < err:
                L = glen(); j += L; edits.append("D%d" % L)
            else:
                r.append(seq[j]); j += 1
        r = "".join(r[:RL])
        i += 1
        fr.write(">r%d\n%s\n" % (i, r))
        fq.write("@r%d\n%s\n+\n%s\n" % (i, r, "I" * RL))
        ft.write("r%d\t%s\t%d\t%s\n" % (i, cname, pos + 1, ",".join(edits) or "-"))
