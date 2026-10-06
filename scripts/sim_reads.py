#!/usr/bin/env python3
"""Forward-strand reads from a one-line FASTA, with Illumina-like errors.
   python3 scripts/sim_reads.py <genome.fa> <out_prefix> <n_reads> [read_len=100] [err=0.005] [indel_frac=0.1] [seed=1]
Each base: substitution with prob err*(1-indel_frac); insertion or deletion
(length 1 + geometric(0.3)) with prob err*indel_frac/2 each.  Reads touching N
are redrawn.  Writes <prefix>.reads.txt (>name / seq lines, the Lean format),
<prefix>.fq (for minibwa), <prefix>.truth.tsv.
SIM_BOTH=1: each read is reverse-complemented with probability 1/2 and the truth
gets a strand column (+/-); without it the output is unchanged (forward only).
SIM_PAIRED=1 [INSERT_MEAN=350 INSERT_SD=50]: n read pairs, see the paired branch."""
import os, random, sys
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

if os.environ.get("SIM_PAIRED") == "1":
    # Pairs: fragment of length ~ N(INSERT_MEAN, INSERT_SD) from either strand; the
    # forward mate reads the fragment start, the reverse mate is the reverse complement
    # of a read at the fragment end.  Writes <prefix>_1/_2.reads.txt, _1/_2.fq and
    # <prefix>.truth.tsv (0-based-1 positions and strands of both mates).
    mean, sd = float(os.environ.get("INSERT_MEAN", "350")), float(os.environ.get("INSERT_SD", "50"))
    comp = str.maketrans("ACGT", "TGCA")
    def fwd_read(seq, j):
        r = []
        while len(r) < RL:
            u = random.random()
            if u < err * (1 - ifrac): r.append(random.choice([b for b in "ACGT" if b != seq[j]])); j += 1
            elif u < err * (1 - ifrac / 2): r.extend(random.choice("ACGT") for _ in range(glen()))
            elif u < err: j += glen()
            else: r.append(seq[j]); j += 1
        return "".join(r[:RL])
    with open(prefix + "_1.reads.txt", "w") as f1, open(prefix + "_2.reads.txt", "w") as f2, \
         open(prefix + "_1.fq", "w") as q1, open(prefix + "_2.fq", "w") as q2, open(prefix + ".truth.tsv", "w") as ft:
        ft.write("pair\tchromosome\tpos1_1based\tstrand1\tpos2_1based\tstrand2\n")
        i = 0
        while i < n:
            cname, seq = random.choice(chrs)
            F = max(RL, int(random.gauss(mean, sd)))
            pos = random.randrange(0, len(seq) - F - 40)
            if "N" in seq[pos:pos + F + 40]: continue
            a, b = fwd_read(seq, pos), fwd_read(seq, pos + F - RL).translate(comp)[::-1]
            if random.random() < 0.5: m1, m2, t = a, b, (pos + 1, "+", pos + F - RL + 1, "-")
            else: m1, m2, t = b, a, (pos + F - RL + 1, "-", pos + 1, "+")
            i += 1
            for f, q, m in ((f1, q1, m1), (f2, q2, m2)):
                f.write(">p%d\n%s\n" % (i, m)); q.write("@p%d\n%s\n+\n%s\n" % (i, m, "I" * RL))
            ft.write("p%d\t%s\t%d\t%s\t%d\t%s\n" % ((i, cname) + t))
    sys.exit(0)
with open(prefix + ".reads.txt", "w") as fr, open(prefix + ".fq", "w") as fq, open(prefix + ".truth.tsv", "w") as ft:
    both = os.environ.get("SIM_BOTH") == "1"
    ft.write("read\tchromosome\tposition_1based\tedits" + ("\tstrand" if both else "") + "\n")
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
        strand = "+"
        if both and random.random() < 0.5:
            r = r[::-1].translate(str.maketrans("ACGT", "TGCA")); strand = "-"
        i += 1
        fr.write(">r%d\n%s\n" % (i, r))
        fq.write("@r%d\n%s\n+\n%s\n" % (i, r, "I" * RL))
        ft.write("r%d\t%s\t%d\t%s%s\n" % (i, cname, pos + 1, ",".join(edits) or "-", "\t" + strand if both else ""))
