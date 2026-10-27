#!/usr/bin/env python3
"""Simulated 2x150 TruSeq pairs that read into adapter and have low-quality tails.
   python3 scripts/sim_adapter.py <genome.fa> <out_prefix> <n_pairs> [seed=1]
Fragment length uniform in [80, 400]; mate 1 = fragment start, mate 2 = reverse
complement of the fragment end; past the fragment each mate reads adapter
(R1: AGATCGGAAGAGCACACGTCTGAACTCCAGTCA..., R2: AGATCGGAAGAGCGTCGTGTAGGGAAAGAGTGT...)
then random bases.  Qualities 'I' (Q40), last L in [0, 40] positions '#' (Q2) with
some N there; 0.2% substitutions in the Q40 part.
Writes <prefix>_R1.fq, _R2.fq (raw, for cutadapt) and <prefix>_E1.fq, _E2.fq: the
expected cut-and-trimmed mates (fragment part before the Q2 tail, all 'I'), for
mapping directly."""
import random, sys
fa, prefix, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
seq = "".join(l.strip() for l in open(fa) if not l.startswith(">")).upper()
A1 = "AGATCGGAAGAGCACACGTCTGAACTCCAGTCACACTTGAATCTCGTATGCCGTCTTCTGCTTG"
A2 = "AGATCGGAAGAGCGTCGTGTAGGGAAAGAGTGTAGATCTCGGTGGTCGCCGTATCATT"
RL = 150
comp = str.maketrans("ACGT", "TGCA")
rc = lambda s: s.translate(comp)[::-1]
rnd = lambda k: "".join(random.choice("ACGT") for _ in range(k))

def mate(frag, ad):
    r = (frag + ad + rnd(RL))[:RL]
    L = random.randint(0, 40)
    hq = RL - L
    r = list(r)
    for i in range(hq):
        if random.random() < 0.002: r[i] = random.choice([b for b in "ACGT" if b != r[i]])
    for i in range(hq, RL):
        if random.random() < 0.1: r[i] = "N"
    return "".join(r), "I" * hq + "#" * L, "".join(r[:min(hq, len(frag))])

outs = [open(f"{prefix}_{s}.fq", "w") for s in ("R1", "R2", "E1", "E2")]
k = 0
while k < n:
    F = random.randint(80, 400)
    p = random.randrange(len(seq) - F)
    frag = seq[p:p + F]
    if "N" in frag: continue
    if random.random() < 0.5: frag = rc(frag)
    k += 1
    r1, q1, e1 = mate(frag, A1)
    r2, q2, e2 = mate(rc(frag), A2)
    for o, s, q in ((outs[0], r1, q1), (outs[1], r2, q2), (outs[2], e1, "I" * len(e1)), (outs[3], e2, "I" * len(e2))):
        o.write(f"@s{k}\n{s}\n+\n{q}\n")
for o in outs: o.close()
