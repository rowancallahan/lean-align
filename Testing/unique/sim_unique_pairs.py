#!/usr/bin/env python3
"""Pairs sliding across the unique genome.   sim_unique_pairs.py GENOME.fa OUT_PREFIX [STEP] [SEED]
Every STEP bp a fragment starts (length ~N(400, 40) clipped to [300, 500]); each start gives two pairs, one per
orientation (R1 on the forward strand / R1 on the reverse strand). 2x150, all qualities 'I' (nothing trimmed).
Substitutions per mate cycle through (0,0) (1,1) (2,2) (1,0) (0,2) (2,1), always at read positions 20..129
(no indels, no clipping incentive). Name = u<n>_<chrom>_<fragstart0>_<fraglen>_<R1strand>_<subs1>_<subs2>."""
import random, sys
fa, out = sys.argv[1], sys.argv[2]
step = int(sys.argv[3]) if len(sys.argv) > 3 else 40
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 7)
RL = 150
chroms, name = {}, None
for line in open(fa):
    line = line.strip()
    if line.startswith(">"): name = line[1:]; chroms[name] = []
    else: chroms[name].append(line)
chroms = {k: "".join(v) for k, v in chroms.items()}
assert all(set(s) <= set("ACGT") for s in chroms.values())
rc = lambda s: s[::-1].translate(str.maketrans("ACGT", "TGCA"))
def mutate(r, n):
    r = list(r)
    for p in rng.sample(range(20, RL - 20), n):
        r[p] = rng.choice([b for b in "ACGT" if b != r[p]])
    return "".join(r)
SUBS = [(0, 0), (1, 1), (2, 2), (1, 0), (0, 2), (2, 1)]
n = 0
with open(out + "_R1.fq", "w") as f1, open(out + "_R2.fq", "w") as f2:
    for c, s in chroms.items():
        for start in range(0, len(s) - 500, step):
            F = min(500, max(300, round(rng.gauss(400, 40))))
            frag = s[start:start + F]
            for strand in "+-":
                a, b = (frag[:RL], rc(frag[-RL:])) if strand == "+" else (rc(frag)[:RL], rc(rc(frag)[-RL:]))
                e1, e2 = SUBS[n % len(SUBS)]
                a, b = mutate(a, e1), mutate(b, e2)
                q = f"u{n}_{c}_{start}_{F}_{strand}_{e1}_{e2}"
                f1.write(f"@{q}/1\n{a}\n+\n{'I' * RL}\n"); f2.write(f"@{q}/2\n{b}\n+\n{'I' * RL}\n")
                n += 1
print(n, "pairs")
