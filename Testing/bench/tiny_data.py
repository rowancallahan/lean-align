#!/usr/bin/env python3
"""Small test data with a known answer.   tiny_data.py OUTDIR
Writes OUTDIR/genome.fa, reads_R1.fq.gz, reads_R2.fq.gz. No download.

1. Genome: 4 Mb in 5 chromosomes, random, but every 15-letter word occurs once on both strands
   (each next letter is drawn among those whose new word and its reverse complement are unused).
2. Pairs: every 40 letters a fragment of about 400 starts; it gives two pairs, one per orientation, 2x150,
   all qualities 'I', with 0-2 substitutions per mate. The name holds the true position.
3. Pairs our adapter rule would cut are left out (the adapter AGATCGGAAGAGC with at most 1 mismatch, or its
   first 6+ letters at the read's end; Spec/Trim.lean `cut`). minibwa does not cut, so those would differ.
On this data both tools must give the same alignment for every pair."""
import gzip, random, sys
out = sys.argv[1]
K, LENGTHS, RL, STEP = 15, [1_200_000, 900_000, 800_000, 600_000, 500_000], 150, 40

# 1. genome
rng = random.Random(1)
mask = (1 << 2 * K) - 1
used = bytearray(1 << (2 * K - 3))                       # one bit per 15-letter word
def seen(x): return used[x >> 3] >> (x & 7) & 1
def mark(x): used[x >> 3] |= 1 << (x & 7)
chroms = {}
for i, L in enumerate(LENGTHS):
    s = [rng.randrange(4) for _ in range(K - 1)]
    f = r = 0                                            # the current word, forward and reverse complement
    for b in s: f = (f << 2 | b) & mask; r = r >> 2 | (3 - b) << 2 * (K - 1)
    for _ in range(L - K + 1):
        order = [0, 1, 2, 3]; rng.shuffle(order)
        for b in order:
            nf = (f << 2 | b) & mask; nr = r >> 2 | (3 - b) << 2 * (K - 1)
            if not seen(nf): break
        else: sys.exit("dead end")
        assert nf != nr and not seen(nr)
        mark(nf); mark(nr); f, r = nf, nr; s.append(b)
    chroms[f"chrU{i + 1}"] = "".join("ACGT"[b] for b in s)
with open(out + "/genome.fa", "w") as fh:
    for name, s in chroms.items():
        fh.write(f">{name}\n")
        for j in range(0, len(s), 60): fh.write(s[j:j + 60] + "\n")

# 2. and 3. pairs
rng = random.Random(7)
ADAPTER = "AGATCGGAAGAGC"
def is_cut(read):
    for i in range(len(read)):
        rest = read[i:]
        if len(rest) >= len(ADAPTER):
            if sum(a != b for a, b in zip(ADAPTER, rest)) <= 1: return True
        elif len(rest) >= 6 and rest == ADAPTER[:len(rest)]: return True
    return False
def rc(s): return s[::-1].translate(str.maketrans("ACGT", "TGCA"))
def mutate(read, n):
    read = list(read)
    for p in rng.sample(range(20, RL - 20), n):
        read[p] = rng.choice([b for b in "ACGT" if b != read[p]])
    return "".join(read)
SUBS = [(0, 0), (1, 1), (2, 2), (1, 0), (0, 2), (2, 1)]
n = kept = 0
with gzip.open(out + "/reads_R1.fq.gz", "wt", compresslevel=1) as f1, gzip.open(out + "/reads_R2.fq.gz", "wt", compresslevel=1) as f2:
    for c, s in chroms.items():
        for start in range(0, len(s) - 500, STEP):
            F = min(500, max(300, round(rng.gauss(400, 40))))
            frag = s[start:start + F]
            for strand in "+-":
                a, b = (frag[:RL], rc(frag[-RL:])) if strand == "+" else (rc(frag)[:RL], rc(rc(frag)[-RL:]))
                e1, e2 = SUBS[n % len(SUBS)]
                a, b = mutate(a, e1), mutate(b, e2)
                q = f"u{n}_{c}_{start}_{F}_{strand}_{e1}_{e2}"
                n += 1
                if is_cut(a) or is_cut(b): continue
                f1.write(f"@{q}/1\n{a}\n+\n{'I' * RL}\n"); f2.write(f"@{q}/2\n{b}\n+\n{'I' * RL}\n")
                kept += 1
print(f"{kept} pairs written, {n - kept} left out (adapter rule)")
