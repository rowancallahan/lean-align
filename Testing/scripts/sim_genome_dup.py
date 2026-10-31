#!/usr/bin/env python3
"""Synthetic genome for speed A/B runs (not for accuracy claims); sim_genome.py plus exact (~5%) and
near-exact (0.1-0.5% diverged, ~3%) segmental copies of 2-10 kb, as a stand-in for chr21's genuine
repeats (n29 danger-region tests: python3 Testing/scripts/sim_genome_dup.py <dir> 40 1 21).
   python3 Testing/scripts/sim_genome_dup.py <out_dir> [mb=8] [nchr=2] [seed=7]
Writes <out_dir>/chr<i>.fa (one record, one sequence line each, the format
whole_genome and sim_reads.py read) and <out_dir>/all.fa (all records).
Composition: uniform random ACGT, plus repeat families so that a few percent
of reads are repeat-heavy (where the mapper spends most of its time):
  * 40 interspersed families (300 bp, ~10% of the genome), copies 2-15% diverged;
  * 2000 recent segmental copies (1-5 kb, 0.5-2% diverged);
  * tandem arrays (unit 2-60 bp, 0.5-5 kb long), ~1% of the genome;
  * a few N runs (50-500 bp) so the non-ACGT fallbacks are exercised."""
import os, random, sys
out = sys.argv[1]
mb = float(sys.argv[2]) if len(sys.argv) > 2 else 8
nchr = int(sys.argv[3]) if len(sys.argv) > 3 else 2
random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 7)
assert mb > 0 and nchr >= 1
ACGT = "ACGT"
rnd = lambda n: "".join(random.choices(ACGT, k=n))

def mutate(s, rate):
    s = list(s)
    for i in range(len(s)):
        if random.random() < rate:
            u = random.random()
            if u < 0.9: s[i] = random.choice([b for b in ACGT if b != s[i]])
            elif u < 0.95: s[i] = ""
            else: s[i] = s[i] + random.choice(ACGT)
    return "".join(s)

def paste(g, pos, s):
    g[pos:pos + len(s)] = list(s[:len(g) - pos])

os.makedirs(out, exist_ok=True)
total = int(mb * 1e6)
lens = [total // nchr] * nchr
fams = [rnd(300) for _ in range(40)]
recs = []
for c in range(nchr):
    L = lens[c]
    g = list(rnd(L))
    for _ in range(int(0.10 * L / 300)):          # interspersed families
        paste(g, random.randrange(L - 400), mutate(random.choice(fams), random.uniform(0.02, 0.15)))
    for _ in range(int(2000 * L / total)):        # segmental duplications
        n = random.randint(1000, 5000)
        a, b = random.randrange(L - n), random.randrange(L - n - 100)
        paste(g, b, mutate("".join(g[a:a + n]), random.uniform(0.005, 0.02)))
    for _ in range(int(0.05 * L / 6000)):         # exact segmental copies (~5%)
        n = random.randint(2000, 10000)
        a, b = random.randrange(L - n), random.randrange(L - n - 100)
        paste(g, b, "".join(g[a:a + n]))
    for _ in range(int(0.03 * L / 6000)):         # near-exact copies 0.1-0.5% (~3%)
        n = random.randint(2000, 10000)
        a, b = random.randrange(L - n), random.randrange(L - n - 100)
        paste(g, b, mutate("".join(g[a:a + n]), random.uniform(0.001, 0.005)))
    for _ in range(int(0.01 * L / 2000)):         # tandem arrays
        u = rnd(random.randint(2, 60))
        n = random.randint(500, 5000)
        paste(g, random.randrange(L - n - 100), mutate((u * (n // len(u) + 1))[:n], 0.01))
    for _ in range(3):                            # N runs
        n = random.randint(50, 500)
        paste(g, random.randrange(L - n), "N" * n)
    s = "".join(g)[:L]
    assert len(s) == L
    recs.append((f"chr{c + 1}", s))
    with open(os.path.join(out, f"chr{c + 1}.fa"), "w") as f:
        f.write(f">chr{c + 1}\n{s}\n")
with open(os.path.join(out, "all.fa"), "w") as f:
    for name, s in recs: f.write(f">{name}\n{s}\n")
print(f"{out}: {nchr} chromosomes, {total} letters")
