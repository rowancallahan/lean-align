#!/usr/bin/env python3
"""Benchmark only.  Simulated 2x150 pairs from a one-line FASTA with known origin.
   python3 bench/sim_pairs.py <genome.1l.fa> <out_prefix> <n_pairs> mason|low|high [seed]
Writes <prefix>_R1.fq / _R2.fq.  Read name s<i>:<chrom>:<b1>-<e1><strand1>:<b2>-<e2><strand2>
(0-based half-open reference interval of each mate; both mates share the name).
mason: an approximation of mason v2.0.9 `--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5`
  (minibwa paper Fig 2a; mason itself is not used): no variants; mismatch rate 0.2/0.4/1.2% x 2.5
  at start / 66% / end of the read (linear between), insertion and deletion 0.005% per base (1 bp),
  qualities as mason's defaults (match ~N(40 -> 39.5, sd 0.05 -> 10), mismatch ~N(40 -> 30, sd 3 -> 15)),
  fragment ~ N(300, 30).
low / high: haplotype variants fixed per reference position (hash of the position, so all reads of a
  locus see the same alleles), genotype hom / het on haplotype 0 / 1, each fragment picks one haplotype;
  low: 1 SNP / 1000 bp, 1 indel (1-3 bp) / 8000 bp (HG002-like); high: 1/100 and 1/1000.  Substitutions
  0.1 -> 0.3 -> 1% (low) or 0.5 -> 1 -> 2.5% (high) with Phred 2-15 at error spots, else ~37 -> ~30;
  read indels 1-3 bp at 0.01% (low) / 0.05% (high) per base; fragment ~ N(400, 80).
Fragments are clamped to [170, 900]; windows with N are skipped."""
import mmap, random, sys
import numpy as np
fa, pre, N, mode = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
# SNP, indel rate on the haplotype; substitution rate at start, at 66%, at end; read indel rate; insert mean, sd
SNP, IND, S0, SM, S1, D, IM, ISD = {"mason": (0, 0, 0.005, 0.01, 0.03, 1e-4, 300, 30),
                                    "low": (1e-3, 1.25e-4, 0.001, 0.003, 0.01, 1e-4, 400, 80),
                                    "high": (1e-2, 1e-3, 0.005, 0.01, 0.025, 5e-4, 400, 80)}[mode]
RL, PAD = 150, 60
random.seed(seed)
rng = np.random.default_rng(seed)
f = open(fa, "rb")
G = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
chrom, i = [], 0
while i < len(G):
    j = G.find(b"\n", i); name = G[i + 1:j].split()[0].decode()
    k = G.find(b"\n", j + 1); k = len(G) if k < 0 else k
    chrom.append((name, j + 1, k - j - 1)); i = k + 1
W = np.array([c[2] for c in chrom], float); W /= W.sum()
RC = str.maketrans("ACGT", "TGCA")
rc = lambda s: s.translate(RC)[::-1]
M64 = np.uint64(0x9E3779B97F4A7C15)

def hap_of(c, p, seq, h):
    """Apply the fixed variants of reference [p, p+len(seq)) on haplotype h; returns the
    haplotype string and its segments (hap start, ref offset) for coordinate lookup."""
    x = (np.arange(p, p + len(seq), dtype=np.uint64) + np.uint64(c << 40)) * M64
    x ^= x >> np.uint64(29); x *= M64
    u = (x >> np.uint64(11)).astype(float) / 2.0 ** 53
    parts, segs, cur, hp = [], [], 0, 0
    for v in np.nonzero(u < SNP + IND)[0]:
        b = int(x[v] & np.uint64(0xffff))
        if v < cur or b % 3 not in (0, 1 + h): continue  # genotype: hom, het hap 0, het hap 1
        parts.append(seq[cur:v]); segs.append((hp, cur)); hp += v - cur; cur = v
        segs.append((hp, cur))
        if u[v] < SNP: parts.append("ACGT"[("ACGT".index(seq[v]) + 1 + (b >> 2) % 3) % 4]); hp += 1; cur += 1
        else:
            k = 1 + (b >> 4) % 3
            if (b >> 6) & 1: parts.append(seq[v] + "".join("ACGT"[(b >> (8 + 2 * t)) & 3] for t in range(k))); hp += 1 + k; cur += 1
            else: parts.append(seq[v]); hp += 1; cur += 1 + k
    parts.append(seq[cur:]); segs.append((hp, cur))
    return "".join(parts), segs

def refpos(segs, hi):
    return max(r + hi - h for h, r in segs if h <= hi) if hi >= 0 else 0

POS = np.arange(RL) / (RL - 1)
SUB = np.interp(POS, [0, 0.66, 1], [S0, SM, S1])
QM = np.interp(POS, [0, 1], [40, 39.5]); QS = np.interp(POS, [0, 1], [0.05, 10])     # mason match qualities
QME = np.interp(POS, [0, 1], [40, 30]); QSE = np.interp(POS, [0, 1], [3, 15])        # mason mismatch qualities

def read(src):
    """One read of RL letters from src (longer than RL), with errors and qualities."""
    out, q, j = [], [], 0
    sub = rng.random(RL + 10) < np.append(SUB, [S1] * 10)
    ind = rng.random(RL + 10) < D
    if mode == "mason":
        base = np.clip(np.round(np.append(QM, [39.5] * 10) + rng.normal(0, 1, RL + 10) * np.append(QS, [10] * 10)), 2, 40).astype(int)
        bad = np.clip(np.round(np.append(QME, [30] * 10) + rng.normal(0, 1, RL + 10) * np.append(QSE, [15] * 10)), 2, 40).astype(int)
    else:
        base = np.clip(np.round(37 - 7 * np.append(POS, [1] * 10) ** 2 + rng.normal(0, 1.5, RL + 10)), 26, 41).astype(int)
        bad = rng.integers(2, 16, RL + 10)
    i = 0
    while len(out) < RL:
        if ind[i]:
            k = 1 if mode == "mason" else random.randint(1, 3)
            if random.random() < 0.5: out += random.choices("ACGT", k=k); q += [int(bad[i])] * k
            else: j += k
        if sub[i]: out.append(random.choice([b for b in "ACGT" if b != src[j]])); q.append(int(bad[i]))
        else: out.append(src[j]); q.append(int(base[i]))
        i += 1; j += 1
    used = j - (len(out) - RL)          # source letters under the read (approximate past an insertion)
    return "".join(out[:RL]), "".join(chr(33 + v) for v in q[:RL]), used

o1, o2 = open(pre + "_R1.fq", "w"), open(pre + "_R2.fq", "w")
n = 0
while n < N:
    c = int(rng.choice(len(chrom), p=W)); name, off, ln = chrom[c]
    L = int(min(900, max(RL + 20, round(random.gauss(IM, ISD)))))
    p = random.randrange(0, ln - L - PAD)
    seq = G[off + p:off + p + L + PAD].decode().upper()
    if "N" in seq: continue
    hap, segs = hap_of(c, p, seq, random.randint(0, 1))
    if len(hap) < L + 10: continue
    fwd = read(hap[:RL + 20])
    rev = read(rc(hap[L - RL - 20:L]))
    tf = f"{p + refpos(segs, 0)}-{p + refpos(segs, fwd[2] - 1) + 1}+"
    tr = f"{p + refpos(segs, L - rev[2])}-{p + refpos(segs, L - 1) + 1}-"
    if random.random() < 0.5: m1, m2, t = fwd, rev, f"{tf}:{tr}"
    else: m1, m2, t = rev, fwd, f"{tr}:{tf}"
    nm = f"s{n}:{name}:{t}"
    o1.write(f"@{nm}\n{m1[0]}\n+\n{m1[1]}\n"); o2.write(f"@{nm}\n{m2[0]}\n+\n{m2[1]}\n")
    n += 1
