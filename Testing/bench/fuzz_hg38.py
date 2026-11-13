#!/usr/bin/env python3
"""Fuzz on hg38 against minibwa: is any claim in our SAM false?

    python3 Testing/bench/fuzz_hg38.py GENOME.fa OURS OURS.idx MINIBWA MB_INDEX DIR [PAIRS] [THREADS]

GENOME.fa  the genome both indexes were built from          OURS, OURS.idx    lean-align and its index
MINIBWA    the minibwa binary (commit c07de5c)              MB_INDEX          minibwa's index prefix
DIR        a work folder                                    PAIRS             pairs per seed (default 10000)

What it does:
 1. Simulates read pairs (2 x 150 letters) from the genome with known origin, for each of the three modes
    `mason`, `low`, `high` and each seed 1, 2, 3 (the models of Testing/benches/sim_pairs.py, written here with the
    Python standard library only, so the reads are not the same letters as that script's numpy random stream).
    mason: no variants; substitutions 0.5% / 1% / 3% at start / 66% / end of the read; 1-letter indels 0.01% per
           letter; fragment ~ N(300, 30).
    low:   per-position variants fixed by a hash of the position (1 SNP per 1000, 1 indel per 8000; hom or het);
           substitutions 0.1% / 0.3% / 1%; read indels 1-3 letters at 0.01%; fragment ~ N(400, 80).
    high:  as low with SNPs 1 per 100, indels 1 per 1000; substitutions 0.5% / 1% / 2.5%; read indels 0.05%.
 2. Maps each mode's pairs (all three seeds in one file) with both aligners.
 3. Checks the four hard rules below on every pair, with the spec's scoring (Spec/Alignment.lean: match 0,
    mismatch -4, a gap of k letters -(6 + 2k)) and the spec's proper pair (Spec/Mapping.lean, insert 100..1000):
      A: the AS of each mapped record equals the score recomputed from its CIGAR, its SEQ and the reference.
      B: on a mapped pair, the bound XB is at least AS1 + AS2 (the bound is not below the pair it reports).
      C: XB is at least the score, under our scoring, of minibwa's pair when that pair is proper (else the bound is false).
      D: when XU:Z:unique, minibwa's proper pair is not at another placement scoring >= ours, nor at the same
         placement scoring more.
    minibwa's alignment is rebuilt as an end-to-end alignment of our (trimmed) part of the read: soft-clipped letters
    inside that part continue the diagonal; a pair is skipped for C and D if the part is not found in minibwa's SEQ.
 4. Prints one line per mode, seed and rule ("HARD A: ...: count") and fails (exit 1) unless every count is 0.
"""
import math
import mmap
import os
import random
import re
import subprocess
import sys

assert len(sys.argv) >= 7, __doc__
GENOME, OURS, OURS_IDX, MINIBWA, MB_IDX, DIR = sys.argv[1:7]
PAIRS = int(sys.argv[7]) if len(sys.argv) > 7 else 10000
THREADS = sys.argv[8] if len(sys.argv) > 8 else "4"
os.makedirs(DIR, exist_ok=True)

MODES = ["mason", "low", "high"]
SEEDS = [1, 2, 3]
RULES = ["A: AS != recomputed score",
         "B: XB < AS1 + AS2",
         "C: XB below a minibwa proper pair score",
         "D: unique but minibwa has a proper pair elsewhere scoring >= ours"]

# ---------------------------------------------------------------------------------------------------------------
# The genome as a one-line FASTA (header line, then all letters of the chromosome on one line), read through mmap.

ONE_LINE = os.path.join(DIR, "genome.1l.fa")
if not os.path.exists(ONE_LINE):
    out = open(ONE_LINE + ".part", "w")
    first = True
    for line in open(GENOME):
        line = line.rstrip("\n")
        if line.startswith(">"):
            if not first:
                out.write("\n")
            out.write(line + "\n")
            first = False
        else:
            out.write(line)
    out.write("\n")
    out.close()
    os.rename(ONE_LINE + ".part", ONE_LINE)

genome_file = open(ONE_LINE, "rb")
G = mmap.mmap(genome_file.fileno(), 0, access=mmap.ACCESS_READ)
CHROMS = []          # (name, offset of the first letter, length), in file order
CHROM_AT = {}        # name -> (offset, length)
i = 0
while i < len(G):
    j = G.find(b"\n", i)
    name = G[i + 1:j].split()[0].decode()
    k = G.find(b"\n", j + 1)
    if k < 0:
        k = len(G)
    CHROMS.append((name, j + 1, k - j - 1))
    CHROM_AT[name] = (j + 1, k - j - 1)
    i = k + 1
assert len(CHROMS) > 0


def reference(chrom, a, b):
    """Letters [a, b) of a chromosome, or None if that is outside it."""
    offset, length = CHROM_AT[chrom]
    if 0 <= a <= b <= length:
        return G[offset + a:offset + b].decode()
    return None


COMPLEMENT = {"A": "T", "C": "G", "G": "C", "T": "A", "N": "N"}


def reverse_complement(s):
    out = []
    for c in reversed(s):
        out.append(COMPLEMENT[c])
    return "".join(out)


# ---------------------------------------------------------------------------------------------------------------
# 1. Simulation

RL = 150         # read length
PAD = 60         # extra reference letters taken after the fragment (room for deletions)
M64 = 0x9E3779B97F4A7C15
MASK64 = (1 << 64) - 1


def interpolate(x, xs, ys):
    """Piecewise-linear y at x, for increasing xs."""
    k = 0
    while k + 1 < len(xs) and x > xs[k + 1]:
        k = k + 1
    if k + 1 == len(xs):
        return ys[-1]
    t = (x - xs[k]) / (xs[k + 1] - xs[k])
    return ys[k] + t * (ys[k + 1] - ys[k])


def clip(v, lo, hi):
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v


class Simulator:
    def __init__(self, mode, seed):
        params = {"mason": (0.0, 0.0, 0.005, 0.01, 0.03, 1e-4, 300, 30),
                  "low": (1e-3, 1.25e-4, 0.001, 0.003, 0.01, 1e-4, 400, 80),
                  "high": (1e-2, 1e-3, 0.005, 0.01, 0.025, 5e-4, 400, 80)}
        self.mode = mode
        self.snp, self.ind, s0, sm, s1, self.d, self.insert_mean, self.insert_sd = params[mode]
        self.rng = random.Random(seed)
        self.sub_rate = []        # substitution rate by position in the read
        self.q_match = []         # quality mean / sd for a correct letter, and for an error (mason)
        self.q_match_sd = []
        self.q_error = []
        self.q_error_sd = []
        for p in range(RL):                                   # read() uses positions 0 .. RL - 1 only
            x = p / (RL - 1)
            self.sub_rate.append(interpolate(x, [0, 0.66, 1], [s0, sm, s1]))
            self.q_match.append(interpolate(x, [0, 1], [40, 39.5]))
            self.q_match_sd.append(interpolate(x, [0, 1], [0.05, 10]))
            self.q_error.append(interpolate(x, [0, 1], [40, 30]))
            self.q_error_sd.append(interpolate(x, [0, 1], [3, 15]))
        total = 0
        for c in CHROMS:
            total = total + c[2]
        self.weights = []
        for c in CHROMS:
            self.weights.append(c[2] / total)

    def haplotype(self, c, p, seq, h):
        """The fixed variants of reference [p, p + len(seq)) on haplotype h (decided by a hash of each position, so
        every read of a locus sees the same alleles). Returns the haplotype letters and its segments
        (haplotype start, reference offset) for finding reference coordinates."""
        parts = []
        segments = []
        cur = 0
        hp = 0
        if self.snp + self.ind > 0:
            v = 0
            while v < len(seq):
                x = ((p + v + (c << 40)) * M64) & MASK64
                x = x ^ (x >> 29)
                x = (x * M64) & MASK64
                u = (x >> 11) / 2.0 ** 53
                if u < self.snp + self.ind and v >= cur:
                    b = x & 0xffff
                    if b % 3 in (0, 1 + h):                       # genotype: hom, het on haplotype 0, het on 1
                        parts.append(seq[cur:v])
                        segments.append((hp, cur))
                        hp = hp + v - cur
                        cur = v
                        segments.append((hp, cur))
                        if u < self.snp:
                            parts.append("ACGT"[("ACGT".index(seq[v]) + 1 + (b >> 2) % 3) % 4])
                            hp = hp + 1
                            cur = cur + 1
                        else:
                            k = 1 + (b >> 4) % 3
                            if (b >> 6) & 1:                      # insertion of k letters after this one
                                inserted = ""
                                for t in range(k):
                                    inserted = inserted + "ACGT"[(b >> (8 + 2 * t)) & 3]
                                parts.append(seq[v] + inserted)
                                hp = hp + 1 + k
                                cur = cur + 1
                            else:                                 # deletion of the k letters after this one
                                parts.append(seq[v])
                                hp = hp + 1
                                cur = cur + 1 + k
                v = v + 1
        parts.append(seq[cur:])
        segments.append((hp, cur))
        return "".join(parts), segments

    def read(self, src):
        """One read of RL letters from src (longer than RL), with errors and qualities; also the number of source
        letters under the read."""
        rng = self.rng
        out = []
        q = []
        j = 0
        i = 0
        while len(out) < RL:
            if self.mode == "mason":
                good = int(clip(round(self.q_match[i] + rng.gauss(0, 1) * self.q_match_sd[i]), 2, 40))
                bad = int(clip(round(self.q_error[i] + rng.gauss(0, 1) * self.q_error_sd[i]), 2, 40))
            else:
                x = i / (RL - 1)
                good = int(clip(round(37 - 7 * x * x + rng.gauss(0, 1.5)), 26, 41))
                bad = rng.randint(2, 15)
            if rng.random() < self.d:                             # an indel in the read
                k = 1 if self.mode == "mason" else rng.randint(1, 3)
                if rng.random() < 0.5:
                    for t in range(k):
                        out.append(rng.choice("ACGT"))
                        q.append(bad)
                else:
                    j = j + k
            if rng.random() < self.sub_rate[i]:
                choices = []
                for b in "ACGT":
                    if b != src[j]:
                        choices.append(b)
                out.append(rng.choice(choices))
                q.append(bad)
            else:
                out.append(src[j])
                q.append(good)
            i = i + 1
            j = j + 1
        used = j - (len(out) - RL)
        quality = ""
        for v in q[:RL]:
            quality = quality + chr(33 + v)
        return "".join(out[:RL]), quality, used


def reference_position(segments, hi):
    """The reference offset of haplotype offset hi (hi >= 0)."""
    assert hi >= 0
    best = None
    for h, r in segments:
        if h <= hi:
            value = r + hi - h
            if best is None or value > best:
                best = value
    return best


def simulate(mode, seed, n, prefix, out1, out2):
    sim = Simulator(mode, seed)
    rng = sim.rng
    made = 0
    while made < n:
        c = rng.choices(range(len(CHROMS)), weights=sim.weights)[0]
        name, offset, length = CHROMS[c]
        L = int(min(900, max(RL + 20, round(rng.gauss(sim.insert_mean, sim.insert_sd)))))
        if length - L - PAD <= 0:
            continue
        p = rng.randrange(0, length - L - PAD)
        seq = G[offset + p:offset + p + L + PAD].decode().upper()
        if "N" in seq:
            continue
        hap, segments = sim.haplotype(c, p, seq, rng.randint(0, 1))
        if len(hap) < L + 10:
            continue
        fwd = sim.read(hap[:RL + 20])
        rev = sim.read(reverse_complement(hap[L - RL - 20:L]))
        tf = str(p + reference_position(segments, 0)) + "-" + str(p + reference_position(segments, fwd[2] - 1) + 1) + "+"
        tr = str(p + reference_position(segments, L - rev[2])) + "-" + str(p + reference_position(segments, L - 1) + 1) + "-"
        if rng.random() < 0.5:
            m1, m2, truth = fwd, rev, tf + ":" + tr
        else:
            m1, m2, truth = rev, fwd, tr + ":" + tf
        read_name = prefix + "s" + str(made) + ":" + name + ":" + truth
        out1.write("@" + read_name + "\n" + m1[0] + "\n+\n" + m1[1] + "\n")
        out2.write("@" + read_name + "\n" + m2[0] + "\n+\n" + m2[1] + "\n")
        made = made + 1


# ---------------------------------------------------------------------------------------------------------------
# 3. The rules

def load_sam(path):
    """(read name, mate 1 or 2) -> the fields we need; secondary and supplementary records are left out."""
    records = {}
    for line in open(path):
        if line.startswith("@"):
            continue
        f = line.rstrip("\n").split("\t")
        flag = int(f[1])
        if flag & 0x900:
            continue
        tags = {}
        for t in f[11:]:
            tags[t[:2]] = t[5:]
        mate = 1 if flag & 64 else 2
        records[(f[0], mate)] = {"chr": f[2], "pos": int(f[3]) - 1, "cigar": f[5], "seq": f[9],
                                 "tags": tags, "mapped": not (flag & 4), "rev": bool(flag & 16)}
    return records


def cigar_ops(cigar):
    ops = []
    for count, op in re.findall(r"(\d+)([MIDSHX=])", cigar):
        ops.append((int(count), op))
    return ops


def columns_of(cigar, pos):
    """The alignment columns: ('d', read index, reference position), ('I', read index, None), ('D', None, reference
    position). Soft-clipped letters continue the diagonal."""
    ops = cigar_ops(cigar)
    out = []
    r = pos
    i = 0
    if ops and ops[0][1] == "S":
        n = ops[0][0]
        for j in range(n):
            out.append(("d", j, pos - n + j))
        i = n
        ops = ops[1:]
    tail = 0
    if ops and ops[-1][1] == "S":
        tail = ops[-1][0]
        ops = ops[:-1]
    for n, op in ops:
        for _ in range(n):
            if op in "M=X":
                out.append(("d", i, r))
                i = i + 1
                r = r + 1
            elif op == "I":
                out.append(("I", i, None))
                i = i + 1
            elif op == "D":
                out.append(("D", None, r))
                r = r + 1
    for j in range(tail):
        out.append(("d", i + j, r + j))
    return out


def score_of(chrom, letters, columns):
    """The spec's score of these columns (match 0, mismatch -4, gap opening -8, gap extension -2); None if the
    columns leave the chromosome."""
    rs = []
    for kind, ri, rr in columns:
        if rr is not None:
            rs.append(rr)
    lo = min(rs) if rs else 0
    X = reference(chrom, lo, max(rs) + 1) if rs else ""
    if X is None:
        return None
    s = 0
    prev = None
    for kind, ri, rr in columns:
        if kind == "d":
            s = s + (0 if letters[ri] == X[rr - lo] else -4)
            prev = "d"
        else:
            s = s + (-2 if prev == kind else -8)
            prev = kind
    return s


def span_of(columns):
    rs = []
    for kind, ri, rr in columns:
        if rr is not None:
            rs.append(rr)
    if not rs:
        return None
    return (min(rs), max(rs) + 1)


def is_proper(a, b):
    """a, b = (chromosome, start, stop, reverse?): the spec's proper pair, insert 100..1000, slack 0."""
    if a[0] != b[0] or a[3] == b[3]:
        return False
    if not a[3]:
        f, r = a, b
    else:
        f, r = b, a
    return f[1] <= r[2] and 100 <= r[2] - f[1] <= 1000 and f[1] <= r[1] and f[2] <= r[2]


def minibwa_window(o, m):
    """minibwa's alignment restricted to OUR part of the read: (columns, minibwa's SEQ), or None."""
    if o["seq"] == "*" or not m["mapped"] or m["seq"] == "*":
        return None
    as_read = reverse_complement(o["seq"]) if (o["mapped"] and o["rev"]) else o["seq"]
    want = reverse_complement(as_read) if m["rev"] else as_read
    t0 = m["seq"].find(want)
    if t0 < 0:
        return None
    all_columns = columns_of(m["cigar"], m["pos"])
    inside = []
    for k in range(len(all_columns)):
        ri = all_columns[k][1]
        if ri is not None and t0 <= ri < t0 + len(want):
            inside.append(k)
    if not inside:
        return None
    sub = []
    for c in all_columns[inside[0]:inside[-1] + 1]:
        if c[0] == "D" or (c[1] is not None and t0 <= c[1] < t0 + len(want)):
            sub.append(c)
    return sub, m["seq"]


def check_rules(ours_sam, mb_sam, counts_by_seed):
    ours = load_sam(ours_sam)
    mb = load_sam(mb_sam)
    assert set(ours.keys()) == set(mb.keys()), "the two SAM files have different reads"
    names = []
    seen = set()
    for name, mate in ours:
        if name not in seen:
            seen.add(name)
            names.append(name)
    for name in names:
        seed = int(name[1:name.index("_")])                 # names start with x<seed>_
        counts = counts_by_seed[seed]
        O = {1: ours[(name, 1)], 2: ours[(name, 2)]}
        M = {1: mb[(name, 1)], 2: mb[(name, 2)]}
        # A: AS of each mapped record = the recomputed score
        for k in (1, 2):
            o = O[k]
            if o["mapped"]:
                s = score_of(o["chr"], o["seq"], columns_of(o["cigar"], o["pos"]))
                if s is None or s != int(o["tags"]["AS"]):
                    counts[RULES[0]] = counts[RULES[0]] + 1
        if "XB" not in O[1]["tags"]:
            continue                                        # a pair with a trimmed-away mate carries no bound
        xb = int(O[1]["tags"]["XB"])
        # B: the bound is not below the reported pair
        if O[1]["mapped"] and O[2]["mapped"] and xb < int(O[1]["tags"]["AS"]) + int(O[2]["tags"]["AS"]):
            counts[RULES[1]] = counts[RULES[1]] + 1
        # C and D: minibwa's pair, rebuilt on our part of the reads, under our scoring
        W1 = minibwa_window(O[1], M[1])
        W2 = minibwa_window(O[2], M[2])
        if W1 is None or W2 is None or M[1]["chr"] != M[2]["chr"]:
            continue
        s1 = score_of(M[1]["chr"], W1[1], W1[0])
        s2 = score_of(M[2]["chr"], W2[1], W2[0])
        sp1 = span_of(W1[0])
        sp2 = span_of(W2[0])
        if s1 is None or s2 is None or sp1 is None or sp2 is None:
            continue
        mb_pair = [(M[1]["chr"], sp1[0], sp1[1], M[1]["rev"]), (M[2]["chr"], sp2[0], sp2[1], M[2]["rev"])]
        if not is_proper(mb_pair[0], mb_pair[1]):
            continue
        total = s1 + s2
        if total > xb:
            counts[RULES[2]] = counts[RULES[2]] + 1
        if O[1]["tags"].get("XU") == "unique" and O[1]["mapped"] and O[2]["mapped"]:
            ours_pair = []
            for k in (1, 2):
                sp = span_of(columns_of(O[k]["cigar"], O[k]["pos"]))
                ours_pair.append((O[k]["chr"], sp[0], sp[1], O[k]["rev"]))
            ours_score = int(O[1]["tags"]["AS"]) + int(O[2]["tags"]["AS"])
            if (mb_pair == ours_pair and total > ours_score) or (mb_pair != ours_pair and total >= ours_score):
                counts[RULES[3]] = counts[RULES[3]] + 1


# ---------------------------------------------------------------------------------------------------------------
# Run

all_zero = True
for mode in MODES:
    r1 = os.path.join(DIR, "all_" + mode + "_R1.fq")
    r2 = os.path.join(DIR, "all_" + mode + "_R2.fq")
    out1 = open(r1, "w")
    out2 = open(r2, "w")
    for seed in SEEDS:
        simulate(mode, seed, PAIRS, "x" + str(seed) + "_", out1, out2)
    out1.close()
    out2.close()
    ours_sam = os.path.join(DIR, "ours_" + mode + ".sam")
    mb_sam = os.path.join(DIR, "mb_" + mode + ".sam")
    subprocess.run([OURS, "map", OURS_IDX, r1, r2, ours_sam, "100", "1000"], check=True)
    mb_out = open(mb_sam, "w")
    mb_err = open(os.path.join(DIR, "mb_" + mode + ".err"), "w")
    subprocess.run([MINIBWA, "map", "-t", THREADS, MB_IDX, r1, r2], stdout=mb_out, stderr=mb_err, check=True)
    mb_out.close()
    mb_err.close()
    counts_by_seed = {}
    for seed in SEEDS:
        counts_by_seed[seed] = {}
        for rule in RULES:
            counts_by_seed[seed][rule] = 0
    check_rules(ours_sam, mb_sam, counts_by_seed)
    for seed in SEEDS:
        print("--- " + mode + " seed " + str(seed))
        for rule in RULES:
            print("  HARD " + rule + ": " + str(counts_by_seed[seed][rule]))
            if counts_by_seed[seed][rule] != 0:
                all_zero = False

assert all_zero, "a hard rule is not 0 (see the HARD lines above)"
print("FUZZ PASSED: rules A-D are 0 for every mode and seed")
