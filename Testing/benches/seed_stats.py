#!/usr/bin/env python3
"""Seed hit statistics on real reads against the whole-genome minimizer index (analysis only).

    python3 bench/seed_stats.py <index_prefix> <chroms.txt> <r1.fq> <r2.fq> <npairs> [skip]

Index: Mz k22 B26 c0 W5 t6 (bench/WholeGenome.lean format: .meta .offs .sl), memory-mapped.
For every mate (trimmed FASTQ, >= 100 letters) and both strands, and seed length L in LS:
m = n // L disjoint seeds at j * (n // m); for each seed the exact genome hits (all L letters
compared) found through the rarest of its 25-letter windows' minimizer buckets.
s = sbound(cap) = cap // 4 (cap 16 from 150 letters, 12 from 100); pigeonhole needs any s+1
of the m seeds.  Reported per scheme: hits summed over the s+1 seeds with fewest hits
(oracle), over the s+1 seeds with the smallest bucket (estimate), over all m seeds, and
bucket entries scanned.
"""
import sys, mmap, numpy as np, time

HC = 0x9E3779B97F4A7C15
M64 = (1 << 64) - 1
K, Q, W, T = 22, 25, 4, 6
KM = (1 << 44) - 1
TM = (1 << 12) - 1
KB = 18
CODE = np.full(256, 4, np.uint8)
for i, ch in enumerate(b"ACGT"): CODE[ch] = i
COMP = bytes.maketrans(b"ACGT", b"TGCA")

pre, chroms_txt, f1, f2, npairs = sys.argv[1:6]
skip = int(sys.argv[6]) if len(sys.argv) > 6 else 0
npairs = int(npairs)
MS = [int(x) for x in (sys.argv[7] if len(sys.argv) > 7 else "10,8,6,5").split(",")]
DEBUG = len(sys.argv) > 8

offs = np.memmap(pre + ".offs", dtype="<u4", mode="r")
slb = np.memmap(pre + ".sl", dtype=np.uint8, mode="r")

# genome: concatenation of the one-line FASTAs (global place = index place)
chroms = []
g0 = 0
for path in open(chroms_txt).read().split():
    f = open(path, "rb")
    mm = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
    h = mm.find(b"\n") + 1
    n = len(mm) - h
    if mm[len(mm) - 1:] == b"\n": n -= 1
    chroms.append((g0, mm, h, n))
    g0 += n
starts = np.array([c[0] for c in chroms], dtype=np.int64)

def gslice(p, n):
    i = int(np.searchsorted(starts, p, side="right")) - 1
    s, mm, h, cn = chroms[i]
    o = p - s
    if o + n > cn: return None
    return mm[h + o: h + o + n]

def bucket(b):
    lo, hi = int(offs[b]), int(offs[b + 1])
    return lo, hi

def entries(lo, hi):
    a = np.asarray(slb[5 * lo: 5 * hi]).reshape(-1, 5).astype(np.uint64)
    v = a[:, 0] | (a[:, 1] << 8) | (a[:, 2] << 16) | (a[:, 3] << 24) | (a[:, 4] << 32)
    return v >> np.uint64(8), v & np.uint64(255)

def hsh(x): return (x * HC) & KM

def seeds_info(R):
    """Per 25-window start p: (kpos, bucket, key) of its minimizer."""
    c = CODE[np.frombuffer(R, np.uint8)].astype(np.uint64)
    n = len(c)
    # 6-word hashes
    w6 = np.zeros(n - T + 1, np.uint64)
    for i in range(T): w6 = w6 * np.uint64(4) + c[i: n - T + 1 + i]
    h6 = (w6 * np.uint64(HC)) & np.uint64(TM)
    w22 = np.zeros(n - K + 1, np.uint64)
    for i in range(K): w22 = w22 * np.uint64(4) + c[i: n - K + 1 + i]
    nw = n - Q + 1
    idx = np.lib.stride_tricks.sliding_window_view(h6, Q + 1 - T)[:nw]
    x = np.argmin(idx, axis=1)   # leftmost least
    o = np.where(x < W, x, x % W)
    kpos = np.arange(nw) + o
    h = (w22[kpos] * np.uint64(HC)) & np.uint64(KM)
    return kpos, (h >> np.uint64(KB)).astype(np.int64), (h & np.uint64(255))

cache = {}
def lookup(R, a, L, info):
    """Exact hits of R[a, a+L) through its rarest window bucket: (diagonals, bucket size, key-matched entries)."""
    kpos, bk, key = info
    best = None
    for p in range(a, a + L - Q + 1):
        lo, hi = bucket(int(bk[p]))
        if best is None or hi - lo < best[0]: best = (hi - lo, p, lo, hi)
    sz, p, lo, hi = best
    pos, ky = entries(lo, hi)
    sel = pos[ky == key[p]].astype(np.int64)
    d = int(kpos[p]) - a
    seed = R[a: a + L]
    hits = []
    for g in sel:
        st = int(g) - d
        if st < 0: continue
        s = gslice(st, L)
        if s is not None and s == seed: hits.append(st - a)
    return hits, sz, len(sel)

def readfq(path):
    f = open(path, "rb")
    while True:
        h = f.readline()
        if not h: return
        s = f.readline().strip(); f.readline(); f.readline()
        yield s

def collect():
    """One line per mate and scheme: M n s, then per strand per seed: hits bucket keymatched ndiag-set."""
    t0 = time.time()
    r1, r2 = readfq(f1), readfq(f2)
    for _ in range(skip): next(r1); next(r2)
    out = sys.stdout
    for i in range(npairs):
        for mate, R in enumerate((next(r1), next(r2))):
            n = len(R)
            if n < 100 or any(ch not in b"ACGT" for ch in R): continue
            cap = 16 if n >= 150 else 12
            s = cap // 4
            infos = [(st, S, seeds_info(S)) for st, S in ((0, R), (1, R.translate(COMP)[::-1]))]
            for M in MS:
                m = min(M, n // Q)
                if m < s + 1: continue
                L = n // m
                rec = []
                for st, S, info in infos:
                    res = [lookup(S, j * L, L, info) for j in range(m)]
                    rec.append([(len(h), sz, km, sorted(set(h))) for h, sz, km in res])
                out.write(repr((i + skip, mate, M, n, s, L, rec)) + "\n")
    print(f"# {npairs} pairs, {time.time() - t0:.1f} s", file=sys.stderr)

collect()
