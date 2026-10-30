#!/usr/bin/env python3
"""Benchmark only (n29 danger regions).  Fraction of a genome inside an exact duplicated L-mer (L default
150; a copy on either strand counts; L-mers with N are ignored), and optionally the per-letter mask
(1 byte per letter, chromosomes concatenated) that whole_genome reads with WG_DANGER=<mask>.
   python3 Testing/benches/dup_mask.py genome.fa [L] [out.mask]
64-bit polynomial hashes: a collision would only over-mark (prototype; not a proof input)."""
import sys, numpy as np
fa = sys.argv[1]; L = int(sys.argv[2]) if len(sys.argv) > 2 else 150
seqs = []; cur = []
for line in open(fa, 'rb'):
    if line.startswith(b'>'):
        if cur: seqs.append(b''.join(cur)); cur = []
    else: cur.append(line.strip().upper())
if cur: seqs.append(b''.join(cur))
lut = np.full(256, 4, np.uint8)
for i, c in enumerate(b'ACGT'): lut[c] = i
B = np.uint64(1000003)
def hashes(code):
    # polynomial hash of every length-L window, by doubling; plus "has N" mask
    n = len(code); h = code.astype(np.uint64); bad = (code == 4).astype(np.int32)
    pw = {1: B}; cur_len = 1; hs = {1: h}
    while cur_len * 2 <= L:
        a = hs[cur_len]; m = len(a) - cur_len
        hs[cur_len * 2] = a[:m] * pw[cur_len] + a[cur_len:cur_len + m]
        pw[cur_len * 2] = pw[cur_len] * pw[cur_len]; cur_len *= 2
    res = None; rl = 0; rp = np.uint64(1)
    for k in sorted(hs, reverse=True):
        if rl + k <= L:
            part = hs[k]
            if res is None: res = part; rp = pw[k]
            else:
                m = min(len(res), len(part) - rl); res = res[:m] * pw[k] + part[rl:rl + m]
            rl += k
    nw = n - L + 1
    cs = np.concatenate([[0], np.cumsum(bad)]); ok = (cs[L:L + nw] - cs[:nw]) == 0
    return res[:nw], ok
tot = 0; cov = 0; allf = []; allok = []; masks = []
for s in seqs:
    code = lut[np.frombuffer(s, np.uint8)]
    rc = np.where(code == 4, 4, 3 - code)[::-1].copy()
    f, ok = hashes(code); r, okr = hashes(rc)
    allf.append((f, ok, r[::-1], okr[::-1], len(s)))
keys = np.concatenate([np.concatenate([f[ok], r[okr]]) for f, ok, r, okr, n in allf])
u, cnt = np.unique(keys, return_counts=True)
for f, ok, r, okr, n in allf:
    # forward L-mer i is duplicated if its hash occurs >= 2 times among forward+RC windows (palindromes aside)
    idx = np.searchsorted(u, f); c = cnt[np.minimum(idx, len(u) - 1)]
    dup = ok & (c >= 2) & (u[np.minimum(idx, len(u) - 1)] == f)
    pal = f == r
    dup &= ~pal | (c >= 3)
    m = np.zeros(n + 1, np.int32); w = np.nonzero(dup)[0]; np.add.at(m, w, 1); np.add.at(m, w + L, -1)
    mk = (np.cumsum(m)[:n] > 0); masks.append(mk.astype(np.uint8)); cov += int(mk.sum()); tot += n
maskall = np.concatenate(masks)
open(sys.argv[3],"wb").write(maskall.tobytes()) if len(sys.argv)>3 else None
print(f"L={L} genome {tot} bases, inside an exact duplicated L-mer: {cov} ({100*cov/tot:.2f}%)")
