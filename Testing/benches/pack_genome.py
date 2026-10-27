#!/usr/bin/env python3
"""Write the concatenated chromosomes as a packed genome (`PGen` layout, MapperPGen.lean).

    python3 bench/pack_genome.py <out_prefix> <chr.1l.fa>...

<out>.pgw: 64-letter blocks of 17 bytes (flag byte 1 = whole block inside the genome and
all ACGT; then letter i in bits 2*(i%4) of byte 1 + (i%64)/4, A0 C1 G2 T3; non-ACGT letters
get code 0), a partial last block with flag 0 and ceil(r/4) code bytes.
<out>.pgx: LE u32 triples (start, stop, byte) of the maximal runs of one non-ACGT byte.
<out>.pgn: the letter count.  Untrusted (the bench samples it against the FASTA; the proved
setting checks it with `checkPG`).  Streams in 64 M-letter chunks.
"""
import sys, mmap, numpy as np

out, files = sys.argv[1], sys.argv[2:]
CODE = np.zeros(256, np.uint8)
ODD = np.ones(256, bool)
for i, ch in enumerate(b"ACGT"):
    CODE[ch] = i
    ODD[ch] = False
CH = 1 << 26
fw = open(out + ".pgw", "wb")
runs = []          # [start, stop, byte]
total = 0
carry = np.zeros(0, np.uint8)

def emit(buf, final):
    """Write the full blocks of buf (and the partial last one when final); return the rest."""
    nb = len(buf) // 64
    if nb:
        blk = buf[: 64 * nb].reshape(nb, 64)
        flag = (~ODD[blk].any(axis=1)).astype(np.uint8)
        c = CODE[blk].reshape(nb, 16, 4)
        by = c[:, :, 0] | (c[:, :, 1] << 2) | (c[:, :, 2] << 4) | (c[:, :, 3] << 6)
        fw.write(np.concatenate([flag[:, None], by], axis=1).astype(np.uint8).tobytes())
    rest = buf[64 * nb:]
    if final and len(rest):
        r = len(rest)
        pad = np.zeros(-r % 4, np.uint8)
        c = CODE[np.concatenate([rest, np.full(len(pad), 65, np.uint8)])].reshape(-1, 4)
        by = c[:, 0] | (c[:, 1] << 2) | (c[:, 2] << 4) | (c[:, 3] << 6)
        fw.write(bytes([0]) + by.astype(np.uint8).tobytes())
        return np.zeros(0, np.uint8)
    return rest

for path in files:
    f = open(path, "rb")
    mm = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
    h = mm.find(b"\n") + 1
    end = len(mm)
    while end > h and mm[end - 1] in (10, 13): end -= 1
    seq = np.frombuffer(mm, np.uint8, count=end - h, offset=h)
    for a in range(0, len(seq), CH):
        x = np.array(seq[a: a + CH])
        assert not ((x == 10) | (x == 13)).any(), path
        # runs of one non-ACGT byte
        odd = ODD[x]
        if odd.any():
            idx = np.flatnonzero(odd)
            vals = x[idx]
            brk = np.flatnonzero((np.diff(idx) != 1) | (np.diff(vals.astype(np.int16)) != 0)) + 1
            starts = np.concatenate([[0], brk])
            stops = np.concatenate([brk, [len(idx)]])
            for s, e in zip(starts, stops):
                p0, p1, v = total + a + int(idx[s]), total + a + int(idx[e - 1]) + 1, int(vals[s])
                if runs and runs[-1][1] == p0 and runs[-1][2] == v: runs[-1][1] = p1
                else: runs.append([p0, p1, v])
        carry = emit(np.concatenate([carry, x]), False)
    total += len(seq)
    print(path, total, file=sys.stderr, flush=True)
emit(carry, True)
fw.close()
open(out + ".pgx", "wb").write(np.array(runs, dtype="<u4").reshape(-1).tobytes())
open(out + ".pgn", "w").write(f"{total}\n")
print(f"letters {total}, runs {len(runs)}", file=sys.stderr)
