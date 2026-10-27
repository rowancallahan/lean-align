#!/usr/bin/env python3
"""Benchmark only.  Re-score minibwa's primary alignments with the spec's scoring (sc0:
mismatch 4, gap 6 + 2L, whole read against any reference window; parasail sg_dx, checked
against a brute DP) near minibwa's position (±PAD letters).  One line per pair:
   name len1 len2 pen1 pen2 mapq1 mapq2 proper chrom
pen = -1 when the mate is unmapped by minibwa.
   python3 bench/mb_penalty.py <genome.1l.fa> <minibwa.sam> > pen.tsv"""
import mmap, re, sys, parasail
PAD = 40
M = parasail.matrix_create("ACGTN", 0, -4)
fa, sam = sys.argv[1:3]
f = open(fa, "rb")
G = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
chrom = {}  # name -> (start, length) of the sequence line
i = 0
while i < len(G):
    j = G.find(b"\n", i)
    name = G[i + 1:j].split()[0].decode()
    k = G.find(b"\n", j + 1)
    k = len(G) if k < 0 else k
    chrom[name] = (j + 1, k - j - 1)
    i = k + 1

def pen(f):
    flag = int(f[1])
    if flag & 4: return -1
    s, n = chrom[f[2]]
    lead = re.match(r"(\d+)[SH]", f[5])
    p = int(f[3]) - 1 - (int(lead.group(1)) if lead else 0)
    a, b = max(0, p - PAD), min(n, p + len(f[9]) + PAD)
    ref = G[s + a:s + b].decode().upper()
    return -parasail.sg_dx_scan_16(f[9], ref, 8, 2, M).score

recs = {}
for line in open(sam):
    if line[0] == "@": continue
    f = line.split("\t")
    flag = int(f[1])
    if flag & 0x900: continue
    r = recs.setdefault(f[0], [None, None])
    r[0 if flag & 64 else 1] = f
    if r[0] and r[1]:
        a, b = r
        fa_, fb = int(a[1]), int(b[1])
        proper = int(bool(fa_ & 2) and not fa_ & 4 and not fb & 4)
        print(f[0], len(a[9]), len(b[9]), pen(a), pen(b), a[4], b[4], proper, a[2], sep="\t")
        del recs[f[0]]
assert not recs, len(recs)
