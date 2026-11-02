#!/usr/bin/env python3
"""Compare two SAM files mate by mate, and both against the true origin in the read name.
   python3 compare_sam.py ours.sam minibwa.sam
Read names from sim_pairs.py look like s12:chr21:1000-1150+:1300-1450- (0-based starts)."""
import re, sys
def load(path):
    out = {}
    for line in open(path):
        if line[0] == '@': continue
        f = line.split('\t')
        flag = int(f[1])
        if flag & 0x900: continue                       # skip secondary / supplementary lines
        mate = 1 if flag & 0x40 else 2
        mapped = not flag & 4
        out[(f[0], mate)] = (f[2], int(f[3]), '-' if flag & 16 else '+', f[5]) if mapped else None
    return out
ours, mb = load(sys.argv[1]), load(sys.argv[2])
assert ours.keys() == mb.keys(), "the two files have different reads"
n = same_pos = same_cigar = ours_truth = mb_truth = 0
for (name, mate), a in ours.items():
    b = mb[(name, mate)]; n += 1
    chrom, s1, e1, st1, s2, e2, st2 = re.match(r'[^:]+:([^:]+):(\d+)-(\d+)([+-]):(\d+)-(\d+)([+-])', name).groups()
    truth = (chrom, int(s1 if mate == 1 else s2) + 1, st1 if mate == 1 else st2)
    if a and b and a[:3] == b[:3]: same_pos += 1; same_cigar += a[3] == b[3]
    near = lambda x: bool(x) and x[0] == truth[0] and x[2] == truth[2] and abs(x[1] - truth[1]) <= 10  # trimming / clipping shift POS a little
    ours_truth += near(a); mb_truth += near(b)
    if a != b and n - same_cigar <= 10: print("differs:", name, mate, "ours", a, "minibwa", b, "truth", truth)
print(f"mates {n}: same position {same_pos}, same position+CIGAR {same_cigar}; within 10 bp of truth: ours {ours_truth}, minibwa {mb_truth}")
