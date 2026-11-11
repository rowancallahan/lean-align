#!/usr/bin/env python3
"""Do our alignments match minibwa's?   compare.py ours.sam minibwa.sam
Reads both files in step (both are in input order), primary records only, one pair = two mates.
A mate "matches" when both tools put it on the same chromosome and strand and the two alignments overlap.
(Not exact start: we trim low-quality ends, minibwa soft-clips them, so starts can differ by the trimmed part.)
A mate is "identical" when chromosome, strand, start and CIGAR are all equal."""
import collections, sys, pysam

def pairs(path):
    """yields (name, mate1, mate2) for each read pair"""
    mates = (r for r in pysam.AlignmentFile(path, check_sq=False) if not (r.is_secondary or r.is_supplementary))
    for a in mates:
        b = next(mates)
        assert a.query_name == b.query_name and a.is_read1 and b.is_read2, a.query_name
        yield a.query_name, a, b

def place(r): return (r.reference_name, r.is_reverse, r.reference_start, r.cigarstring)
def match(a, b):
    return (a.reference_name == b.reference_name and a.is_reverse == b.is_reverse
            and a.reference_start < b.reference_end and b.reference_start < a.reference_end)

count = collections.Counter(); examples = []
for (name, o1, o2), (name2, m1, m2) in zip(pairs(sys.argv[1]), pairs(sys.argv[2]), strict=True):
    assert name == name2, (name, name2)
    count["pairs"] += 1
    ours_mapped = not (o1.is_unmapped or o2.is_unmapped)
    mb_mapped = not (m1.is_unmapped or m2.is_unmapped)
    ours_unique = ours_mapped and o1.get_tag("XU") == "unique" and o2.get_tag("XU") == "unique"
    mb_q60 = mb_mapped and min(m1.mapping_quality, m2.mapping_quality) >= 60
    count["ours mapped"] += ours_mapped; count["minibwa mapped"] += mb_mapped
    count["ours unique"] += ours_unique; count["minibwa MAPQ 60"] += mb_q60
    if not (ours_mapped and mb_mapped): continue
    count["both mapped"] += 1
    same = match(o1, m1) and match(o2, m2)
    count["both mapped, match"] += same
    count["both mapped, identical"] += place(o1) == place(m1) and place(o2) == place(m2)
    if ours_unique:
        count["ours unique, minibwa mapped"] += 1
        count["ours unique, minibwa mapped, match"] += same
        if not same and len(examples) < 10: examples.append((name, place(o1), place(m1), m1.mapping_quality))
    if ours_unique and mb_q60:
        count["ours unique and minibwa MAPQ 60"] += 1
        count["ours unique and minibwa MAPQ 60, match"] += same

n = count["pairs"]
for k, v in count.items(): print(f"{v:>12,}  {100 * v / n:6.2f}%  {k}")          # % of all pairs
print("agreement rates (% of the row they are divided by):")
for num, den in [("both mapped, match", "both mapped"), ("both mapped, identical", "both mapped"),
                 ("ours unique, minibwa mapped, match", "ours unique, minibwa mapped"),
                 ("ours unique and minibwa MAPQ 60, match", "ours unique and minibwa MAPQ 60")]:
    print(f"  {100 * count[num] / max(count[den], 1):6.2f}%  {num} / {den}")
print("ours unique but a different place than minibwa (name, ours, minibwa, minibwa MAPQ):")
for e in examples: print("  ", e)
