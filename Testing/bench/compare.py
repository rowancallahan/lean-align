#!/usr/bin/env python3
"""Do our alignments agree with minibwa's?   compare.py ours.sam minibwa.sam

Both files hold the same read pairs in the same order. Only primary records are read.
A mate "matches" when both tools put it on the same chromosome and strand and the two alignments overlap.
A mate is "identical" when chromosome, strand, start and CIGAR are all equal.
Starts can differ without a real disagreement: we trim low-quality ends, minibwa soft-clips them."""
import sys
import pysam

assert sys.version_info >= (3, 10), "needs Python 3.10 or newer (zip with strict=True)"
assert len(sys.argv) == 3, __doc__


def read_pairs(path):
    """Gives (mate1, mate2) for each read pair, in file order."""
    primary = []
    for record in pysam.AlignmentFile(path, check_sq=False):
        if record.is_secondary or record.is_supplementary:
            continue
        primary.append(record)
        if len(primary) == 2:
            mate1, mate2 = primary
            assert mate1.query_name == mate2.query_name
            assert mate1.is_read1 and mate2.is_read2
            yield mate1, mate2
            primary = []
    assert primary == []


def mapped(mate1, mate2):
    return not mate1.is_unmapped and not mate2.is_unmapped


def match(a, b):
    same_chromosome = a.reference_name == b.reference_name
    same_strand = a.is_reverse == b.is_reverse
    overlap = a.reference_start < b.reference_end and b.reference_start < a.reference_end
    return same_chromosome and same_strand and overlap


def identical(a, b):
    return (a.reference_name == b.reference_name and a.is_reverse == b.is_reverse
            and a.reference_start == b.reference_start and a.cigarstring == b.cigarstring)


pairs = 0
ours_mapped = 0
minibwa_mapped = 0
ours_unique = 0
minibwa_mapq60 = 0
both_mapped = 0
both_mapped_match = 0
both_mapped_identical = 0
unique_and_minibwa_mapped = 0
unique_and_minibwa_mapped_match = 0
unique_and_mapq60 = 0
unique_and_mapq60_match = 0
examples = []

for (o1, o2), (m1, m2) in zip(read_pairs(sys.argv[1]), read_pairs(sys.argv[2]), strict=True):
    assert o1.query_name == m1.query_name
    pairs += 1
    we_mapped = mapped(o1, o2)
    they_mapped = mapped(m1, m2)
    we_unique = we_mapped and o1.get_tag("XU") == "unique" and o2.get_tag("XU") == "unique"
    they_mapq60 = they_mapped and m1.mapping_quality >= 60 and m2.mapping_quality >= 60
    if we_mapped:
        ours_mapped += 1
    if they_mapped:
        minibwa_mapped += 1
    if we_unique:
        ours_unique += 1
    if they_mapq60:
        minibwa_mapq60 += 1
    if not (we_mapped and they_mapped):
        continue
    both_mapped += 1
    pair_matches = match(o1, m1) and match(o2, m2)
    if pair_matches:
        both_mapped_match += 1
    if identical(o1, m1) and identical(o2, m2):
        both_mapped_identical += 1
    if we_unique:
        unique_and_minibwa_mapped += 1
        if pair_matches:
            unique_and_minibwa_mapped_match += 1
        if not pair_matches and len(examples) < 10:
            examples.append((o1.query_name, o1.reference_name, o1.reference_start,
                             m1.reference_name, m1.reference_start, m1.mapping_quality))
    if we_unique and they_mapq60:
        unique_and_mapq60 += 1
        if pair_matches:
            unique_and_mapq60_match += 1


def show(label, count, out_of):
    assert out_of > 0, label
    percent = round(100 * count / out_of, 2)
    print(count, "of", out_of, "=", percent, "%", label)


show("pairs we map (both mates)", ours_mapped, pairs)
show("pairs minibwa maps (both mates)", minibwa_mapped, pairs)
show("pairs we call unique", ours_unique, pairs)
show("pairs minibwa gives MAPQ 60 on both mates", minibwa_mapq60, pairs)
show("pairs both tools map", both_mapped, pairs)
show("... of those, match", both_mapped_match, both_mapped)
show("... of those, identical", both_mapped_identical, both_mapped)
show("pairs we call unique that minibwa maps: match", unique_and_minibwa_mapped_match, unique_and_minibwa_mapped)
show("pairs we call unique and minibwa gives MAPQ 60: match", unique_and_mapq60_match, unique_and_mapq60)
print("pairs we call unique that minibwa puts elsewhere (name, our chromosome, our start, theirs, theirs, their MAPQ):")
for example in examples:
    print("  ", example)
