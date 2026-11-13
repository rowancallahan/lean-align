#!/usr/bin/env python3
"""Do our alignments agree with minibwa's?   compare.py ours.sam minibwa.sam

Both files hold the same read pairs in the same order. Only primary records are read.

Our record holds the part of the read we kept after trimming; minibwa's holds the whole read.
So the two start positions and CIGARs can differ while both tools agree. Two questions are asked per mate:

  same place       same chromosome, same strand, and the two alignments overlap on the reference.
  same positions   every letter of the read that both tools align sits at the same reference position.

A pair counts when both of its mates do."""
import sys
import pysam

assert sys.version_info >= (3, 10)
assert len(sys.argv) == 3, __doc__


def check_our_record(record, sam):
    name = record.query_name
    if record.query_sequence is None:               # a mate that was trimmed away completely has SEQ * and QUAL *
        assert record.is_unmapped, name + ": SEQ is * on a mapped record"
        assert record.get_tag("XT").startswith("trimmedAway"), name + ": SEQ is * on a record that is not trimmed away"
        return
    assert record.query_qualities is not None, name + ": no QUAL"
    assert len(record.query_sequence) == len(record.query_qualities), name + ": SEQ and QUAL differ in length"
    if record.is_unmapped:
        return
    assert record.infer_query_length() == len(record.query_sequence), name + ": CIGAR length differs from SEQ length"
    assert record.reference_start >= 0, name + ": starts before its chromosome"
    assert record.reference_end <= sam.get_reference_length(record.reference_name), name + ": ends after its chromosome"
    unique = record.get_tag("XU") == "unique"
    assert (record.mapping_quality == 60) == unique, name + ": MAPQ must be 60 exactly when XU is unique"


def check_our_mates(mate1, mate2):
    name = mate1.query_name
    assert mate1.next_reference_name == mate2.reference_name, name + ": mate 1 names the wrong chromosome for mate 2"
    assert mate1.next_reference_start == mate2.reference_start, name + ": mate 1 names the wrong start for mate 2"
    assert mate2.next_reference_name == mate1.reference_name, name + ": mate 2 names the wrong chromosome for mate 1"
    assert mate2.next_reference_start == mate1.reference_start, name + ": mate 2 names the wrong start for mate 1"


def both_mapped(mate1, mate2):
    return not mate1.is_unmapped and not mate2.is_unmapped


def read_pairs(path, is_ours):
    sam = pysam.AlignmentFile(path, check_sq=False)
    mates = []
    for record in sam:
        if is_ours:
            check_our_record(record, sam)
        if record.is_secondary or record.is_supplementary:
            continue
        mates.append(record)
        if len(mates) < 2:
            continue
        mate1, mate2 = mates
        mates = []
        assert mate1.query_name == mate2.query_name
        assert mate1.is_read1 and mate2.is_read2
        if is_ours and both_mapped(mate1, mate2):
            check_our_mates(mate1, mate2)
        yield mate1, mate2
    assert mates == []


def same_place(ours, theirs):
    same_chromosome = ours.reference_name == theirs.reference_name
    same_strand = ours.is_reverse == theirs.is_reverse
    overlap = ours.reference_start < theirs.reference_end and theirs.reference_start < ours.reference_end
    return same_chromosome and same_strand and overlap


def same_positions(ours, theirs):
    """Only called when same_place holds, so both records show the read on the same strand."""
    kept_from = theirs.query_sequence.find(ours.query_sequence)
    assert kept_from >= 0, ours.query_name + ": the part we kept is not inside the read minibwa reports"
    our_positions = ours.get_reference_positions(full_length=True)
    their_positions = theirs.get_reference_positions(full_length=True)
    letters_both_align = 0
    for i in range(len(our_positions)):
        our_position = our_positions[i]
        their_position = their_positions[kept_from + i]
        if our_position is None or their_position is None:
            continue
        if our_position != their_position:
            return False
        letters_both_align += 1
    return letters_both_align > 0


pairs = 0
we_map = 0
they_map = 0
unique_and_mapq60 = 0
unique_not_mapq60 = 0
mapq60_not_unique = 0
neither = 0
both_confident_same_place = 0
both_confident_same_positions = 0
unique_and_they_map = 0
unique_and_they_map_same_place = 0
examples = []

for (o1, o2), (m1, m2) in zip(read_pairs(sys.argv[1], True), read_pairs(sys.argv[2], False), strict=True):
    assert o1.query_name == m1.query_name
    pairs += 1
    we_mapped = both_mapped(o1, o2)
    they_mapped = both_mapped(m1, m2)
    we_unique = we_mapped and o1.get_tag("XU") == "unique" and o2.get_tag("XU") == "unique"
    they_mapq60 = they_mapped and m1.mapping_quality >= 60 and m2.mapping_quality >= 60
    if we_mapped:
        we_map += 1
    if they_mapped:
        they_map += 1

    if we_unique and they_mapq60:
        unique_and_mapq60 += 1
    elif we_unique:
        unique_not_mapq60 += 1
    elif they_mapq60:
        mapq60_not_unique += 1
    else:
        neither += 1

    if not (we_unique and they_mapped):
        continue
    unique_and_they_map += 1
    place = same_place(o1, m1) and same_place(o2, m2)
    if place:
        unique_and_they_map_same_place += 1
    elif len(examples) < 10:
        examples.append((o1.query_name, o1.reference_name, o1.reference_start,
                         m1.reference_name, m1.reference_start, m1.mapping_quality, m2.mapping_quality))
    if they_mapq60 and place:
        both_confident_same_place += 1
        if same_positions(o1, m1) and same_positions(o2, m2):
            both_confident_same_positions += 1


def show(count, out_of, label):
    assert out_of > 0, label
    percent = round(100 * count / out_of, 2)
    print(count, "of", out_of, "=", percent, "%", label)


show(we_map, pairs, "pairs we map (both mates)")
show(they_map, pairs, "pairs minibwa maps (both mates)")
print()
print("all pairs, by our call and minibwa's:")
show(unique_and_mapq60, pairs, "we say unique, minibwa gives MAPQ 60 to both mates")
show(unique_not_mapq60, pairs, "we say unique, minibwa does not")
show(mapq60_not_unique, pairs, "minibwa gives MAPQ 60 to both mates, we do not say unique")
show(neither, pairs, "neither")
print()
print("pairs where we say unique and minibwa gives MAPQ 60:")
show(both_confident_same_place, unique_and_mapq60, "same place")
show(both_confident_same_positions, unique_and_mapq60, "same positions, letter for letter")
print()
show(unique_and_they_map_same_place, unique_and_they_map, "pairs we say unique that minibwa maps at all: same place")
print("pairs we say unique that minibwa puts elsewhere")
print("(name, our chromosome, our start, minibwa's chromosome, minibwa's start, minibwa's MAPQ of mate 1, of mate 2):")
for example in examples:
    print("  ", example)
