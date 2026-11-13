#!/usr/bin/env python3
"""Is every mate where it was cut from?   tiny_truth.py ours.sam
Reads the SAM of the tiny data (tiny_data.py). A read name is u{n}_{chromosome}_{start}_{fragment length}_{strand}_{e1}_{e2}.
The forward mate starts at start + 1 (SAM positions count from 1), the reverse mate at start + fragment length - 150 + 1,
both on that chromosome, both with the CIGAR 150M. Any other record stops the script."""
import sys
import pysam

assert len(sys.argv) == 2, __doc__
READ_LENGTH = 150
records = 0
for record in pysam.AlignmentFile(sys.argv[1], check_sq=False):
    assert not record.is_unmapped, record.query_name
    assert not record.is_secondary and not record.is_supplementary, record.query_name
    number, chromosome, start, fragment_length, strand, errors1, errors2 = record.query_name.split("_")
    assert record.reference_name == chromosome, record.query_name
    assert record.cigarstring == "150M", record.query_name
    if record.is_reverse:
        expected_start = int(start) + int(fragment_length) - READ_LENGTH
    else:
        expected_start = int(start)
    assert record.reference_start == expected_start, record.query_name      # pysam counts from 0
    records += 1
print(records, "records, every one at its true position")
