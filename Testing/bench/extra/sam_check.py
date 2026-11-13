#!/usr/bin/env python3
"""Is every record of our SAM file well formed, and does it come from the input reads?

    python3 Testing/bench/extra/sam_check.py OURS.sam R1.fq.gz R2.fq.gz

The chromosome lengths are read from the @SQ lines of the SAM header. The SAM must have two records per input pair,
mate 1 then mate 2, in the order of the FASTQ files. Prints the number of records that break each rule, with an
example, and fails (exit 1) unless every count is 0.

Checked on every record:
 - QNAME is the FASTQ read name (up to the first space, without a /1 or /2 ending), in the FASTQ order.
 - FLAG: 0x1 set; 0x40 on mate 1 and 0x80 on mate 2; none of 0x100, 0x200, 0x400, 0x800 or higher bits.
 - SEQ '*' only together with QUAL '*', only on an unmapped record, and only with the tag XT:Z:trimmedAway1/2.
 - Otherwise: len(QUAL) = len(SEQ); SEQ has only A, C, G, T; QUAL letters are 33..126; a mapped mate is not shorter
   than 20 letters when its input read had 20 or more.
 - SEQ and QUAL (reverse-complemented and reversed on a mapped reverse-strand record) are a contiguous window of the
   FASTQ read with the same qualities.
 - Mapped: CIGAR is not '*', has only M, I, D, no zero length, no two equal ops in a row, at least one M; the CIGAR's
   query length is len(SEQ); RNAME is a chromosome and the alignment lies inside it; MAPQ is 60 if XU:Z:unique, else 0.
 - Unmapped: RNAME '*', POS 0, MAPQ 0, CIGAR '*', RNEXT '*', PNEXT 0, TLEN 0; FLAG 77 or 141.
 - Tags: a mapped record has AS, XB, XU in this order, AS <= 0; an unmapped one has XB, XU, or only XT:Z:trimmedAway1/2;
   XB <= 0; XU is unique, multimapper, unknown or repetitiveUnknown; XU unique never on an unmapped record.
Checked on every pair:
 - 0x8 set iff the mate is unmapped. When both are mapped: 0x2 set, 0x20 = mate on the reverse strand, RNEXT and
   PNEXT name the mate, the mates are on opposite strands, the same XU, XB and XT; on one chromosome
   |TLEN| = the span of both alignments, TLEN of mate 2 = -TLEN of mate 1, positive on the leftmost (mate 1 on a tie).
   When not both are mapped: 0x2 not set.
 - XT:Z:trimmedAwayK names a mate K whose SEQ is '*'; trimmedAway2 is not used when mate 1 is gone too.
"""
import gzip
import re
import sys

assert len(sys.argv) == 4, __doc__
SAM, FQ1, FQ2 = sys.argv[1:4]

counts = {}      # rule -> number of records or pairs breaking it
examples = {}    # rule -> the first example


def bad(rule, example):
    if rule not in counts:
        counts[rule] = 0
        examples[rule] = example
    counts[rule] = counts[rule] + 1


def mate_name(name):
    """The read name up to the first space, without a /1 or /2 ending."""
    name = name.split(" ")[0]
    if name.endswith("/1") or name.endswith("/2"):
        name = name[:-2]
    return name


COMPLEMENT = {"A": "T", "C": "G", "G": "C", "T": "A", "N": "N"}


def reverse_complement(s):
    out = []
    for c in reversed(s):
        out.append(COMPLEMENT[c])
    return "".join(out)


def read_fastq(f):
    """The next record (name, letters, qualities), or None at the end of the file."""
    header = f.readline()
    if header == "":
        return None
    letters = f.readline().rstrip("\n")
    plus = f.readline()
    quality = f.readline().rstrip("\n")
    assert header.startswith("@") and plus.startswith("+"), "not a FASTQ record: " + header
    return header[1:].rstrip("\n"), letters, quality


def parse_record(line):
    f = line.rstrip("\n").split("\t")
    tags = {}
    tag_order = []
    for t in f[11:]:
        tags[t[:2]] = t[5:]
        tag_order.append(t[:2])
    flag = int(f[1])
    return {"qname": f[0], "flag": flag, "rname": f[2], "pos": int(f[3]), "mapq": int(f[4]), "cigar": f[5],
            "rnext": f[6], "pnext": int(f[7]), "tlen": int(f[8]), "seq": f[9], "qual": f[10], "tags": tags,
            "tag_order": tag_order, "mapped": flag & 4 == 0, "rev": flag & 16 != 0}


def cigar_ops(cigar):
    """[(length, op)], or None if the CIGAR is not a list of number-op pairs."""
    ops = []
    for n, op in re.findall(r"(\d+)([MIDNSHP=X])", cigar):
        ops.append((int(n), op))
    joined = ""
    for n, op in ops:
        joined = joined + str(n) + op
    if joined != cigar:
        return None
    return ops


def check_record(d, mate, fastq_record, chromosomes):
    qn = d["qname"]
    o_name, o_seq, o_qual = fastq_record
    if qn != mate_name(o_name):
        bad("QNAME != FASTQ name (order or content)", qn + " " + mate_name(o_name))
    f = d["flag"]
    if f & 1 == 0:
        bad("0x1 not set", qn)
    if (f & 64 != 0) != (mate == 1) or (f & 128 != 0) != (mate == 2):
        bad("0x40/0x80 wrong for the mate", qn + " " + str(f))
    if f & 0x100 or f & 0x200 or f & 0x400 or f & 0x800 or f >= 0x1000:
        bad("secondary/QC/dup/supplementary flag set", qn + " " + str(f))

    # SEQ and QUAL, and where they come from
    if d["seq"] == "*":
        if d["qual"] != "*":
            bad("SEQ * but QUAL not *", qn)
        if d["mapped"]:
            bad("mapped record with SEQ *", qn)
        if not d["tags"].get("XT", "").startswith("trimmedAway"):
            bad("SEQ * without XT:Z:trimmedAway", qn)
    else:
        if len(d["qual"]) != len(d["seq"]):
            bad("len(QUAL) != len(SEQ)", qn)
        if re.fullmatch("[ACGTN]+", d["seq"]) is None:
            bad("SEQ outside ACGTN", qn)
        if d["mapped"] and len(d["seq"]) < 20 <= len(o_seq):
            bad("mapped mate trimmed to fewer than 20 letters (input had 20 or more)", qn)
        for c in d["qual"]:
            if not 33 <= ord(c) <= 126:
                bad("QUAL outside 33..126", qn)
                break
        window = d["seq"]
        window_qual = d["qual"]
        if d["rev"] and d["mapped"]:
            window = reverse_complement(d["seq"])
            window_qual = d["qual"][::-1]
        if "N" in window:
            bad("trimmed window contains N (proved A/C/G/T only)", qn)
        found = False
        p = o_seq.find(window)
        while p >= 0 and not found:
            if o_qual[p:p + len(window)] == window_qual:
                found = True
            p = o_seq.find(window, p + 1)
        if not found:
            bad("SEQ/QUAL are not a window of the FASTQ read (strand-corrected)", qn)

    if d["mapped"]:
        if d["cigar"] == "*":
            bad("mapped record with CIGAR *", qn)
        elif cigar_ops(d["cigar"]) is None:
            bad("CIGAR syntax", qn + " " + d["cigar"])
        else:
            ops = cigar_ops(d["cigar"])
            query_length = 0
            reference_length = 0
            has_m = False
            zero_length = False
            other_op = False
            repeated_op = False
            for k in range(len(ops)):
                n, op = ops[k]
                if n == 0:
                    zero_length = True
                if op not in "MID":
                    other_op = True
                if k + 1 < len(ops) and ops[k + 1][1] == op:
                    repeated_op = True
                if op in "M=X":
                    has_m = True
                if op in "MIS=X":
                    query_length = query_length + n
                if op in "MDN=X":
                    reference_length = reference_length + n
            d["reflen"] = reference_length
            if zero_length:
                bad("zero-length CIGAR op", qn + " " + d["cigar"])
            if other_op:
                bad("CIGAR op outside M/I/D", qn + " " + d["cigar"])
            if repeated_op:
                bad("adjacent equal CIGAR ops", qn + " " + d["cigar"])
            if not has_m:
                bad("mapped record whose CIGAR has no aligned base (no M)", qn + " " + d["cigar"])
            if d["seq"] != "*" and query_length != len(d["seq"]):
                bad("CIGAR query length != len(SEQ)", qn + " " + d["cigar"])
            if d["rname"] not in chromosomes:
                bad("RNAME not in the genome", qn + " " + d["rname"])
            elif d["pos"] < 1 or d["pos"] - 1 + reference_length > chromosomes[d["rname"]]:
                bad("alignment outside the chromosome", qn + " " + d["rname"] + ":" + str(d["pos"]))
        if d["mapq"] != (60 if d["tags"].get("XU") == "unique" else 0):
            bad("MAPQ != 60 iff XU unique", qn + " " + str(d["mapq"]))
    else:
        if (d["rname"], d["pos"], d["mapq"], d["cigar"], d["rnext"], d["pnext"], d["tlen"]) != ("*", 0, 0, "*", "*", 0, 0):
            bad("unmapped record with non-default RNAME/POS/MAPQ/CIGAR/RNEXT/PNEXT/TLEN", qn)

    # tags
    t = d["tags"]
    if d["mapped"]:
        if d["tag_order"] != ["AS", "XB", "XU"]:
            bad("mapped record tags != AS XB XU", qn)
        elif re.fullmatch(r"-?\d+", t["AS"]) is None or int(t["AS"]) > 0:
            bad("AS not a non-positive integer", qn + " " + t["AS"])
    elif t.get("XT", "").startswith("trimmedAway"):
        if d["tag_order"] != ["XT"]:
            bad("trimmedAway record has other tags", qn)
        if f not in (77, 141):
            bad("trimmedAway record flag != 77/141", qn + " " + str(f))
    elif d["tag_order"] != ["XB", "XU"]:
        bad("unmapped record tags != XB XU (or XT trimmedAway)", qn)
    elif f not in (77, 141):
        bad("unmapped record flag != 77/141", qn + " " + str(f))
    if "XB" in t and (re.fullmatch(r"-?\d+", t["XB"]) is None or int(t["XB"]) > 0):
        bad("XB not a non-positive integer", qn + " " + t["XB"])
    if "XU" in t and t["XU"] not in ("unique", "multimapper", "unknown", "repetitiveUnknown"):
        bad("XU value", qn + " " + t["XU"])
    if not d["mapped"] and t.get("XU") == "unique":
        bad("XU unique on an unmapped record", qn)


def check_pair(a, b):
    qn = a["qname"]
    for x, y in ((a, b), (b, a)):
        if (x["flag"] & 8 != 0) != (not y["mapped"]):
            bad("0x8 != mate unmapped", qn)
        if x["mapped"] and y["mapped"]:
            if (x["flag"] & 32 != 0) != y["rev"]:
                bad("0x20 != mate strand", qn)
            if x["rnext"] != ("=" if x["rname"] == y["rname"] else y["rname"]):
                bad("RNEXT != mate RNAME", qn)
            if x["pnext"] != y["pos"]:
                bad("PNEXT != mate POS", qn)
            if x["flag"] & 2 == 0:
                bad("both mapped but 0x2 not set", qn)
    if a["mapped"] and b["mapped"]:
        if a["rname"] == b["rname"] and "reflen" in a and "reflen" in b:
            left = min(a["pos"], b["pos"])
            right = max(a["pos"] + a["reflen"], b["pos"] + b["reflen"])
            span = right - left
            if abs(a["tlen"]) != span or abs(b["tlen"]) != span:
                bad("|TLEN| != span of the two alignments", qn)
            if a["tlen"] != -b["tlen"]:
                bad("TLEN of the mates not opposite", qn)
            a_left = a["pos"] <= b["pos"]
            if (a["tlen"] > 0) != a_left or (b["tlen"] > 0) == a_left:
                bad("TLEN sign: positive must be the leftmost mate (mate 1 on ties)", qn)
        if a["rev"] == b["rev"]:
            bad("proper pair with both mates on one strand", qn)
        if "XU" not in a["tags"]:
            bad("mapped without XU", qn)
        for tag in ("XU", "XB", "XT"):
            if a["tags"].get(tag) != b["tags"].get(tag):
                bad("mates carry different XU/XB/XT", qn)
                break
    else:
        for d in (a, b):
            if d["flag"] & 2:
                bad("0x2 set on a pair that is not mapped", qn)
    for d in (a, b):
        xt = d["tags"].get("XT", "")
        if xt.startswith("trimmedAway"):
            named = a if xt[-1] == "1" else b
            if named["seq"] != "*":
                bad("XT trimmedAway names a mate that still has SEQ", qn + " " + xt)
            if xt[-1] == "2" and a["seq"] == "*":
                bad("trimmedAway2 but mate 1 is also gone (should say trimmedAway1)", qn)


chromosomes = {}
records = []     # the records of the pair being read
pairs = 0
fq1 = gzip.open(FQ1, "rt")
fq2 = gzip.open(FQ2, "rt")
for line in open(SAM):
    if line.startswith("@SQ"):
        name = None
        length = None
        for field in line.rstrip("\n").split("\t"):
            if field.startswith("SN:"):
                name = field[3:]
            if field.startswith("LN:"):
                length = int(field[3:])
        chromosomes[name] = length
        continue
    if line.startswith("@"):
        continue
    records.append(parse_record(line))
    if len(records) < 2:
        continue
    r1 = read_fastq(fq1)
    r2 = read_fastq(fq2)
    if r1 is None or r2 is None:
        bad("record count != 2 x FASTQ pairs", "more records than FASTQ pairs")
        break
    if mate_name(r1[0]) != mate_name(r2[0]):
        bad("FASTQ mates differ in name", r1[0])
    check_record(records[0], 1, r1, chromosomes)
    check_record(records[1], 2, r2, chromosomes)
    check_pair(records[0], records[1])
    pairs = pairs + 1
    records = []
if records != [] or read_fastq(fq1) is not None:
    bad("record count != 2 x FASTQ pairs", "fewer records than FASTQ pairs, or an odd number of records")

print(str(pairs) + " pairs checked")
for rule in counts:
    print("  FAIL " + rule + ": " + str(counts[rule]) + "   e.g. " + examples[rule])
assert pairs > 0, "no pairs"
assert counts == {}, "some records are not well formed (see the FAIL lines above)"
print("SAM CHECK PASSED")
