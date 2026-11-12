#!/usr/bin/env python3
"""Structural check of a BAM written by Testing/benches/BamWrite.lean against the SAM of the same run.
   python3 -I bam_check.py X.bam X.sam
Checks: every BGZF block (gzip header, BC subfield BSIZE, zlib inflate with the block's CRC32 and ISIZE, no block over
65536 bytes), the 28-byte EOF block last, the BAM header (text equals the SAM header, @SQ names/lengths equal n_ref),
then every record field against the SAM line (QNAME, FLAG, RNAME, POS, MAPQ, CIGAR, RNEXT, PNEXT, TLEN, SEQ, QUAL, tags
with their BAM types), plus bin == reg2bin and the block_size / l_read_name / n_cigar_op consistency. No samtools needed."""
import struct, sys, zlib
bam, sam = sys.argv[1:]
data = open(bam, 'rb').read()
EOF = bytes.fromhex('1f8b08040000000000ff0600424302001b0003000000000000000000')
assert data.endswith(EOF), 'EOF block missing'
out, pos, blocks = bytearray(), 0, 0
while pos < len(data):
    assert data[pos:pos + 4] == b'\x1f\x8b\x08\x04', f'bad gzip header at {pos}'
    xlen = struct.unpack_from('<H', data, pos + 10)[0]
    assert xlen == 6 and data[pos + 12:pos + 16] == b'BC\x02\x00', 'BC subfield'
    bsize = struct.unpack_from('<H', data, pos + 16)[0] + 1
    assert bsize <= 65536
    crc, isize = struct.unpack_from('<II', data, pos + bsize - 8)
    d = zlib.decompressobj(-15); payload = d.decompress(data[pos + 18:pos + bsize - 8]) + d.flush()
    assert d.eof and not d.unused_data, 'deflate stream does not end at the CRC'
    assert len(payload) == isize and zlib.crc32(payload) == crc, f'CRC/ISIZE mismatch in block at {pos}'
    out += payload; pos += bsize; blocks += 1
assert pos == len(data)
b = bytes(out)
assert b[:4] == b'BAM\x01'
ltext = struct.unpack_from('<i', b, 4)[0]; text = b[8:8 + ltext].decode(); p = 8 + ltext
nref = struct.unpack_from('<i', b, p)[0]; p += 4
refs = []
for _ in range(nref):
    ln = struct.unpack_from('<i', b, p)[0]; name = b[p + 4:p + 4 + ln - 1].decode(); assert b[p + 3 + ln] == 0
    refs.append((name, struct.unpack_from('<i', b, p + 4 + ln)[0])); p += 8 + ln
lines = open(sam).read().split('\n')
samhdr = [l for l in lines if l.startswith('@')]
assert text == ''.join(l + '\n' for l in samhdr), 'header text differs'
assert refs == [(l.split('\t')[1][3:], int(l.split('\t')[2][3:])) for l in samhdr if l.startswith('@SQ')]
reads = [l.split('\t') for l in lines if l and l[0] != '@']
def reg2bin(beg, end):
    end -= 1
    for sh, off in ((14, 4681), (17, 585), (20, 73), (23, 9), (26, 1)):
        if beg >> sh == end >> sh: return off + (beg >> sh)
    return 0
SEQ, OPS = '=ACMGRSVTWYHKDBN', 'MIDNSHP=X'
n = 0
while p < len(b):
    bs = struct.unpack_from('<i', b, p)[0]; rec = b[p + 4:p + 4 + bs]; p += 4 + bs
    ref, pos0, lrn, mapq, bin_, ncig, flag, lseq, nref_, npos, tlen = struct.unpack_from('<iiBBHHHiiii', rec, 0)
    q = 32; name = rec[q:q + lrn - 1].decode(); assert rec[q + lrn - 1] == 0; q += lrn
    cig = ''.join(f'{v >> 4}{OPS[v & 15]}' for v in struct.unpack_from(f'<{ncig}I', rec, q)); q += 4 * ncig
    seq = ''.join(SEQ[(rec[q + i // 2] >> (4 if i % 2 == 0 else 0)) & 15] for i in range(lseq)); q += (lseq + 1) // 2
    qual = ''.join(chr(c + 33) for c in rec[q:q + lseq]); q += lseq
    tags = []
    while q < len(rec):
        t, ty = rec[q:q + 2].decode(), chr(rec[q + 2]); q += 3
        if ty == 'Z':
            e = rec.index(0, q); tags.append(f'{t}:Z:{rec[q:e].decode()}'); q = e + 1
        else:
            f, w = {'c': ('<b', 1), 'C': ('<B', 1), 's': ('<h', 2), 'S': ('<H', 2), 'i': ('<i', 4), 'I': ('<I', 4)}[ty]
            tags.append(f'{t}:i:{struct.unpack_from(f, rec, q)[0]}'); q += w
    s = reads[n]
    exp_ref = s[2]; got_ref = '*' if ref < 0 else refs[ref][0]
    got_next = '*' if nref_ < 0 else ('=' if nref_ == ref else refs[nref_][0])
    reflen = sum(int(c) for c, o in __import__('re').findall(r'(\d+)([A-Z=])', cig) if o in 'MDN=X')
    want_bin = reg2bin(pos0, pos0 + max(reflen, 1)) if ref >= 0 else 4680   # htslib: a record with no reference span covers [pos, pos+1)
    got = [name, str(flag), got_ref, str(pos0 + 1), str(mapq), cig or '*', got_next, str(npos + 1), str(tlen), seq or '*', qual or '*']   # l_seq 0 prints as *
    assert got == s[:11] and tags == s[11:], f'record {n}: BAM {got + tags} != SAM {s}'
    assert bin_ == want_bin, f'record {n}: bin {bin_} != {want_bin}'
    n += 1
assert n == len(reads), (n, len(reads))
print(f'OK: {blocks} BGZF blocks (CRC32 + ISIZE verified), {len(refs)} refs, {n} records equal to the SAM lines field by field')
