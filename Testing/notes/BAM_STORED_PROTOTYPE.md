# BAM writer prototype (stored BGZF) vs SAM text

`Testing/benches/BamWrite.lean` (`lake exe bam_write`), checker `Testing/scripts/bam_check.py`. Pure Lean: BAM records
(4-bit sequence, raw qualities, typed binary tags, `reg2bin`) in BGZF blocks with *stored* deflate payload (65280 bytes
per block), gzip CRC32 computed in Lean (slice-by-8), the 28-byte BGZF EOF block. No `extern`/`unsafe`/zlib. Not in `Spec/`.

Method: the pairs are mapped once with the proved `alignPairs` (100 000-pair chunks, as the shim) and the results kept;
only the output stage is timed (SAM: `Spec.samChunk` in 16 tasks + write; BAM: `bamChunk` in 16 tasks, BGZF framing in
one task per block, + write), 3 repetitions each, same results for both, 4 cores. Index load and mapping excluded.
Box: 4 cores shared (timings vary ~30% run to run; the median of the 3 repetitions is listed, the raw runs are in
the table below).

## Validation

### samtools 1.24 / htslib 1.24 (built from the tagged GitHub releases, Rowan allowed it)

On the same six outputs (3 sets x real M1 + synthetic mapped, 200 000 pairs, 400 000 records each; files regenerated for
this run, one repetition):

- `samtools quickcheck -v X.bam`: exit 0 on all six (header and BGZF EOF block fine).
- `samtools view -c X.bam`: 400000 on all six, equal to the SAM record count.
- `samtools flagstat`: 400000 in total, 200000 read1 + 200000 read2, all paired; real M1: 0 mapped, 0 properly paired;
  synthetic: 400000 mapped (100.00 %), 400000 properly paired, 0 singletons.
- Round trip: `samtools view -h X.bam` compared with the SAM of the same run with `cmp`/`diff`: the ONLY difference on all six is the
  one `@PG ID:samtools ...` line that `samtools view -h` appends to the header. All other header lines and all 400 000
  records are byte-identical (so samtools decodes SEQ, QUAL, CIGAR, flags, mate fields, TLEN and the tags `AS XB XU XT` to
  exactly the text our SAM writer prints).

### Python checker (independent of samtools; run first, before samtools was available)

`bam_check.py` parses every BGZF block independently (gzip header, BC subfield, zlib inflate, CRC32 and ISIZE of
each block, EOF block last), the BAM header (text equals the SAM header, n_ref list equals the `@SQ` lines), and every
record against the SAM line of the same run: QNAME, FLAG, RNAME, POS, MAPQ, CIGAR, RNEXT, PNEXT, TLEN, SEQ, QUAL, all tags
with their BAM types, bin == reg2bin, block_size/l_read_name/n_cigar_op consistent. Run on all six outputs below
(400 000 records each): OK. The checker was shown to fail on a flipped payload byte and on a changed tag.

## Results, 200 000 pairs (raw seconds; M1 = today's results, every pair unmapped)

Output stage, median of 3 repetitions (wall s / CPU s / bytes):

| set (results) | SAM text | BAM stored | 
|---|---|---|
| hg38_mason 2x150 (M1) | 0.615 / 1.54 / 164 999 607 | 1.327 / 3.82 / 138 244 796 |
| hg002_200k 2x250 (M1) | 0.829 / 1.89 / 239 201 415 | 1.677 / 5.08 / 192 688 135 |
| novaseq_200k 2x151 (M1) | 0.570 / 1.67 / 159 978 383 | 1.243 / 3.82 / 133 622 928 |
| hg38_mason (synthetic mapped) | 2.323 / 4.70 / 181 286 178 | 2.239 / 5.05 / 142 813 622 |
| hg002_200k (synthetic mapped) | 1.542 / 4.09 / 255 974 036 | 2.431 / 5.88 / 197 527 489 |
| novaseq_200k (synthetic mapped) | 1.516 / 3.63 / 176 750 530 | 2.123 / 4.98 / 138 275 835 |

(synthetic = invented found pairs, 150M-style CIGAR, to size the mapped path; the SAM "write" there is dominated by disk
writes and varies from 0.1 to 1.6 s between repetitions.)

Raw M1 runs (wall s): mason SAM 0.817 / 0.615 / 0.543, BAM 1.345 / 1.265 / 1.327; hg002 SAM 0.683 / 0.829 / 1.156,
BAM 1.677 / 1.750 / 1.467; novaseq SAM 0.570 / 0.521 / 0.761, BAM 1.242 / 1.219 / 1.259. The write call itself is
0.05-0.13 s for either format (page cache), so the 16-19 % smaller file saves under 0.02 s of write time on this box.
Mapping for the same pairs (not part of the comparison): mason 32.3 s, hg002 10.2 s, novaseq 16.7 s (`alignPairs`, wall).

## Reading

- BAM stored is **16-19 % fewer bytes** but, in this pure-Lean prototype, **not faster**: at M1 its output stage takes
  about 0.7 s longer wall and about 2.3 s more CPU per 200 000 pairs. Of the BAM stage, the record building is about
  0.85 s (per base: complement + 4-bit pack, per quality: -33, all through `ByteArray.push`), CRC32+framing about 0.2-0.4 s.
  SAM text is mostly `String`/`ByteArray` copies of data already in text form.
- Tried: table-driven packing, slice-by-8 CRC, pre-sized buffers: each within noise (the first version was 1.1-1.4 s).
  Ideas left: write into a preallocated buffer by index instead of `push`, pack 8 bases per step from a 256x256 table,
  skip `String` -> bytes for qualities by keeping the FASTQ line as bytes (`FastqRecord.quality : String` costs a
  `toUTF8` per mate).
- Gains would come on the I/O side only when the output goes through a slow disk or pipe or when compression is on
  (stored blocks do not compress; real BGZF would, at a CPU cost without zlib).
- Because it is not faster, no `Spec/Sam.lean` change is proposed from this. The prototype's field order and types are in
  `BamWrite.lean` (`putRecord`, `bamPair` mirror `samLines`) should Rowan want a BAM spec for `IO_PAIRED_UNPAIRED_TRIM.md` §5.
