# SAM/BAM output fuzz and minibwa comparison on the current head (2026-11-02)

Head tested: `origin/claude/festive-fermi-mf9mo6` @ 0ef82b5 (= f29c675 placements + proved quality trimming in the shim + FASTQ chunk 20 000 +
capBudget 5000, then one notes commit). Built locally with Lean 4.35; shim `lean-align map shim.idx R1 R2 out.sam 100 1000`; minibwa c07de5c
`map -t 4`; samtools/htslib 1.24. Sets: hg38 `mason`, `low` (simulated 2x150, true positions in the read names), `NovaSeq` 2x151, `HiSeq` 2x250,
200 000 pairs each, plus a generated edge-case set (3 041 pairs, 6 082 records). Everything below is measured; the repeat-masked (lowercase)
hg38 check from the earlier note is still open (needs `ngi-igenomes.s3.amazonaws.com` allowed in the environment's network policy).

Reproduce: `sh Testing/scripts/output_vs_minibwa.sh OUT mason...` (KEEP=1), then `bash Testing/scripts/output_fuzz.sh OUT SET... PATH/edge`;
edge reads: `python3 -I Testing/scripts/fuzz_reads.py GENOME.upper.fa PREFIX 150 1`. Checker: `Testing/scripts/sam_fuzz_check.py`
(independent of the Lean code; reads the FASTQ and the chromosome list), `Testing/scripts/bam_check.py`.

## Summary

1. **One class of malformed output, ~1-2.7 % of pairs: placeholder alignments.** The last-resort pair is printed as two all-insertion
   alignments: mate 1 `nI` at `chr1:1` (flag 99), mate 2 `nI` at `chr1:101` (flag 147), TLEN 100, MAPQ 0, `XU:Z:unknown`, tier
   `boundsOnly`/`stoppedEarly`. A CIGAR with no aligned base is formally an alignment (score about -306 for 150 letters) and satisfies the
   proper-pair test vacuously (TLEN 100 = the minimum fragment given to the shim in these runs), so `alignPairs_correct` is not contradicted, but a reader sees a pair mapped
   to chr1:1. Counts below. minibwa maps 85-100 % of those reads and 28-54 % of them with MAPQ >= 30, so they are mappable pairs, not junk reads.
2. **Everything else the checker tests has zero violations on all five inputs** (about 1.6 M records): FLAG bits, `*`/0 fields of unmapped records,
   CIGAR syntax and ops, CIGAR query length == len(SEQ), len(QUAL) == len(SEQ), positions inside their chromosomes, RNEXT/PNEXT/0x20/0x8 against
   the mate, TLEN (opposite, = span of the two alignments, positive on the leftmost), proper pair = opposite strands, tag set and order, MAPQ 60
   iff `XU:Z:unique`, `*` SEQ/QUAL only on a mate named by `XT:Z:trimmedAway1/2`, printed SEQ/QUAL is a window of the FASTQ read (strand
   corrected) and A/C/G/T only (the trimmer's proved property), QNAME and order equal to the FASTQ.
3. **SAM and BAM agree record for record.** `bam_write` on the same reads gives the same SAM records as the shim (byte for byte), its BAM passes
   `samtools quickcheck`, `view -c` equals the SAM record count, `samtools view` of the BAM is byte-equal to the SAM records, `view -h` equals
   the SAM header except the `@PG` samtools adds, `flagstat` and `stats` (SN lines) are identical to those of the SAM, and the independent
   Python BAM parser reproduces every field (CRC32/ISIZE per BGZF block, bin, typed tags).
4. **Independent correctness check against the reference**: for every mapped record with only `M` operations (no `N` possible in a trimmed
   window), `AS == -4 * NM` where NM comes from `samtools calmd` against hg38: 381 639 (mason), 388 033 (low), 358 131 (HiSeq), 369 225 (NovaSeq),
   3 008 (edge) records, **zero exceptions**.
5. **Against minibwa**, comparing aligned reference intervals (trimming shortens our reads, minibwa soft-clips): when both tools call a pair unique
   (ours `XU:Z:unique`, minibwa MAPQ >= 30 on both mates) the strand and aligned interval overlap on all but 0-7 pairs per set, and
   where they differ on simulated reads we are at the true position (7 of 8 such pairs, the eighth both off).

## 1. Mapped and unique, ours vs minibwa (% of 200 000 pairs)

| set | ours both mapped | of which placeholder | ours mapped with an aligned base | ours unique | minibwa both mapped | proper | pair MAPQ >= 30 | MAPQ 60 |
|---|---|---|---|---|---|---|---|---|
| mason | 97.96 | 0.99 (1 972) | 96.98 | 86.51 | 100.00 | 99.99 | 96.14 | 90.35 |
| low | 99.86 | 0.16 (320) | 99.70 | 94.23 | 100.00 | 99.99 | 96.29 | 90.63 |
| HiSeq | 94.10 | 1.19 (2 385) | 92.90 | 81.71 | 99.57 | 98.06 | 92.50 | 87.57 |
| NovaSeq | 97.80 | 2.72 (5 436) | 95.09 | 81.94 | 99.08 | 97.62 | 91.23 | 85.15 |

Of minibwa's pairs with MAPQ >= 30 we map / mark unique: mason 97.96 / 89.82 %, low 99.86 / 97.56 %, HiSeq 95.59 / 88.08 %, NovaSeq 98.69 / 89.38 %.
Of our unique pairs minibwa has MAPQ >= 30 for 99.82 / 99.69 / 99.70 / 99.52 %. (Our MAPQ is 60 for unique and 0 otherwise.)
Trimming now shortens: mates shortened (mean letters removed): mason 10.6 % (1.3), low 4.0 % (2.7), HiSeq 76.7 % (24.4), NovaSeq 22.2 % (12.5); none trimmed away
in these four sets.

## 2. Our unique pairs vs minibwa (both mates; aligned reference interval, soft clips and trimmed ends excluded)

| relation (pair = the worse mate) | mason | low | HiSeq | NovaSeq |
|---|---|---|---|---|
| our unique pairs | 173 017 | 188 466 | 163 427 | 163 877 |
| identical position and CIGAR | 80.31 % | 92.13 % | 6.96 % | 69.38 % |
| ours inside minibwa's interval (we trim more) | 18.29 % | 7.51 % | 92.41 % | 30.21 % |
| minibwa inside ours (minibwa clips more) | 1.31 % | 0.13 % | 0.39 % | 0.26 % |
| same interval, CIGAR differs (e.g. minibwa `5S145M` vs ours `145M`) | 144 | 435 | 246 | 194 |
| shifted overlap (>= 50 %) | 9 | 2 | 118 | 48 |
| different chromosome/strand or disjoint | 2 | 5 | 32 | 13 |
| minibwa has a mate unmapped / overlap < 50 % | 0 / 0 | 0 / 0 | 2 / 2 | 4 / 0 |

Pairs both tools call unique (ours unique, minibwa MAPQ >= 30): mason 172 708, low 187 878, HiSeq 162 943, NovaSeq 163 092; strand and interval overlap
on 100.00 % (disjoint: 0 / 0 / 7 / 2 pairs). The HiSeq/NovaSeq "identical" shares are low only because the shim now trims HiSeq mates by 24 letters on average
(real adapter/low-quality tails; minibwa soft-clips them or aligns them), so positions differ at the ends, not at the locus.
Simulated sets, true position from the read name (aligned interval inside the true one +-10): mason, 31 637 of 31 638 "ours inside" pairs have both tools at truth;
the 3 pairs where only ours is at truth are 2 disjoint and 1 "inside"; low: 4 disjoint pairs have ours at truth and minibwa off, 1 both off, nothing where
minibwa is right and we are not.
Mates placed identically by both tools (from our unique pairs): FLAG differs on 2 / 0 / 41 / 1 mates, RNEXT 0 / 0 / 1 / 1, TLEN 109 / 1 153 / 2 963 / 11 136 and
PNEXT 17 986 / 7 334 / 118 894 / 27 533 (the other mate is clipped/trimmed differently), MAPQ 11 566 / 13 176 / 5 375 / 10 462 (mason / low / HiSeq / NovaSeq).

## 3. What minibwa does with the pairs we place badly (% of the group)

| set | our pairs | n | minibwa maps both mates | MAPQ 0 | MAPQ >= 30 | has XA | has SA |
|---|---|---|---|---|---|---|---|
| mason | placeholder pair (CIGAR without M) | 1,972 | 100.00% | 34.43% | 50.60% | 25.86% | 0.00% |
| mason | mapped by us, real alignment, uniqueness unknown, XB:i:0 | 9,637 | 100.00% | 42.02% | 39.08% | 47.67% | 0.00% |
| mason | mapped by us, real alignment, uniqueness unknown, XB < 0 | 11,303 | 100.00% | 1.96% | 96.31% | 6.64% | 0.01% |
| mason | unmapped by us, XB < 0 | 4,071 | 100.00% | 2.26% | 96.56% | 5.97% | 0.00% |
| low | placeholder pair (CIGAR without M) | 320 | 100.00% | 50.31% | 28.13% | 29.38% | 0.00% |
| low | mapped by us, real alignment, uniqueness unknown, XB:i:0 | 10,169 | 100.00% | 45.95% | 35.54% | 49.80% | 0.00% |
| low | mapped by us, real alignment, uniqueness unknown, XB < 0 | 757 | 100.00% | 2.91% | 94.32% | 8.45% | 0.00% |
| low | unmapped by us, XB < 0 | 288 | 100.00% | 1.39% | 96.53% | 5.21% | 0.00% |
| HiSeq | placeholder pair (CIGAR without M) | 2,385 | 92.08% | 20.13% | 53.50% | 18.91% | 10.52% |
| HiSeq | mapped by us, real alignment, uniqueness unknown, XB:i:0 | 16,310 | 98.38% | 33.79% | 50.09% | 29.97% | 5.62% |
| HiSeq | mapped by us, real alignment, uniqueness unknown, XB < 0 | 6,069 | 99.92% | 9.67% | 73.36% | 24.44% | 11.02% |
| HiSeq | unmapped by us, XB < 0 | 11,809 | 96.67% | 10.78% | 69.06% | 21.31% | 10.57% |
| NovaSeq | placeholder pair (CIGAR without M) | 5,436 | 84.71% | 15.03% | 52.03% | 18.78% | 6.97% |
| NovaSeq | mapped by us, real alignment, uniqueness unknown, XB:i:0 | 18,231 | 96.76% | 38.06% | 42.31% | 34.16% | 2.72% |
| NovaSeq | mapped by us, real alignment, uniqueness unknown, XB < 0 | 8,065 | 99.34% | 7.58% | 79.89% | 18.65% | 4.49% |
| NovaSeq | unmapped by us, XB < 0 | 4,391 | 91.69% | 12.87% | 54.34% | 31.11% | 10.50% |

(Placeholder = the `nI` pairs above. "Real alignment, XB:i:0" = a genuine pair printed with bound 0 and uniqueness unknown; "XB < 0" = a router
budget stop, not a repeat. "unmapped by us" pairs all have XB < 0.) Placeholder pairs are at most 2.7 % of pairs, but the router stops that give no
answer within its budget (XB < 0) are another 2-6 %, and minibwa has a confident placement for most of those too.

## 4. Samtools and BAM (same reads, `bam_write` real results)

| input | pairs | SAM records == bam_write SAM | bam_check (Python) | quickcheck | view -c | `samtools view` BAM == SAM | `view -h` == SAM (-@PG) | flagstat | stats SN |
|---|---|---|---|---|---|---|---|---|---|
| mason | 200 000 | yes | OK | 0 | 400 000 | byte-equal | equal | equal | equal |
| low | 200 000 | yes | OK | 0 | 400 000 | byte-equal | equal | equal | equal |
| HiSeq | 200 000 | yes | OK | 0 | 400 000 | byte-equal | equal | equal | equal |
| NovaSeq | 200 000 | yes | OK | 0 | 400 000 | byte-equal | equal | equal | equal |
| edge | 3 041 | yes | OK | 0 | 6 082 | byte-equal | equal | equal | equal |

Two fixes were needed in my own tooling, not in the BAM writer: (a) `Testing/benches/BamWrite.lean` still passed `some letters` for a trimmed-away mate
where `Main.lean` passes `none` (so on trimmed-away pairs it aligned different input; fixed: same `chunkPairs` rule as `Main.lean`); (b) `bam_check.py` expected
`bin` from `reg2bin(pos, pos+0)` for zero-span records (htslib uses `pos+1`, which is what the writer emits) and `''` for an empty SEQ (BAM l_seq 0 prints `*`).

## 5. Edge-case set (3 041 pairs, valid FASTQ: A/C/G/T/N, Phred+33)

Categories in `fuzz_reads.py`: normal pairs with errors/indels, bad-quality tails/heads/noisy qualities, adapter-like tails, one or both mates all-`#`, all-N reads,
N-rich reads, 1..101-letter reads, 400-1000-letter reads, different mate lengths, same-strand mates, mates 2.5 kb apart, mates on different chromosomes, random
sequences, identical mates, mate 2 left of mate 1, duplicates, reads at chromosome ends and next to genome N runs, names with comments.
Result: no crash, 3 041 pairs in, 6 082 records out in input order; hard violations: only the 2 116 placeholder records (random/unmappable pairs get the chr1:1 pair);
all other rules zero. Observations:
- Trimmed away (`SEQ *`, `XT:Z:trimmedAway1/2`, flags 77/141, `*`/0 elsewhere): 450 mates, all with no A/C/G/T. The tag names the first trimmed-away mate only (mate 1 if both).
- **A mate with all-low quality is not trimmed away**: the proved trimmer keeps the best nonempty window, so an all-`#` read is cut to its single best letter (300 mates
  in this set) and is then aligned as e.g. `1M` or `5I` (warning: mates shortened to < 20 letters: 999 here; 1 627 in HiSeq, 986 in NovaSeq, 0 in mason/low).
- 16 edge records and 48-606 per real set have CIGARs starting or ending with an insertion/deletion (e.g. `4I8M4I4M1D107M`, `4I246M`); legal SAM but validators such as Picard's
  complain; they are the long low-score gapped alignments of the fallback, or short end insertions.
- Malformed-input behaviour (out-of-step mate names, unequal files, SEQ/QUAL length mismatch) was not rerun here; the shim code throws for all three.

## What to fix before writing the specs (observations, not changes)

1. Do not print the placeholder pair: either leave such pairs unmapped (`found := none`, the proved M1 answer) or require at least one aligned base / a score above `junkScore`
   in the printed alignment; this removes all 640-10 872 violations per set without touching `alignPairs_correct`.
2. Decide the trimmer's floor: today a read with any A/C/G/T is never trimmed away; a minimum kept length would stop 1-letter mates from being aligned and printed.
3. TLEN/PNEXT/MAPQ differences against minibwa are consequences of trimming and our MAPQ policy (0/60), not of inconsistent output: our own output is internally consistent (section 2 of the Summary).

## CI regression: `Testing/scripts/fuzz_ci.sh` (branch test/fuzz-ci)

A small version of the output fuzz that needs no hg38 and runs in about 20 s (16 s measured here, 2 917 pairs): it generates a 2 Mb two-chromosome genome with repeats,
segmental copies, tandem arrays and N runs (`sim_genome_dup.py`, fixed seed), runs `lean-align build`, simulates 3 x 700 pairs (`sim_pairs.py` mason/low/high) plus the edge-case set
(`fuzz_reads.py`, 40 pairs per category), maps them and runs `sam_fuzz_check.py`. Nothing large is committed; everything is generated into a temp directory that is removed afterwards.
Zero hard violations are required (exit 1 otherwise); the checks are the ones in this note's Summary item 2. Checked to fail: clearing 0x2 on one record, changing one TLEN, dropping one SEQ letter,
shifting one POS and replacing one SEQ by `*` are each caught (exit 1).

**Wiring:** a separate script, called from `CI_check.sh` only when `FUZZ=1` (`FUZZ=1 sh Testing/scripts/CI_check.sh`), so the default developer check keeps its current length. The
other CI steps print into the same `== step` format and `fail=1` on error.

**Two expected failures** (`--xfail=` flags in `fuzz_ci.sh`; they print `XFAIL` with the count and do not fail the run):
- `no-aligned-base`: no mapped record may have a CIGAR with zero aligned bases (the `150I` placeholders): currently 616 records in the 5 834.
- `short-mate`: no mapped mate that had 20 or more letters in the FASTQ may be printed with fewer than 20 (the all-`#` read trimmed to one letter): currently 251 mates.
When a fix lands the rule has no hits and the script prints `XPASS ... delete the flag so this rule is enforced`; deleting the flag from `fuzz_ci.sh` turns it into a hard check.
(An input read that is itself shorter than 20 letters is not flagged.)
