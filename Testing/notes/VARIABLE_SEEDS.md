# Variable-length seeds: how short is the shortest unique substring in hg38, and what would pinning by it buy?

Box S1, 2026-11-02. Research plus a quick measurement; no proofs, nothing in the mapper changed. Program:
`Testing/scripts/seed_uniqueness.c` (`gcc -O3 -march=native -pthread`; one pass over hg38.upper.fa with 4 threads, ~5.5 min;
exact counts of the sampled k-mers on both strands through hash tables, no suffix array or FM-index needed). Usage:
`seed_uniqueness hg38.upper.fa 5000 mason_R1 mason_R2 nova_R1 nova_R2 hg002_R1 hg002_R2`. hg38 here = the bench genome:
3 099 922 541 bases in 195 sequences (primary chromosomes + unplaced/random contigs). "Unique" = the k-mer or its
reverse complement occurs exactly once in this file.

## 1. Minimal unique length per position (200 000 random hg38 positions, error-free genome windows, extended to the right)

Fraction of positions whose k-mer is unique: k=14 0.5 %, 16 11.9 %, 18 51.7 %, 20 69.9 %, 22 74.8 %, 24 77.2 %, 26 79.0 %,
28 80.6 %, 30 81.9 %, 32 83.2 % (k=12: 0).

Minimal unique length (smallest tested k with count 1), cumulative over all positions: <=16: 11.9 %, <=18: 51.7 %,
<=20: 69.9 %, <=24: 77.2 %, <=28: 80.6 %, <=32: 83.2 %, >32: 16.8 %. Median 18-19; the bulk is 17-20.

Inside repeats (strata by what the same position looks like at other lengths):
| stratum (n) | <=22 | <=24 | <=28 | <=32 | >32 |
|---|---|---|---|---|---|
| 20-mer occurs >= 2 times, "repeat-ish" (60 174) | 16.3 % | 24.3 % | 35.5 % | 44.0 % | 56.0 % |
| 20-mer repeated but the 32-mer unique (26 465) | 37.0 % | 55.2 % | 80.7 % | 100 % | - |
| 32-mer occurs >= 2 times, a true repeat of >= 32 bp (33 709 = 16.9 %) | 0 | 0 | 0 | 0 | 100 % |
So about 17 % of the genome has no unique substring at all up to 32 letters (and for those the unique length, if any, is
far beyond; exactly the part where a pinned seed does not exist and the router must fall back). A further 13 % of positions
(20-mer repeated, 32-mer unique) needs 22-32 letters: a fixed 25-mer already covers most of them, a 20-mer seed does not.

## 2. Reads: mates with at least one exact unique seed (first 5000 pairs = 10 000 mates per set; all windows of the length at every offset)

Mates with >= 1 unique window of length <= K (any tested length 16/20/24/28/32 up to K), exact match to hg38 (a window with a
sequencing error or a novel variant has count 0 and does not count):
| set | K=16 | 20 | 24 | 28 | 32 |
|---|---|---|---|---|---|
| mason 2x150 | 93.7 % | 97.5 % | 98.1 % | 98.5 % | 98.6 % |
| NovaSeq 2x151 | 88.5 % | 93.4 % | 94.3 % | 94.9 % | 95.2 % |
| HiSeq (hg002) 2x250 | 94.1 % | 96.4 % | 96.8 % | 97.0 % | 97.2 % |
With windows of ONE length: 20: 96.1 / 92.6 / 95.4 %, 24: 95.8 / 92.4 / 94.9 %, 32: 96.0 / 92.2 / 94.4 % (mason / NovaSeq / HiSeq);
a mate has ~70-160 unique windows of each length 20-32, so unique seeds are plentiful (one needs to find only one or two).
Per read position, the shortest unique window starting there (16/20/24/28/32/none): mason 11.2/41.6/5.0/2.2/1.6/38.4 %,
NovaSeq 10.6/46.0/5.4/2.4/1.8/33.9 %, HiSeq 10.9/48.8/6.0/2.6/1.9/29.9 % (the "none" positions are the ones whose windows
hit an error/variant or a repeat; most mates still have unique windows elsewhere).

## 3. Is the unique seed's locus the true one? (mason, truth from the read name: 0-based start of the genome interval and strand; seed locus within 25 bp and same strand)

Per seed length (all windows of that length): window precision 80.8 % (k=16), 98.5 % (20), 99.3 % (24), 99.35 % (28), 99.4 % (32).
Per mate (with a unique window of that length): the LEFTMOST unique window is at the truth for 79.9 % (16), 92.3 % (20),
95.3 % (24), 96.2 % (28), 96.6 % (32) of mates; ALL its unique windows are at the truth for 27.8 / 60.6 / 86.0 / 89.2 / 91.3 %.
Policy "shortest unique length first" (K=32) pins 98.6 % of mates but only 79.3 % of them correctly (the 16-mers dominate);
policy "one fixed length, leftmost" pins 96.0 % at length 32 with 96.6 % correct, 95.8 % at 24 with 95.3 % correct.
Reading: a unique substring is not a proof of the right place. Up to ~4 % of mates (reads from diverged repeat copies whose
exact 24-32-mers match ONE other copy exactly) are pinned to the wrong locus; k=16-20 are unreliable (random hits in 3.1 G x 2 strands:
expected 1.4 random occurrences of a given 16-mer). So a pinned seed is a candidate that must be extended and scored, and
anything claiming "no better alignment elsewhere" still needs the pigeonhole argument (e+1 disjoint seeds, one clean).

## 4. Rough lookup cost (measured latency on this box; the rest is an estimate, not a measurement of a real FM-index)

Random read in a 2 GiB array, one core: 245 ns when dependent (pointer chase), 25 ns when 8 are in flight (VM, no huge pages).
- Our 25-mer minimizer lookup (hg38 NovaSeq, callgrind): ~10.6 lookups per pair, each = bucket offsets + a linear scan of
  ~280 slots + ~26 key matches each needing a genome window read (random, independent, so they overlap): ~300 random accesses per pair
  = 7-70 µs of the ~148 µs CPU per pair. After the word-level match check (branch speed/n31-okat) the scan+check is ~8 % of Ir.
- FM-index backward search (BWA/minibwa style): one dependent random access per extended base. A unique seed needs about
  18-20 steps (section 1) = ~5 µs per attempt unbatched (20 x 245 ns), ~0.5 µs when attempts of many reads are interleaved (25 ns/step);
  an error inside the seed restarts it. Locating the single hit with a sampled suffix array costs about (sampling / 2) more dependent
  steps (~16 at 1/32) = ~4 µs unbatched / 0.4 µs batched. Index: 2-bit BWT + occ ~1.2 GB + SA samples ~0.4-0.8 GB (about 2 GB;
  minibwa's file here is 6.2 GB with its extras; ours is 5.3 GB). Per mate, finding a first unique seed + locating it is therefore
  ~1-10 µs against our ~4-37 µs of lookup+match work per mate (half of the per-pair 7-70 µs). The gain is real only for the 95 % of mates with a unique seed AND only if the
  rest of the pipeline (extension, pairing, tie detection) is kept; it does not remove the router's need for complete seeding on the ~5 % + ties.

## 5. Versus the planned fixed short-seed extra index (DEEP_CAPS.md section 5: 21- or 18-letter minimizer index, 5-6 GB)

- The extra index serves a different goal: completeness at deeper error caps (24/28) from the pigeonhole bound, with a PROOF
  (every true occurrence reported). Variable-length unique seeds give speed for the easy 90-96 % of mates, not completeness; for
  the 17 % of genome positions with no unique substring they give nothing.
- Memory: the extra index adds 5-6 GB on top of 5.3 GB (too much for a 16 GB box with the genome and reads); an FM-style structure is ~2 GB
  but would be a second, differently built index (and a new proved completeness statement for backward search).
- Short unique lengths cluster at 17-20, but at 16-20 the false-hit rate is already 1.5-20 % per window (section 3), so a fixed
  18-21-letter seed in a hash index would meet many random hits per lookup; a 24-letter seed has 99.3 % window precision but
  23 % of positions have no unique 24-mer. That is the trade the variable-length scheme resolves per position (extend until unique), at the price of
  dependent memory steps (245 ns each here) that a hash lookup does not have.
- Suggested use if pursued: not as a replacement of the proved seeding, but as a hint: pin each mate by its first unique >= 24-letter window
  (or a 20-letter one confirmed by a second window on the same diagonal), score it with the existing kernels, and let `tierPair` re-check;
  the router already accepts any untrusted candidate placement. Measure first what fraction of T1/T2 work that would skip.

Caveats: 5000 pairs per set; mason truth tolerance +-25 bp; counts are for this 195-sequence file (a graph/alt-aware reference would have more repeats);
the cost section is a model built from one measured latency and the callgrind counts above, not a run of an FM-index.
