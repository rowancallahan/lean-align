# Semi-repetitive pairs on real reads (NovaSeq 2x151, HiSeq 2x250, 200k pairs each)

Build: `speed/gaveup2-fast` ff61781 with `gaveUpRepeats = 200` (`gaveUpSeeds = 2` already) set LOCALLY, plus a LOCAL debug print (`dbgTrace` in `afterLeftoverDbg`, bound to `afterLeftover` by
`implemented_by`, so no proof changes) that prints every pair reaching `lookAtG`: both trimmed mates, the occurrence count of each 25-mer grid seed (`GaveUp.seedCount`, genome both strands, inside chromosomes),
and the number of candidate places (mate 1's hits within the cap, mate 2's hits near them). **Those edits were not pushed**; this branch has only this note and the scripts (`Testing/fuzz/semi_repetitive.py`; full reports in `Testing/notes/semi_repetitive/`).
Real reads, hg38 release index, minibwa c07de5c `map -t 4` for the comparison. A pair is "selected" when it reaches the complete search (not answered by the router, the walks, the join) and has fewer than 2 grid seeds at >= 200 occurrences in either mate, i.e. exactly the pairs the repeat rule does NOT give up on. Duplicated trace lines (same pair twice) are removed.

## What the selected pairs are

| | NovaSeq | HiSeq |
|---|---|---|
| pairs reaching the complete search, not highly repetitive | 5 257 (2.6 %) | 2 708 (1.4 %) |
| of those: pair found >= -100 | 225 (4.3 %) | 211 (7.8 %) |
| of those: unmapped, bound below the floor ("proved none", tier boundsOnly) | 4 593 (87 %) | 2 178 (80 %) |
| of those: gave up on the places rule (>= 50 places, label gaveUp) | 439 (8.4 %) | 319 (11.8 %) |
| "semi-repetitive": max seed occurrence >= 20 in some mate | 2 491 (47 %) | 1 657 (61 %) |
| ... of which exactly one seed >= 200 | 1 292 | 908 |

(The three rows add up to the pair count in each set.)

**Distributions** (per mate, both mates counted; full tables in the two reports)
- Max seed occurrence per mate: NovaSeq 0: 3 183, 1: 2 141, 2-4: 753, 5-9: 537, 10-19: 482, **20-49: 791, 50-99: 459, 100-149: 251, 150-199: 383**, 200+: 1 534. HiSeq 0: 1 081, 1: 916, 2-4: 405, 5-9: 313, 10-19: 354, **20-49: 628, 50-99: 328, 100-149: 155, 150-199: 144**, 200+: 1 092.
- Grid seeds at >= 200 per mate: 0 in 8 980 / 4 324 mates, 1 in 1 534 / 1 092 mates (2+ is excluded by construction).
- Mate length after trimming: NovaSeq < 50: 595, 50-99: 1 031, 100-139: 1 167, 140-199: 7 721; HiSeq < 50: 324, 50-99: 534, 100-139: 397, 140-199: 1 041, 200-249: 2 609, 250: 511. About 16 % of the selected mates (both sets) are under 100 letters after trimming.
- Candidate places for mate 1 within the cap: NovaSeq 0: 2 271, 1: 547, 2-4: 238, 5-9: 431, 10-19: 538, 20-49: 878, 50+: 354; HiSeq 0: 1 128, 1: 230, 2-4: 182, 5-9: 265, 10-19: 282, 20-49: 364, 50+: 257. Mate 2 near mate 1 is mostly 0 (3 751 / 1 746).
- minibwa on the same pairs: NovaSeq MAPQ 60 45 %, 30-59 11 %, 1-29 19 %, 0 16 %, unmapped or one mate 8 %; HiSeq MAPQ 60 44 %, 30-59 15 %, 1-29 19 %, 0 21 %, unmapped 2 %. minibwa gives an XA list on 25 % / 28 %. Where we found a pair, minibwa agrees on the place for 207 of 225 (NovaSeq) and 175 of 211 (HiSeq); where we have none (unmapped), minibwa has MAPQ >= 30 for 2 821 of the 5 032 unmapped NovaSeq pairs and 1 386 of the 2 178 HiSeq proved-none pairs.

## Reading it (for the trick design)

1. **Most selected pairs are not semi-repetitive at all.** Roughly half the mates have a max seed count of 0-1: short mates after trimming, or reads with errors every few bases, so no 25-mer hits. The complete search for them costs little (0-1 candidate places) and ends in "proved none"; minibwa maps a good share by clipping (`113S38M`, `153S41M1D52M4S`). An extra k-mer index of repeats would not help these; a smaller seed or the clipped-end local alignment would.
2. **The truly semi-repetitive pairs (max seed 20-199, plus those with a single >= 200 seed) are 47 % / 61 % of the selected pairs and are mostly the expensive ones:** 20-400 candidate places per mate, each a banded check. They sit in chrY, chrUn and the `_random` contigs, chr1 pericentromere, and tandem copies. 77-81 % end as "proved none", 14-15 % as gave up on the places rule, 5-8 % as a found pair; minibwa gives MAPQ 0 or 1-29 to 51-57 % of them (a real multimapper), MAPQ 60 to 26-32 %.
3. **Where a decent pair exists it is usually found quickly** (`bestUnchecked`): short mate pinned to a unique long mate (mate 1 38-62 bp with a seed hitting 20-124 places; the partner is unique, so one candidate place survives).
4. **The cost is the product, not the single seed:** a seed with 140-350 hits on one mate and 20-50 near-hits on the other means hundreds of banded checks per pair; pairs with two seeds at 20-60 hits are as expensive as one with a single 200+ seed.

## Examples (real reads; occurrences per 25-mer grid seed in brackets, `s0` is the first seed at read offset 0, `s1` at 25, ...)

NovaSeq 2x151, 12 pairs (the last three are non-repetitive pairs for contrast):

### `A00744:46:HV3C3DSXX:2:1103:30427:24314`
```
mate1 144 bp [s0:9][s1:0][s2:11][s3:20][s4:10]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:3][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 95 candidate places for mate 1 within the cap, 109 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp stoppedEarly
minibwa: chrY:11576021+ 151M / chrY:11576288- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 1 hits 20 places and each hit needs a banded check; 95 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:16685:31203`
```
mate1 151 bp [s0:0][s1:40][s2:21][s3:28][s4:21][s5:15]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:1][s3:0][s4:0][s5:3]
complete search: 130 candidate places for mate 1 within the cap, 15 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp boundsOnly
minibwa: chrUn_KI270754v1:31475+ 151M / chrUn_KI270754v1:31704- 151M  MAPQ 0/0  XA
```
Why expensive: the busiest seed of mate 1 hits 40 places and each hit needs a banded check; 130 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1104:7193:4961`
```
mate1 151 bp [s0:31][s1:27][s2:0][s3:27][s4:27][s5:286]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 116 candidate places for mate 1 within the cap, 127 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp stoppedEarly
minibwa: chrY:56703542+ 151M / chrY:56703723- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 1 hits 286 places and each hit needs a banded check; 116 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:24325:35133`
```
mate1  44 bp [s0:22]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:1][s1:1][s2:1][s3:1][s4:1][s5:1]
complete search: 1 candidate places for mate 1 within the cap, 1 for mate 2 near them
ours:    chr17:5220433- 44M / chr17:5220167+ 151M  AS 0+0  unknown bestUnchecked
minibwa: chr17:5220433- 107S44M / chr17:5220167+ 151M  MAPQ 50/60  XA
```
Why expensive: the busiest seed of mate 1 hits 22 places and each hit needs a banded check.

### `A00744:46:HV3C3DSXX:2:1103:18602:33051`
```
mate1 151 bp [s0:0][s1:28][s2:73][s3:43][s4:0][s5:1]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:39][s1:38][s2:34][s3:142][s4:63][s5:0]
complete search: 22 candidate places for mate 1 within the cap, 49 for mate 2 near them
ours:    chr1_KI270709v1_random:11374- 151M / chr1_KI270709v1_random:11272+ 151M  AS -8+-4  unknown bestUnchecked
minibwa: chr1_KI270709v1_random:11374- 151M / chr1_KI270709v1_random:11272+ 151M  MAPQ 0/0  XA
```
Why expensive: the busiest seed of mate 2 hits 142 places and each hit needs a banded check; 22 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:14913:27101`
```
mate1 151 bp [s0:30][s1:41][s2:19][s3:0][s4:5][s5:22]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:25][s1:8][s2:349][s3:0][s4:40][s5:14]
complete search: 24 candidate places for mate 1 within the cap, 45 for mate 2 near them
ours:    chr1:143216744+ 151M / chr1:143216951- 150M  AS -8+-8  unknown bestUnchecked
minibwa: chr1:143216744+ 151M / chr1:143216950- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 2 hits 349 places and each hit needs a banded check; 24 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:29197:22842`
```
mate1 151 bp [s0:0][s1:0][s2:2][s3:0][s4:0][s5:0]   (occurrences per 25-mer grid seed)
mate2 129 bp [s0:0][s1:3][s2:0][s3:20][s4:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr5:49658642+ 10M5D131M10S / chr5:49658601- 62S89M  MAPQ 33/41
```
Why expensive: the busiest seed of mate 2 hits 20 places and each hit needs a banded check.

### `A00744:46:HV3C3DSXX:2:1103:19461:26678`
```
mate1 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:3]   (occurrences per 25-mer grid seed)
mate2 145 bp [s0:11][s1:141][s2:1][s3:0][s4:0]
complete search: 13 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr8:119408566- 151M / chr8:119407609+ 151M  MAPQ 60/60
```
Why expensive: the busiest seed of mate 2 hits 141 places and each hit needs a banded check; 13 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:5014:26052`
```
mate1 148 bp [s0:4][s1:0][s2:1185][s3:0][s4:0]   (occurrences per 25-mer grid seed)
mate2 143 bp [s0:0][s1:0][s2:2][s3:15][s4:0]
complete search: 13 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr2:179247336- 151M / chr18:47666396+ 59S34M58S  MAPQ 60/29
```
Why expensive: the busiest seed of mate 1 hits 1185 places and each hit needs a banded check; 13 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:27832:34413`
```
mate1  35 bp [s0:0]   (occurrences per 25-mer grid seed)
mate2  25 bp [s0:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr1:68228886+ * / chr1:68228886- 18S31M102S  MAPQ 0/1  XA
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

### `A00744:46:HV3C3DSXX:2:1104:25907:1548`
```
mate1 147 bp [s0:0][s1:0][s2:0][s3:0][s4:0]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:3][s1:0][s2:0][s3:0][s4:1][s5:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr8:138974031- 151M / chr8:138973543+ 151M  MAPQ 60/60
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

### `A00744:46:HV3C3DSXX:2:1104:25970:2253`
```
mate1 151 bp [s0:1][s1:1][s2:1][s3:1][s4:1][s5:0]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 6 candidate places for mate 1 within the cap, 8 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr9:6870056+ 147M4S / chr9:6870055- 3S148M  MAPQ 60/60
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

HiSeq 2x250, 6 pairs:

### `HISEQ1:93:H2YHMBCXX:1:1116:19980:47610`
```
mate1 249 bp [s0:3][s1:9][s2:12][s3:13][s4:14][s5:1][s6:7][s7:10][s8:6]   (occurrences per 25-mer grid seed)
mate2 245 bp [s0:0][s1:3][s2:1][s3:20][s4:3][s5:0][s6:3][s7:3][s8:3]
complete search: 31 candidate places for mate 1 within the cap, 50 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp stoppedEarly
minibwa: chr14_KI270725v1_random:74567+ 250M / chr14_KI270725v1_random:74788- 250M  MAPQ 49/46  XA
```
Why expensive: the busiest seed of mate 2 hits 20 places and each hit needs a banded check; 31 candidate places for mate 1 inside the cap.

### `HISEQ1:93:H2YHMBCXX:1:1116:12807:48103`
```
mate1 247 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0][s6:0][s7:9][s8:0]   (occurrences per 25-mer grid seed)
mate2 247 bp [s0:28][s1:27][s2:0][s3:0][s4:23][s5:68][s6:0][s7:26][s8:28]
complete search: 102 candidate places for mate 1 within the cap, 24 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp boundsOnly
minibwa: chrY:56757045- 250M / chrY:56756966+ 250M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 2 hits 68 places and each hit needs a banded check; 102 candidate places for mate 1 inside the cap.

### `HISEQ1:93:H2YHMBCXX:1:1116:11533:52890`
```
mate1 249 bp [s0:27][s1:26][s2:2][s3:23][s4:24][s5:0][s6:22][s7:552][s8:27]   (occurrences per 25-mer grid seed)
mate2 208 bp [s0:0][s1:0][s2:0][s3:2][s4:1][s5:0][s6:0][s7:0]
complete search: 17 candidate places for mate 1 within the cap, 52 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp boundsOnly
minibwa: chrY:56675020+ 250M / chrY:56675146- 5S245M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 1 hits 552 places and each hit needs a banded check; 17 candidate places for mate 1 inside the cap.

### `HISEQ1:93:H2YHMBCXX:1:1116:8126:53620`
```
mate1  55 bp [s0:20][s1:11]   (occurrences per 25-mer grid seed)
mate2 241 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0][s6:0][s7:0][s8:0]
complete search: 1 candidate places for mate 1 within the cap, 1 for mate 2 near them
ours:    chr19:16659250+ 55M / chr19:16659370- 241M  AS 0+-4  unknown bestUnchecked
minibwa: chr19:16659250+ 76M174S / chr19:16659361- 250M  MAPQ 60/60
```
Why expensive: the busiest seed of mate 1 hits 20 places and each hit needs a banded check.

### `HISEQ1:93:H2YHMBCXX:1:1116:12736:42888`
```
mate1  62 bp [s0:124][s1:15]   (occurrences per 25-mer grid seed)
mate2 181 bp [s0:1][s1:1][s2:1][s3:1][s4:1][s5:1][s6:3]
complete search: 1 candidate places for mate 1 within the cap, 1 for mate 2 near them
ours:    chr4:25802731- 62M / chr4:25802463+ 181M  AS 0+0  unknown bestUnchecked
minibwa: chr4:25802543- 250M / chr4:25802461+ 250M  MAPQ 60/60
```
Why expensive: the busiest seed of mate 1 hits 124 places and each hit needs a banded check.

### `HISEQ1:93:H2YHMBCXX:1:1116:2475:62726`
```
mate1  38 bp [s0:11]   (occurrences per 25-mer grid seed)
mate2 147 bp [s0:14][s1:24][s2:556][s3:159][s4:123]
complete search: 5 candidate places for mate 1 within the cap, 1 for mate 2 near them
ours:    chr15:50485552- 38M / chr15:50485186+ 147M  AS 0+0  unknown bestUnchecked
minibwa: chr15:50485552- 212S38M / chr15:50485185+ 208M42S  MAPQ 48/60
```
Why expensive: the busiest seed of mate 2 hits 556 places and each hit needs a banded check.
