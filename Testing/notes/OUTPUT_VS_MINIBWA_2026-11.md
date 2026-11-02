# lean-align (M2) output vs minibwa, hg38, 2026-11-02

What was run: `origin/m2/placements` @ 7d5571e (M2 stage 5, built locally with Lean 4.35; `origin/main`'s newer
`Spec/Aligner.lean` with `junkScore` was NOT merged: it makes the `.unknown` case demand `found = none → bound < junkScore`,
which the M2 proofs do not know yet). Shim: `lean-align map shim.idx R1 R2 out.sam 100 1000`. minibwa c07de5c, default
`map -t 4`, release index. samtools/htslib 1.24. All four 200k-pair sets of the release: `hg38_mason` and `hg38_low`
(simulated 2x150, true positions in the read names), `hg002_200k` (real HiSeq 2x250), `novaseq_200k` (real NovaSeq 2x151).
(The fifth set, `hg002_1M`, has the same first 200k pairs as `hg002_200k`, so it adds nothing.)
Rebuild: `sh Testing/scripts/output_vs_minibwa.sh OUTDIR hg38_mason hg38_low hg002_200k novaseq_200k` (writes
`analysis.md`, flagstat, stats, idxstats per set; `KEEP=1` keeps the SAMs). Analysis: `Testing/scripts/output_vs_minibwa.py`.
Percentages are of all 200 000 pairs unless said otherwise.

## 1. Mapped and unique, ours vs minibwa

| set | ours: both mates mapped | ours: XU:Z:unique | minibwa: both mapped | proper (0x2) | pair MAPQ >= 30 | pair MAPQ = 60 |
|---|---|---|---|---|---|---|
| hg38_mason | 93.98 % | 88.22 % | 100.00 % | 99.99 % | 96.14 % | 90.35 % |
| hg38_low | 98.11 % | 94.61 % | 100.00 % | 99.99 % | 96.29 % | 90.63 % |
| hg002_200k | 79.00 % | 70.53 % | 99.57 % | 98.06 % | 92.50 % | 87.57 % |
| novaseq_200k | 88.77 % | 81.97 % | 99.08 % | 97.62 % | 91.23 % | 85.15 % |

(pair MAPQ = lower mate's MAPQ. Ours prints MAPQ 60 for unique and 0 for everything else, so for ours MAPQ >= 30 = MAPQ 60 =
unique, and our proper-pair % equals our mapped %: we only ever print a proper pair, never a half-mapped one.)
Of minibwa's pairs with MAPQ >= 30 we map / mark unique: mason 95.50 % / 91.59 %, low 99.18 % / 97.96 %,
hg002 83.36 % / 76.06 %, novaseq 93.49 % / 89.43 %. Of OUR unique pairs, minibwa has MAPQ >= 30 for 99.82 % (mason),
99.70 % (low), 99.75 % (hg002), 99.53 % (novaseq).

## 2. Our unique pairs vs minibwa's placement (both mates compared)

| our unique pairs | mason | low | hg002 | novaseq |
|---|---|---|---|---|
| pairs | 176 444 | 189 228 | 141 060 | 163 941 |
| same chrom/pos/strand AND same CIGAR | 98.59 % | 99.64 % | 98.19 % | 99.66 % |
| same chrom/pos/strand, CIGAR differs | 1 247 (0.71 %) | 329 (0.17 %) | 1 240 (0.88 %) | 266 (0.16 %) |
| minibwa soft-clips an end, ours end to end | 1 220 (0.69 %) | 326 (0.17 %) | 1 296 (0.92 %) | 246 (0.15 %) |
| off by 1-2 bases (no clipping) | 15 | 11 | 8 | 23 |
| 3-50 bp apart (no clipping) | 2 | 3 | 7 | 10 |
| different locus (other chrom / > 50 bp) | 2 / 1 | 2 / 1 | 4 / 4 | 4 / 8 |
| different strand | 0 | 2 | 1 | 3 |

What the disagreements are (examples in each `analysis.md`):
- **Clipped ends**: minibwa reports a local alignment (`8S142M`, `147M3S`); ours is end to end (`150M`) with a mismatch-rich
  end. On the simulated sets the true position settles who is right: mason, 1 216 of the 1 220 clipped pairs have ours at
  the true position and minibwa off by the clip length (4 both off); low, 253 ours at truth / 9 minibwa at truth / 64 both off.
  This is a scoring-policy difference (end-to-end vs local), not a placement error on our side.
- **Same placement, CIGAR differs** (0.2-0.9 %): the same clipping at the other mate, or an indel represented differently.
- **Off by 1-2 bases**: in the examples a read with an indel near its start, where minibwa places `5M2I143M` and ours `150M` (not checked for all of them).
  Mason: all 15 have ours at the true position. Low: 7 pairs minibwa at truth, ours not, 1 the other way.
- **Different locus / strand** (4-15 pairs per set): mason ours at truth in all 3; low: ours at truth in 4 of 5 (the fifth both off).
- Mates with both mates identical in placement: FLAG differs on 2 / 0 / 28 / 1 mates (mason / low / hg002 / novaseq),
  RNEXT on 0 / 0 / 2 / 1, PNEXT on 1 236 / 340 / 1 312 / 280, TLEN on 128 / 189 / 290 / 337 (all because the *other* mate
  is clipped or placed differently), MAPQ on 13 137 / 14 144 / 7 248 / 12 116 (see section 3).

## 3. Format differences, side by side (samtools)

| | ours | minibwa |
|---|---|---|
| header | `@HD VN:1.6 SO:unsorted`, 195 `@SQ`, `@PG lean-align` | `@HD ... GO:query`, `@PG` with command line |
| flags in use (mate 1) | 99, 83 (proper pairs), 77 (both unmapped) | 99, 83, plus 73, 89, 97, 65, 81, 113, 69, 101, 77 (half-mapped and improper pairs), and 2048/256 records |
| MAPQ | only 0 or 60 | graded (60, 52, 48, ... 0) |
| CIGAR | `M`, `I`, `D`, end to end only | also `S` (and `H`) |
| AS | negative penalty (e.g. `-4`) | positive alignment score (e.g. `462`) |
| tags | `AS XB XU XT` | `NM AS ms md MC MQ n2 XA SA` |
| NM / MD | none (`samtools calmd` adds them; done here) | `NM` yes, `md:i` is a number, not the MD string |
| mate fields | RNEXT `=`, PNEXT, TLEN as in the spec | same convention; TLEN differs only when a mate's end differs |
| extra records | none | hg002 4 954 and novaseq 2 244 supplementary/secondary lines (flagstat total 404 954, 402 244; 1 in mason) |

`samtools flagstat` (primary mapped / properly paired / singletons / mate on another chromosome):

| set | ours | minibwa |
|---|---|---|
| hg38_mason | 375 908 / 375 908 / 0 / 0 | 400 000 / 399 950 / 0 / 14 |
| hg38_low | 392 440 / 392 440 / 0 / 0 | 400 000 / 399 978 / 0 / 8 |
| hg002_200k | 315 986 / 315 986 / 0 / 0 | 398 849 / 392 244 / 557 / 3 794 |
| novaseq_200k | 355 072 / 355 072 / 0 / 0 | 397 716 / 390 478 / 1 404 / 4 204 |

`samtools stats` after sort (ours with NM/MD from `samtools calmd` against hg38.upper.fa), ours | minibwa:

| set | error rate | insert size mean / sd | reads MQ0 | bases mapped (cigar) | inward / outward / other / diff-chrom pairs |
|---|---|---|---|---|---|
| mason | 1.258e-2 \| 1.173e-2 | 299.3 / 29.2 \| 299.2 / 29.1 | 23 020 \| 10 074 | 56.4 M \| 60.0 M | 187 954/0/0/0 \| 199 984/9/0/7 |
| low | 5.78e-3 \| 4.54e-3 | 398.0 / 77.7 \| 397.9 / 77.4 | 13 984 \| 9 712 | 58.9 M \| 60.0 M | 196 220/0/0/0 \| 199 992/4/0/4 |
| hg002 | 7.00e-3 \| 9.03e-3 | 406.8 / 77.9 \| 401.6 / 91.1 | 33 866 \| 15 004 | 79.0 M \| 97.5 M | 157 993/0/0/0 \| 193 704/3 401/144/1 897 |
| novaseq | 6.28e-3 \| 6.18e-3 | 400.7 / 156.8 \| 401.3 / 166.1 | 27 190 \| 17 188 | 53.6 M \| 59.5 M | 177 536/0/0/0 \| 194 483/1 422/149/2 102 |

`samtools idxstats`: mapped reads per chromosome, sum of |ours - minibwa| over chromosomes: mason 24 765 of 400 001,
low 9 354 of 400 000, hg002 88 671 of 403 803, novaseq 46 396 of 399 960; the largest single-chromosome gaps
are on the large chromosomes (chr1, chr2, chr4, chrX); I did not test whether any chromosome is over- or under-represented relative to its length.
Our error rate is higher than minibwa's on the two simulated sets and lower on real HiSeq; not investigated (two candidate reasons: we align
clipped ends end to end and count their mismatches; on HiSeq we skip the 21 % of pairs that are not mapped).

## 4. Pairs we place badly: what minibwa does with the same read names

"Fallback / XB:i:0" = we print a pair with uniqueness unknown and bound 0 (last resort); "unmapped" = both mates `*`.
Columns for minibwa; MAPQ columns are the lower mate over pairs where minibwa maps both mates, as % of the group.

**hg38_mason**

| our pairs | n | minibwa maps both | proper | MAPQ 0 | 1-9 | 10-29 | 30-59 | 60 | XA | SA | same placement as ours |
|---|---|---|---|---|---|---|---|---|---|---|---|
| mapped, unknown, XB:i:0 | 6 350 | 100.00 % | 99.86 % | 43.65 % | 3.80 % | 14.30 % | 21.10 % | 17.15 % | 50.60 % | 0.00 % | 36.69 % |
| mapped, unknown, XB < 0 | 5 160 | 100.00 % | 99.98 % | 0.52 % | 0.35 % | 0.72 % | 5.41 % | 93.00 % | 3.99 % | 0.00 % | 92.85 % |
| unmapped, XB:i:0 | 4 034 | 100.00 % | 99.68 % | 50.00 % | 7.24 % | 17.75 % | 20.10 % | 4.91 % | 42.14 % | 0.00 % | - |
| unmapped, XB < 0 | 8 012 | 100.00 % | 99.99 % | 2.81 % | 0.39 % | 1.35 % | 6.80 % | 88.65 % | 6.80 % | 0.01 % | - |

**hg38_low**

| our pairs | n | minibwa maps both | proper | MAPQ 0 | 1-9 | 10-29 | 30-59 | 60 | XA | SA | same placement as ours |
|---|---|---|---|---|---|---|---|---|---|---|---|
| mapped, unknown, XB:i:0 | 6 648 | 100.00 % | 99.94 % | 51.62 % | 4.11 % | 13.93 % | 23.41 % | 6.93 % | 56.02 % | 0.00 % | 29.59 % |
| mapped, unknown, XB < 0 | 344 | 100.00 % | 100.00 % | 2.33 % | 0.87 % | 1.45 % | 5.81 % | 89.53 % | 5.23 % | 0.00 % | 83.72 % |
| unmapped, XB:i:0 | 3 106 | 100.00 % | 99.77 % | 45.24 % | 8.15 % | 16.68 % | 22.38 % | 7.57 % | 36.83 % | 0.00 % | - |
| unmapped, XB < 0 | 674 | 100.00 % | 100.00 % | 2.23 % | 0.15 % | 1.78 % | 7.57 % | 88.28 % | 7.72 % | 0.00 % | - |

**hg002_200k**

| our pairs | n | minibwa maps both | proper | MAPQ 0 | 1-9 | 10-29 | 30-59 | 60 | XA | SA | same placement as ours |
|---|---|---|---|---|---|---|---|---|---|---|---|
| mapped, unknown, XB:i:0 | 8 199 | 99.83 % | 98.68 % | 29.37 % | 2.24 % | 5.49 % | 8.18 % | 54.54 % | 27.97 % | 3.07 % | 48.98 % |
| mapped, unknown, XB < 0 | 8 734 | 99.67 % | 98.07 % | 1.35 % | 1.06 % | 1.45 % | 6.64 % | 89.16 % | 6.50 % | 3.09 % | 66.85 % |
| unmapped, XB:i:0 | 3 039 | 99.61 % | 97.56 % | 54.72 % | 5.43 % | 12.04 % | 7.50 % | 19.91 % | 28.33 % | 0.33 % | - |
| unmapped, XB < 0 | 38 968 | 97.95 % | 90.99 % | 9.42 % | 7.58 % | 4.10 % | 10.67 % | 66.18 % | 16.74 % | 7.55 % | - |

**novaseq_200k**

| our pairs | n | minibwa maps both | proper | MAPQ 0 | 1-9 | 10-29 | 30-59 | 60 | XA | SA | same placement as ours |
|---|---|---|---|---|---|---|---|---|---|---|---|
| mapped, unknown, XB:i:0 | 10 193 | 99.47 % | 96.08 % | 39.39 % | 6.41 % | 8.84 % | 16.38 % | 28.45 % | 37.24 % | 1.69 % | 37.43 % |
| mapped, unknown, XB < 0 | 3 402 | 97.47 % | 89.74 % | 5.23 % | 5.17 % | 3.94 % | 14.87 % | 68.25 % | 16.58 % | 3.17 % | 63.52 % |
| unmapped, XB:i:0 | 5 328 | 98.93 % | 88.66 % | 54.67 % | 12.33 % | 10.89 % | 8.58 % | 12.46 % | 29.64 % | 3.25 % | - |
| unmapped, XB < 0 | 17 136 | 90.39 % | 80.14 % | 10.64 % | 11.51 % | 5.40 % | 13.36 % | 49.47 % | 22.74 % | 7.35 % | - |

Reading: the bound-0 groups are the repeat-like pairs: minibwa maps all of them but gives MAPQ 0 to 30-55 % and has an
`XA` alternative-hit list on 28-56 % (the real multimappers; SA is rare, so those are not chimeric). Our fallback pair
agrees with minibwa's primary placement for only 30-49 % of them (ties are broken differently). The groups with a negative
bound (XB < 0) are the opposite: minibwa maps them confidently (MAPQ 60 for 49-93 %), so these are pairs the router could
not finish within its budget, not repeats; this is the main sensitivity gap: `unmapped, XB < 0` is 4.0 % of mason,
19.5 % of hg002 and 8.6 % of novaseq pairs, and for the HiSeq/NovaSeq sets minibwa maps them 98 % / 90 %, 66 % / 49 % with MAPQ 60.

**Repeat-masked (lowercase) hg38: NOT done.** The release holds only `hg38.upper.fa`. The soft-masked FASTA comes from
`https://ngi-igenomes.s3.amazonaws.com/.../WholeGenomeFasta/genome.fa` (3.1 GB; Rowan allowed the download) but this
session's network policy denied that host (HTTP 403 on CONNECT), so no masked sequence was available. Everything else in
this note is measured; this item is open. Plan once the host is allowed: per chromosome, collect the lowercase runs,
compute for each minibwa placement the fraction of its reference span that is lowercase (>= 50 %, >= 90 %, any), and report
it per group above with the all-pairs and our-unique-pairs baselines.

## 5. BAM (stored BGZF prototype) on the M2 output

`bam_write` on this branch, real results, 200 000 pairs, 3 repetitions each (raw seconds; SAM text vs BAM stored):

| set | SAM bytes | BAM bytes | SAM format+write wall (3 runs) | BAM format+write wall (3 runs) | CPU SAM / BAM |
|---|---|---|---|---|---|
| hg38_mason | 176 871 157 | 140 953 887 | 0.986, 0.973, 1.054 s | 1.044, 1.099, 1.241 s | 2.87, 2.77, 2.86 / 3.29, 3.24, 3.33 s |
| hg002_200k | 249 069 720 | 195 055 438 | 1.169, 1.454, 1.238 s | 1.409, 2.190, 2.112 s | 3.62, 4.11, 3.38 / 4.43, 5.56, 6.01 s |

(alignPairs wall for the same pairs: 19.3 s mason, 9.2 s hg002; not part of the output timing.) With M2 records (CIGAR,
mate fields, 4 tags) the BAM writer is closer to the SAM writer than at M1 (mason: about 0.06-0.2 s longer, 20 % fewer bytes)
but still not faster. Validation: Python field-by-field checker OK (400 000 records each); `samtools quickcheck` rc 0;
`view -c` 400000; `flagstat` identical to the SAM (375 908 / 315 986 mapped and properly paired); `samtools view -h` of the
BAM equals our SAM except for the `@PG ID:samtools` line samtools adds; the BAM's SAM records equal the shim's output byte for byte.
BAM stays shelved.

## What stands out (for whoever picks this up)

1. Where we map uniquely we agree with minibwa to the base on 98.2-99.7 % of pairs, and wherever they differ on simulated
   reads we are at the true position more often (1 216 of 1 220 clipped pairs on mason).
2. The gap is coverage, not accuracy: pairs mapped 79-98 % vs 99-100 %. The biggest block is `unmapped, XB < 0` (router gave up
   within budget while minibwa maps it with MAPQ 60), 38 968 pairs in hg002 alone.
3. MAPQ: ours is 0/60 only; of the mates both tools place identically, 2.6-3.7 % still differ in MAPQ against minibwa's graded values (13 137 / 14 144 / 7 248 / 12 116 mates, mason / low / hg002 / novaseq).
4. `samtools calmd`-recomputed NM/MD would be needed for tools that expect them; minibwa's `md:i` is not the SAM MD string.
