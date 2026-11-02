# Danger regions on full hg38 (`speed/n31-danger`)

Bench only; nothing in the proved path changed. Release `bench-release` (hg38.upper.fa, 195 records, 3,099,922,541 letters);
bench index `whole_genome build` (846,844,994 entries, 782 s, 7.7 GB peak) + `WG_CHECK=1` (check passed, 719 s).
Measured with `Testing/scripts/danger_measure.sh` (`TWIN=0`), bench RTX, `WG_XH=0`, 4 cores (`taskset -c 0-3`), CPU = the bench
RESULT cpu (excludes index load and FASTQ/SAM I/O), median of 3, one run at a time, 200k pairs per set.
**No minibwa comparison is in this note**: minibwa c07de5c is built on the box but these runs measure our own CPU split only.

## Duplicated 150-mers (`Testing/benches/dup_mask.c`)
**5.43%** of hg38 (168,297,452 bases) lies inside an exact duplicated 150-mer, either strand (chr21: 7.0%).
The C tool (canonical rolling hash, hash-partitioned passes, 16 parts) took 35 min on one core, < 5 GB RSS;
byte-identical to `dup_mask.py` on a 4 Mb synthetic genome (python needs ~40 B/base: not possible here).

## Ties and the all-seeds-danger flag (both mates' hitting seeds all in the mask)
| set | ties of 200k | tie CPU / total bench CPU | flagged pairs | flagged ties (catch) | precision | flagged CPU / total |
|---|---|---|---|---|---|---|
| mason | 9,240 (4.6%) | 15.4 s / 66.2 s | 727 | 658 (7.1%) | 90.5% | 0.07 s / 65.0 s (0.11%) |
| low | 9,802 (4.9%) | 8.5 s / 26.6 s | 591 | 572 (5.8%) | 96.8% | 0.06 s / 25.5 s (0.24%) |
| novaseq_200k | 11,929 (6.0%) | 9.5 s / 34.9 s | 1,034 | 506 (4.2%) | 48.9% | 0.07 s / 34.8 s (0.20%) |
| hg002_200k | 9,597 (4.8%) | 7.2 s / 31.8 s | 592 | 292 (3.0%) | 49.3% | 0.05 s / 32.8 s (0.15%) |

(tie CPU + rest CPU from the tie/rest split runs; total from the unsplit run, so they differ by a few percent.)

## Result
- Ties are as costly on hg38 as on chr21 (22–32% of CPU), but the flag catches 3–7% of them (chr21: 57–60%) and the
  flagged pairs cost 0.1–0.2% of CPU. Answering flagged pairs at once saves at most that: **~0.1–0.2% of bench CPU**.
  A per-entry danger bit can only recover this ceiling, so the prototype (step 3) was not built, on the parent's decision.
- On the real read sets (NovaSeq, HG002) half of the flagged pairs are not ties (precision 49%), so an immediate answer
  would also change ~500 non-tie pairs per 200k.
- Likely cause (not tested): hg38 ties sit in diverged repeats (Alu, L1, satellites), not exact 150-mer copies, and a
  25-mer seed usually also occurs somewhere outside the mask, so "all occurrences in the mask" rarely holds.
- Recommendation: drop exact-duplicate danger regions for speed. A tie-focused saving on hg38 needs a different
  signal (e.g. seed multiplicity / bucket size of the rarest seed, already known at lookup).
