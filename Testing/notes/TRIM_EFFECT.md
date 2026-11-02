# Does quality trimming change where we place reads? (NovaSeq 200k, HiSeq 200k)

Same shim at ab3aacd built twice: normal (Spec.trimRecord = proved trimmer) and a LOCAL-ONLY variant with `trimRecord record := record` in
`Spec/Fastq.lean` and `Proofs/Fastq.lean` (Main.lean unchanged; those edits were reverted and are NOT in this branch). Same `shim.idx`,
`map shim.idx R1 R2 out.sam 100 1000`. Script `Testing/fuzz/trim_effect.py`; full reports in `Testing/notes/trim_effect/`.
"unique" = both mates `XU:Z:unique`; "mapped" = both mates mapped and not an all-insertion mate; same place = same chromosome and strand, intervals overlapping (300 bp slack) on both mates.

| | NovaSeq trim | NovaSeq no-trim | HiSeq trim | HiSeq no-trim |
|---|---|---|---|---|
| mapped (non-degenerate) | 95.09 % | 92.97 % | 92.90 % | 84.97 % |
| mapped incl. all-insertion pairs | 97.80 % | 94.11 % | 94.10 % | 85.53 % |
| unique | 81.94 % | 81.51 % | 81.71 % | 70.53 % |
| unmapped mates | 2.20 % | 5.89 % | 5.90 % | 14.47 % |
| non-degenerate mapped pairs with pair score < -50 | 3.68 % | 4.46 % | 3.61 % | 8.35 % |
| ... < -100 | 2.40 % | 2.77 % | 2.62 % | 5.10 % |
| all mapped pairs (incl. all-insertion) < -50 / < -100 | 6.36 / 5.10 % | 5.62 / 3.95 % | 4.83 / 3.84 % | 8.94 / 5.72 % |

(Scores are over kept bases for trim, over full reads for no-trim: not like for like. The all-insertion share is higher with trimming on NovaSeq: 5 434 vs 2 285 pairs.)

| per pair | NovaSeq | HiSeq |
|---|---|---|
| unique in both builds, same place | 162 050 (81.03 %) | 140 823 (70.41 %) |
| **unique in both builds, different place** | **0** | **0** |
| unique only with trimming | 1 827 (0.91 %) | 22 604 (11.30 %) |
| unique only without trimming | 974 (0.49 %) | 237 (0.12 %) |

- **Trimming never moves a pair that is unique in both builds** (0 of 162 050 and 0 of 140 823), so there is nothing to rescore on the full read at two places.
- Unique only with trimming: the no-trim build gives `unknown` for 1 389 (NovaSeq) / 14 542 (HiSeq), and all-insertion or unmapped for 438 / 8 062; those it does map, it puts at the same place for 1 321 of 1 389 and 13 939 of 14 542 (68 and 603 elsewhere). Tiers are mostly `boundsOnly`: without trimming the search gives up at the bound (long 250-bp reads with 3' junk).
- Unique only without trimming: the trim build says `unknown` for 921 / 232 (mostly `boundsOnly`); at the same place for 824 of 921 and 136 of 232, elsewhere for 97 and 96. These are the reads where cutting bases removes seed or score support, 0.49 % and 0.12 % of pairs.
- HiSeq (2x250) benefits much more than NovaSeq (2x151): +8.0 points mapped, +11.2 points unique, pairs below -50 halve. On NovaSeq trimming gains +0.4 points unique and +2.1 points mapped.
- So trimming is net positive on both sets and costs a small unique minority. The 3-5 % of pairs it loses are not placement changes but reads that lose the unique label because fewer bases remain; an earlier finding (REAL_VS_MINIBWA.md section 6) is that 4 of 7 alarming pairs had a cut tail pointing to another copy, so the unique label of a trimmed read can differ from a full-read decision; the full-read decision was never different in placement among the pairs unique in both builds.
