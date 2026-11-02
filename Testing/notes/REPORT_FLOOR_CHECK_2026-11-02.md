# Report-floor branch check: speed/report-floor-proofs @ 1472f46 vs the festive-fermi head (37265c7)

Nothing was pushed to the report-floor branch. Both builds were run from their own binary on the same box (4 cores, shim.idx for hg38), one at a time. The base is
the festive-fermi head `37265c7` (the build before the report floor); the branch is `1472f46` (Spec: `requiredMapBound -16`, `junkScore -50`, degenerate pair removed, exact
pair search at 16 for leftovers). Tools: `Testing/fuzz/compare_runs.py` (new), `audit_vs_minibwa.py`, `sam_fuzz_check.py`, `fuzz_ci.sh`.

## Verdict

- **Correctness of the output: good.** The branch builds; `CI_check.sh` passes (424 theorems, standard axioms only); `fuzz_ci.sh` has zero hard violations, `no-aligned-base` now XPASSes,
  `short-mate` falls from 251 to 60 (still XFAIL). On the hg38 fuzz sets audit rules A-D are 0, no placeholder and no pair with AS1+AS2 < -50 remains, and every one of the base's
  `unique` pairs is unchanged: no suspicious change anywhere.
- **Speed: a very large regression.** The fallback search costs between 30 and several hundred seconds of CPU per 20-30k pairs where the base needs 3-8 s (table below).
  NovaSeq 200k did not finish in 19 minutes (53 CPU-minutes) where the base takes 14 s.
- **The theorem still carries `hNoLeftover`, and real reads violate it**: 416 of 20 000 NovaSeq pairs and 253 of 20 000 HiSeq pairs end as unmapped answers with a bound that is still
  >= -16 (the branch's "leftover"). None on the simulated sets. See the last section.

## 1. Build, CI, `fuzz_ci.sh`

`lake build lean-align` ok; `sh Testing/scripts/CI_check.sh` ALL CHECKS PASSED, `424 theorems, standard axioms only; sorry only in Spec/`.
`sh Testing/scripts/fuzz_ci.sh` (2 917 pairs, 14 s): VIOLATIONS none; XPASS `no-aligned-base` (was 616 records); XFAIL `short-mate` 60 mates (was 251). Delete the
`--xfail=no-aligned-base` flag in `fuzz_ci.sh` when the branch lands.

## 2. hg38 fuzz (3 seeds x mason/low/high, 10k pairs each, one run per mode) and two real sets (first 20k pairs of NovaSeq and HiSeq)

`audit_vs_minibwa.py` on the branch SAMs (rules recompute scores from the reference; see FUZZ_SEEDS_2026-11-02.md):

| rule | mason | low | high |
|---|---|---|---|
| A: AS != recomputed score | 0 | 0 | 0 |
| B: XB < AS1+AS2 | 0 | 0 | 0 |
| C: XB below a minibwa proper pair's score (29 998 / 29 998 / 29 996 scorable pairs) | 0 | 0 | 0 |
| D: unique but minibwa has a proper pair elsewhere scoring >= ours | 0 | 0 | 0 |
| E: unique, minibwa MAPQ 60 elsewhere, truth = minibwa | 0 | 0 | 0 |
| unique pairs not within 10 bp of the true origin | 5 of 26 098 | 4 of 28 435 | 18 of 17 860 |
| mapped pairs with AS1+AS2 < -50, or a placeholder | 0 | 0 | 0 |

`sam_fuzz_check.py` (flags, mates, TLEN, lengths, `*`, provenance...) on all five branch outputs: no violations. Also none on `novaseq` and `hg002` (20k): both XPASS `no-aligned-base`; `short-mate` XFAIL 45 and 115 mates.

## 3. Base -> branch: what changed (pairs)

| set (pairs) | build | printed pair >= -50 | of which unique | placeholder | printed < -50 | unmapped |
|---|---|---|---|---|---|---|
| mason (30 000) | base | 28 627 | 25 882 | 305 | 460 | 608 |
| | branch | 28 975 | 26 098 | 0 | 0 | 1 025 |
| low (30 000) | base | 29 568 | 28 227 | 43 | 330 | 59 |
| | branch | 29 876 | 28 435 | 0 | 0 | 124 |
| high (30 000) | base | 23 999 | 17 749 | 720 | 1 799 | 3 482 |
| | branch | 24 161 | 17 860 | 0 | 0 | 5 839 |
| NovaSeq 20k | base | 18 278 | 16 436 | 587 | 714 | 421 |
| | branch | 18 467 | 16 554 | 0 | 0 | 1 533 |
| HiSeq 20k | base | 17 911 | 16 399 | 243 | 655 | 1 191 |
| | branch | 18 011 | 16 443 | 0 | 0 | 1 989 |

Per pair, `compare_runs.py` classifies every difference (all sets; counts mason / low / high / NovaSeq 20k / HiSeq 20k):

| class | counts | expected? |
|---|---|---|
| unchanged | 29 235 / 29 627 / 27 481 / 18 699 / 19 102 | |
| placeholder -> unmapped | 206 / 11 / 660 / 560 / 218 | yes |
| printed < -50 -> unmapped | 211 / 54 / 1 697 / 552 / 580 | yes |
| placeholder -> real pair >= -50 | 99 / 32 / 60 / 27 / 25 | new (exact search at 16 finds a pair) |
| printed < -50 -> real pair >= -50 | 249 / 276 / 102 / 162 / 75 | new |
| anything else (suspicious) | 0 / 0 / 0 / 0 / 0 | |

Every pair that was `unique` on the base is unchanged on the branch (checked directly: 0 of them differ, including none with a score below -50); the extra unique pairs were not unique before; `unique` counts only grow (+216, +208, +111, +118, +44). The pairs that become real pairs are either at the truth
(`mason x1_s535 base placeholder -612 -> branch -12 chr6:43128478 150M / chr6:43128294 150M`, truth chr6:43128478) or in repeats at another copy (`x1_s981`, `chrX:58672839` vs truth `chrX:59494108`;
these have uniqueness unknown). The price: the mapped-at-all rate drops where reads are noisy (`high` prints 24 161 pairs vs 26 518 = 25 798 + 720 on the base, 2 357 fewer).

## 4. Time of the map step (raw seconds, `lean-align map shim.idx R1 R2 out.sam 100 1000`, default 4 threads, whole run incl. index load)

| set | base wall | base user CPU | branch wall | branch user CPU |
|---|---|---|---|---|
| mason, 30k pairs | 23.0 | 5.5 | 68.7 | 193.9 |
| low, 30k pairs | 7.2 | 3.3 | 390.8 | 879.6 |
| high, 30k pairs | 9.5 | 8.1 | 55.9 | 120.0 |
| NovaSeq, first 20k pairs | 5.8 | 2.6 | 120.0 | 321.0 |
| HiSeq, first 20k pairs | 6.7 | 2.9 | 41.6 | 104.7 |
| NovaSeq, 200k pairs | 14.2 | 28.9 | not finished after 1 151 s wall / 3 190 s CPU (stopped) | |

The index-load part (an empty-FASTQ run of the same binary just before) was 5-44 s (page-cache noise: 44.5 s for the first cold base run), so wall differences below ~10 s are noise;
user CPU is not affected by it (0.0 s for the empty runs). The slowdown is in the fallback: about 29 ms of CPU per pair on `low` (which has only a few percent of pairs that reach it).
It is the largest on the simulated 2x150 `low` set, so it is not only a real-NovaSeq problem.

## 5. The leftover (what the theorem does not cover)

`alignPairs_correct` on this branch carries `hNoLeftover` (no result may be a leftover: unmapped with `bestPossibleScore >= requiredMapBound = -16`). Counting such answers in the SAMs
(`XB:i` >= -16 on an unmapped pair):

| set | base | branch |
|---|---|---|
| mason / low / high (30k each) | 0 / 0 / 0 | 0 / 0 / 0 |
| NovaSeq, first 20k pairs | 0 | **416** (386 boundsOnly, 30 stoppedEarly; 293 with XB = 0) |
| HiSeq, first 20k pairs | 0 | **253** (228 boundsOnly, 24 stoppedEarly, 1 deepSearchTie; 220 with XB = 0) |

So on real reads the hypothesis fails for 2.1 % and 1.3 % of the pairs: they are printed unmapped with an honest but weak bound, which the Spec has no answer for
(the branch's own suggestion: a `.gaveUp` answer whose `Correct` clause is only the bound). On the base these pairs were either printed as placeholders or as pairs below -50.
