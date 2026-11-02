# WFA in the tier 2 heuristic, on hg38 (box S1, 4 cores, 15 GB; branch speed/n31-wfa)

## What was added
`bandWfa` (Aligner/mapper/TierHeur.lean): banded semi-global gap-affine wavefronts, same contract as `bandDP`
(mismatch 4, gap 6 + 2L, free window ends, band ± w). Penalties are even, so levels are halved (mismatch 2, first gap
letter 4, extension 1). Per level and diagonal: furthest read row (M/I/D, stored row+1); levels kept for the traceback;
first diagonal reaching the read end at the lowest level wins (as `bandDP`'s first minimum). Unproved: every alignment
it reports is still re-scored by the router (`checkRuns`/`tierPair_sound`).
**Turn on:** `WG_XHWFA=1` (bench; `HCfg.wfa := true`). Default off. Used by all three `bandDP` call sites of `heurP` / `nearY`.
Not on the `alignPairs` path (heuristic off there); the shim output is unchanged.

## hg38 measurements (bench index, `WG_XH=1 WG_XHC=16 WG_XHCHK=0 WG_XHCK=100`, taskset 0-3, 4 interleaved runs per arm)
| set | kept (both arms) | wall s off / on (median) | CPU s off / on (median) |
|---|---|---|---|
| mason | 175836 | 15.63 / 15.02 | 61.1 / 59.2 |
| low | 191379 | 6.17 / 5.82 | 24.2 / 22.7 |
| NovaSeq | 167730 | 8.21 / 7.96 | 32.2 / 31.3 |
| HiSeq (hg002) | 166423 | 7.39 / 7.34 | 29.0 / 28.7 |
Kept pairs identical in all 32 runs (no drop). CPU −1 … −6%, within the run-to-run spread (individual CPU values overlap).

## Why it cannot matter at 150–250 bp (callgrind, WFA off, 3000 mason + 3000 NovaSeq pairs, tierPair only)
8.87 G Ir (1.48 M Ir/pair). `heurP` 2.14% inclusive; `bandDP` 0.86% (`bandCells` 0.62%); `nearY` 0.67%; `hamD` 0.44%.
Ceiling for any bandDP replacement: < 1% of Ir. Larger: scanAWK 12.7%, stageKSP 8.0%, kerGKG 5.3%, lanesAnyU 4.6%,
List.mergeSort ~6%, malloc/free ~7%. (chr21 earlier showed bandDP at 27% of the heuristic's time; on hg38 the heuristic is 2% of the total, so the share of the whole is small.) The cost of `bandWfa` grows with the penalty, not the read length, so
it is meant for very long reads, where a read-length-proportional DP is the bottleneck.

## Speed vs minibwa c07de5c on this box (shim = default settings, heuristic off; raw seconds, median of 3 after a warm-up; SAM to file)
Load-subtracted: minibwa wall − its "index loaded" time; shim wall − wall of the same run on empty FASTQ. FASTQ read and SAM write included.
| set | minibwa default s | minibwa native s | shim s | minibwa def / ours |
|---|---|---|---|---|
| mason | 16.1 | 17.0 | 19.5 | 0.83x (slower) |
| low | 10.8 | 10.5 | 7.1 | 1.52x |
| NovaSeq | 14.7 | 13.9 | 15.4 | 0.95x (slower) |
| HiSeq | 29.4 | 29.0 | 11.9 | 2.47x |
End to end (with index load): mason 27.3 / 25.7 / 28.0; low 17.9 / 18.3 / 14.3; NovaSeq 23.5 / 24.1 / 18.4; HiSeq 40.9 / 38.6 / 15.0 (minibwa def / native / shim).
CPU s (end to end): minibwa def mason 70.7, low 46.1, NovaSeq 63.2, HiSeq 123.7; shim 94.1, 41.9, 51.3, 34.5.
Index load is noisy on this VM (minibwa 7–13 s, shim empty run 2–8 s), so differences under ~2 s are not meaningful.
The bench RESULT times exclude FASTQ/SAM I/O and index load, so they are not comparable to these numbers.
