# Walk keeps the best candidate pair (exp/unknown-walkbest)

Problem: ~1 pair in 9 is mapped with `XU:Z:unknown` (n1m 11.8%, h1m 9.1%). Most come from the router giving up
(gate budget, bound 0) and the fallback walk (`Report.fallbackOfK`) reporting the FIRST acceptable pair from at most
`walkK` (3) anchors per strand of each mate's rarest seed.

Change (Proofs/Report.lean, Proofs/Aligner.lean): the walk tries candidates in order and keeps the best-scoring pair
(`bestLazy`), stopping once a pair scores >= `walkStop` (-8). Mate 2's anchors are computed only if needed; a candidate
whose gap-free anchor score is below the best pair so far is skipped. Soundness: `bestLazy_mem` + existing
`walkAt_sound`; `lake build lean-align` green; Spec untouched. Default: `walkK = 3`, `walkStop = -8`.
Mapped counts and mapped-unknown counts are unchanged; XB is not tightened. SAM differs only on baseline-unknown pairs.

## Accuracy (200k sim pairs, pairs at the true position +-20 bp; "unk" = base's mapped-unknown pairs: mason 20256, low 10576)
| variant | mason all / unk | low all / unk |
|---|---|---|
| base | 187909 / 14898 | 193308 / 4854 |
| thr -8, k=3 (default) | 188771 / 15760 | 194273 / 5819 |
| thr -8, k=6 | 188975 / 15933 | 194460 / 5994 |
| thr -8, k=12 | 189106 / 16042 | 194643 / 6157 |
| no stop, k=3 | 188813 / n.m. | 194489 / n.m. |
(n.m. = not measured)
| minibwa c07de5c | 196329 / 17357 | 196486 / 7286 |

## CPU cost (user+sys, median of 3 interleaved runs, 4 threads, 1M pairs; base drifts between batches, compare within a row)
| | base | k=3 | k=6 | k=12 |
|---|---|---|---|---|
| n1m | 75.2 s | +6.8% | +8.1% | +14.8% |
| h1m | 77.7 s | +5.5% | +7.9% | +5.8% (noisy) |
Wall +3% to +7%. No 5M FIFO run (no variant meets the +1% goal).

## Tried, did not help
- Steering (try candidates with a nearby partner-mate anchor first): same candidate set under the early stop, +1/+5 pairs vs k=6, more CPU.
- Lazy mate-2 anchors: no CPU change (k=3: 80.8 vs 80.3 s).
- Pruning candidates by gap-free anchor score vs the best pair: identical results to k=6, no CPU saving (anchors are sorted best-first).
- Threshold sweep -4/-8/-12/none: accuracy within ~100 pairs, time differences below the noise (~1 s).

## To get under +1%
The cost is the partner DP (`nearOf`: seed vote over the window + banded DP) of every extra candidate, run on ~12% of pairs
whose first pair scores below -8. It needs a cheaper PROVED check before the DP that rejects a candidate that cannot beat the
best pair so far (e.g. an upper bound on the partner score from seed votes in the window), or a better first candidate.
Not started. The small extra index (format change) was not tried.
