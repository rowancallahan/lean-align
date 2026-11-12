# Repeat hint from seed bucket sizes, measured on hg38 (`speed/n31-repeat-hint`)

Idea (Rowan): if a pair's seeds are all high-count, call it a repeat, take one candidate pair, report uniqueness unknown and
skip the tie search. Measurement only: nothing in the router changed; the setting was **not implemented** (no threshold looks good).

Setup: bench index of hg38 (`bench-release`), bench RTX, `WG_XH=0`, 4 cores (`taskset -c 0-3`), 200k pairs per set.
`WG_SEEDCNT=1` (new, default off) dumps per pair, per mate and strand, the min and median `LookG.size` (bucket entries) over
the mate's seeds. Bucket sizes include other keys that share the bucket (≈10 entries even for a unique read), so the
numbers below are the bucket-size proxy, not exact occurrence counts. Mate statistic = better of the two strands; a pair is
flagged when both mates pass. "Tie" = RT reason tie. Analysis: `Testing/benches/repeat_hint.py DIR set`.

## 1–2. Ties caught, precision, wrongly flagged (N = threshold)
`min` = rarest seed's bucket ≥ N (all seeds high); `med` = median seed's bucket ≥ N. Ties: mason 9,240, low 9,802, novaseq 11,929, hg002 9,597.

| stat N | mason catch / prec / unique T1 flagged | low | novaseq | hg002 |
|---|---|---|---|---|
| min 50 | 1.6% / 90.6% / 13 | 7.1% / 91.3% / 56 | 14.5% / 84.8% / 128 | 10.9% / 81.5% / 93 |
| min 200 | 0.8% / 98.6% / 0 | 4.3% / 97.9% / 4 | 8.8% / 91.4% / 21 | 6.4% / 89.7% / 13 |
| min 1000 | 0.2% / 93.3% / 0 | 1.1% / 100% / 0 | 1.8% / 87.8% / 0 | 1.1% / 92.4% / 1 |
| med 50 | 42.2% / 33.3% / 7,019 | 43.9% / 36.7% / 7,174 | 43.7% / 36.1% / 6,922 | 41.6% / 27.9% / 6,936 |
| med 200 | 35.1% / 46.9% / 3,249 | 38.6% / 49.6% / 3,654 | 37.5% / 46.2% / 3,737 | 36.3% / 37.0% / 3,768 |
| med 1000 | 22.2% / 58.3% / 1,258 | 26.6% / 58.8% / 1,704 | 23.1% / 52.4% / 1,779 | 20.1% / 40.1% / 1,935 |

(more thresholds, 20…1000, in the script output.)

## 3. CPU of flagged pairs = the most any early answer could save (bench CPU s, median of 3, no index load, no I/O)
| set | all pairs | min ≥ 50 | min ≥ 200 | med ≥ 200 |
|---|---|---|---|---|
| mason | 45.0 | 0.12 (159 pairs) | 0.05 (73) | 13.4 (6,922) |
| low | 18.5 | 0.32 (763) | 0.18 (434) | 5.9 (7,621) |
| novaseq_200k | 22.2 | 1.10 (2,037) | 0.58 (1,152) | 9.1 (9,666) |
| hg002_200k | 21.1 | 0.77 (1,289) | 0.40 (686) | 8.2 (9,431) |

## 4. Placement quality (first candidate not at truth)
Not measured: the dump has no candidate enumeration for tie pairs (`gmX` exists only for T1gm). Bound: every flagged tie
has ≥ 2 equally good candidates, at most one of which is the simulated locus, so a single pick is at truth for at most 1 of k
of them (≤ 50% for k = 2, the common case). Flagged non-tie pairs (the unique T1 column above) have one candidate and keep their placement.

## Result
- The precise flag (min) saves ≤ 0.3–5% of bench CPU (novaseq min ≥ 50: 1.1 of 22.2 s) and catches ≤ 15% of ties; the broad flag
  (median ≥ 200) catches 35–38% of ties but flags 3.2–3.8k unique T1 pairs per 200k (precision 37–50%).
- The median ≥ 200 group is where O3's `gateBudget` early stop already saves CPU (mason −30% at gate 15000), so the hint is not needed there.
- Ties with two copies have ordinary-looking bucket counts; a useful flag needs exact per-key occurrence counts (index change), not bucket sizes.
- Recommendation: do not implement.
