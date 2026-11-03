# A second index for a finer pigeonhole: measurement and plan (2026-11-03)

Question (Rowan, via the parent session): would a second index of shorter, overlapping or spaced seeds (k = 16-20 grid,
closed syncmers) settle the expensive complete-search pairs cheaply, i.e. prove "no proper pair ≥ requiredMapBound"
with few candidates instead of the second look (`lookAt`)? Budget: < 8 GB total, ~2.5 GB spare.

**Answer: not worth building.** A finer pigeonhole settles 17-20 % of these pairs, about 12 % of their complete-search
time (0.4 s of 3.5 s single-thread CPU per 200k NovaSeq pairs, 0.1 s of 1.1 s HiSeq). Most of the time is in pairs
where even the rarest seeds are repeats, and in pairs that have real near placements. Shorter seeds help neither class,
and an all-genome index of seeds finer than today's 25 does not fit in 2.5 GB.

## What was measured

Pairs: every pair that reaches the complete search (`lookAt`, stage 6) and ends with a bound only. The source is
`pipe_prof` on festive 4dade3b (the code after the cheaper-mate swap), full 200k sets, with a dump line per pair:
name, cap `c`, join cost, `lookAt` µs, and both trimmed mates.
- NovaSeq: 2,627 pairs, `lookAt` 3.51 s (single thread)
- HiSeq: 1,358 pairs, `lookAt` 1.11 s

Exact hg38 occurrence counts of every k-mer of these mates, for k = 16, 18, 20, 25 (canonical, both strands, all of
`genome.fa`, positions kept up to 500 per k-mer): `Testing/scripts/second_index/kcount.c`, one pass over the genome per
k. Between 0.86 and 0.90 million distinct k-mers per k.

Model (`Testing/scripts/second_index/evalq.py`), per pair:
- `e = c / 4` seeds can be spoiled within the cap.
- Seeds are disjoint grid k-mers per mate (`m = n / k`, at offsets `j · (n / m)`, as the 25-mer index).
- Scheme `(k, r)`: the `r` rarest seeds of each mate, `r ≥ e + 1`. A placement within the cap keeps `≥ r − e` of them
  clean on its diagonal (q-gram / pigeonhole), so a candidate is a (strand, diagonal) with `≥ r − e` distinct seeds
  within ±`e`. `r = e + 1` is today's join (`noPairJS`).
- Settled: no mate-1 candidate has a mate-2 candidate on the other strand within the insert window.
- Cost: summed occurrence counts of the looked-up seeds.
- "Too heavy": no `r` avoids a seed with more than 500 occurrences.
- The smallest settling `r` is reported.

The model is approximate (e = c/4 instead of `sbound`, a plain insert window instead of `joinW`/dovetail). Its 25-mer
row is the check: it settles 6-11 % of pairs the real join left open or skipped for budget.

## Results

| k | set | settled | open (candidates exist) | too heavy | `lookAt` time of settled | settled cost (index entries) median / p90 |
|---|---|---|---|---|---|---|
| 25 (today's length) | NovaSeq | 160 (6.1 %) | 2,014 | 453 | 0.24 s of 3.51 | 44 / 440 |
| 25 | HiSeq | 146 (10.8 %) | 1,000 | 212 | 0.06 s of 1.11 | 20 / 334 |
| 20 | NovaSeq | 448 (17.1 %) | 1,742 | 437 | 0.39 s | 29 / 476 |
| 20 | HiSeq | 224 (16.5 %) | 960 | 174 | 0.11 s | 31 / 427 |
| 18 | NovaSeq | 510 (19.4 %) | 1,705 | 412 | 0.42 s | 31 / 528 |
| 18 | HiSeq | 235 (17.3 %) | 933 | 190 | 0.10 s | 44 / 406 |
| 16 | NovaSeq | 530 (20.2 %) | 1,663 | 434 | 0.41 s | 125 / 723 |
| 16 | HiSeq | 261 (19.2 %) | 904 | 193 | 0.10 s | 141 / 806 |

Where the `lookAt` time sits (k = 18; the 25-mer split in parentheses):

| set | too heavy | open | settled |
|---|---|---|---|
| NovaSeq | 412 pairs, 2.06 s (453, 2.67 s) | 1,705 pairs, 1.02 s (2,014, 0.59 s) | 510 pairs, 0.42 s (160, 0.24 s) |
| HiSeq | 190 pairs, 0.58 s (212, 0.76 s) | 933 pairs, 0.43 s (1,000, 0.30 s) | 235 pairs, 0.10 s (146, 0.06 s) |

Open pairs have a median of 10 candidate diagonals (p90 166-344): real places where most seeds match. The full
alignment there scores below `requiredMapBound`, so a seed filter cannot reject them; only alignment can.

Reading:
1. **Too heavy** (16 % of the pairs, 59-76 % of the time): seeds with hundreds to thousands of places among the rarest
   `e + 1`. Typical cases: one Alu/L1-like seed on a short mate (`e = 1`, two seeds), or repeats covering a whole mate
   while staying under the repeat rule (K = 2, N = 200). A shorter seed inside the same repeat is just as repetitive.
   What helps here is the repeat rule itself (K = 1 or the ManyPlaces rule), not a finer index. Same-box numbers from
   the gaveup2 runs: K = 1 at N = 200 was 29 % (NovaSeq) and 17 % (HiSeq) faster end to end than K = 2.
2. **Open** (64-69 % of pairs, 26-39 % of the time): real candidates, about 10 per pair. The lever is verifying them
   cheaply (the banded checks in `hitsKPF`/`fineE`, S-F's area), not finding fewer.
3. **Settled by a finer pigeonhole**: 0.4 s / 0.1 s single-thread CPU per 200k. That is about 0.1 s / 0.03 s wall at
   4 threads, ~1-2 % of today's 6.6 s / 6.8 s headline.

## Memory

- A full grid index of k = 16-20 at every genome position: 3.1e9 entries × 4-5 B = **12-15 GB**. Out of budget.
- Sampled to fit 2.5 GB (≤ 0.5e9 entries, density ≤ 0.16): minimizers or closed syncmers need a window of about
  `w ≈ 2 / 0.16 − 1 ≈ 11` k-mers. The pigeonhole then works on windows of `L = k + w − 1 ≈ 28` letters (k = 18), or
  `L = 2k − s − 1` for closed syncmers at the same density. That is **coarser than today's 25-letter seeds**: within the
  budget, a second all-genome index cannot give a finer pigeonhole.
- Only a restricted index fits: finer seeds at repeat positions only (~0.5e9 positions, 2-2.6 GB, `INDEX_TRICKS.md` 3b).
  It targets exactly the "too heavy" pairs, where (point 1) finer seeds stay heavy.

## Proof plan (if it were built anyway)

1. `MzIndex.q` is a global constant (`def q : Nat := 25`, `Aligner/index/minimizer/MzIndex.lean`), and `/ 25` appears
   in 24 files (seed grids, `fastT`, `sbound`-based counts, `noPairJS`/`anchSel`, `rareSel`, `GaveUp`). Step 1: make `q`
   an index field (or a parameter of `MzIdx`, checked like `k`, `w`). The lookup theorem `lookupSeed_mem` and
   `check2P`/`check3P` are already parametric in `k`, `w`, the bucket bits and the slot width; they need `q` threaded
   through. This is mechanical, but it touches the router's proofs wherever `25` is a literal.
2. A second `MzIdx` (`q'`, `k'`) in `LoadedIndex`, checked at build time by the same `indexOk`.
3. The pigeonhole for `q'`-seeds: `exists_clean_seed_amongE` is stated for disjoint seeds of the index's length, so
   it carries over once `q` is a parameter. The q-gram form ("`≥ r − e` of `r` seeds agree on a diagonal within ±e") is
   new: a counting lemma over disjoint seeds plus the diagonal-shift bound for indels (`gapBound`).
4. A `noPairJS'` / `tierNo'` stage on the second index, giving the same `TierOut` (T3, `pf = some c`), so the router
   and the reporter need no change (as with the 25-mer join, `tierNo_ok`).

Estimate: steps 1-2 are the bulk (several hundred lines of edits across the router's proofs), steps 3-4 are moderate.
For ~1-2 % of the headline, this is not the next thing to do.

## Recommendation

- Do not build a second index for a finer pigeonhole.
- For the "too heavy" class (most of the remaining complete-search time): settle the repeat rule (K = 1, or the
  ManyPlaces rule at `gaveUpPlaces`). This is a Spec choice for Rowan, measured same-box in the gaveup2 runs.
- For the "open" class: cheaper verification of the ~10 candidates per pair (S-F's `fineE` / banded-check work), and a
  cap on per-pair candidates before the complete search.

Scripts: `Testing/scripts/second_index/kcount.c` (`gcc -O2`; `kcount K KMERS GENOME CAP OUT`),
`Testing/scripts/second_index/evalq.py` (reads the `BOUND` dump lines and the `kcount` outputs). The dump lines come
from a local `pipe_prof` edit that prints, per bound-only stage-6 pair: name, `c`, join cost, `lookAt` µs, and both
mates. That edit is not committed; it is three lines after the `closed {k}` count.
