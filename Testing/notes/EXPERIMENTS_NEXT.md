# Next experiments (Rowan, 2026-11): deeper error caps, faster index lookup, dedup

All measured as a direct A/B on one box with the release (`speed/n29-base` tree vs the change): same hg38 index
and reads, interleaved runs (median of 3), plus callgrind Ir per pair on the same subsets; SAM must stay
byte-identical unless the change is meant to add mapped pairs (then count gains at truth on the sims).

## 1. Faster index lookup (idea from archive/arrays)
- **Then:** seed mapper over `Array Char` chromosomes with a hashed index (UInt64 polynomial hash of each word). Key
  argument: hash collisions only add candidates, so the proof needs just `LookupComplete` — every true occurrence is
  reported; extras are filtered later.
- **Now:** `mzLookSP` → `scanAWK` (Aligner/index/minimizer/MzWord.lean) scans every slot of the bucket `[lo, hi)`
  and compares `slot &&& kb` with the key. hg38 buckets are large and mix keys, so this is **12% of hg38 time** and
  grows with genome size (chr21: small).
- **Experiments:** (a) sort each bucket's slots by key at build time and binary-search the key's run (proof:
  the run is exactly the slots with that key — same results as the scan, so `scanAWK` equality, or completeness);
  (b) more bucket bits (smaller buckets) — index format change, the index check (`check3P`) covers it; (c) a
  per-key offset table. The index checker must cover any new layout; the lookup only needs completeness.

## 2. Dedup before the expensive work (idea from archive/dedup-parallel)
- **Then:** `mapWithDedup` dropped candidate windows that don't fit their chromosome (by length) and removed repeated
  windows with a HashSet before scoring (`mapWithDedup_eq_mapWith`); identical output, fewer kernel calls.
- **Now:** `diags` (Aligner/mapper/FastGenAlgo.lean) already dedups diagonals, but by flattening to a List,
  `List.mergeSort` and `dedupAdj` — the **5–6% `List.mergeSort` hotspot on hg38**. `ParGroup.distinct`/`dedupMap`
  exist (HashSet dedup, map each distinct item once) but are not on the alignPairs path.
- **Experiments:** (a) replace diags' list sort with an Array sort or HashSet distinct (@[csimp], same list up to
  order where order matters — check `diags` users); (b) dedup identical read pairs within a chunk (PCR/optical
  duplicates) with `dedupMap` inside alignPairs (`alignPairs_eq_map` still holds since each pair's result is the same
  function of the pair); (c) drop candidates outside the chromosome before kernels.

## 3. Deeper error caps (idea from archive/bounds + bounds-v2)
- **Then:** sharp bounds: charge each mismatch, each gapX run and each gapY column once;
  e = max((−T)/min(−mismatch, −(gapOpen+gapExtend)), (−T+gapOpen)/min(−mismatch, −gapExtend)) spoiled seeds →
  e+1 seeds guarantee a clean one; total gap columns ≤ d = (−T+gapOpen)/−gapExtend, ≤ d2 = (−T+2·gapOpen)/−gapExtend
  when both kinds occur; start/end shifts |s|+|t| ≤ d (same sign unless ≤ d2) → 19 windows per seed hit instead
  of 169. Proved in SeedMapper2 / MapperWalk2 (`exists_clean_seed2`), on main.
- **Now:** disjoint 25-letter seeds, m = ⌊n/25⌋ (6 at 150 bp), caps −12 (<150 bp) / −16 (≥150). chr21 mason sims:
  ~5% of pairs have 5–7 spread mismatches (just over the cap) and go unmapped.
- **Experiments:** (a) with the bound formula, compute which seed length / count reaches 5–7 errors at 150 bp
  (e.g. 15–16-letter seeds → 9–10 seeds); (b) spaced seeds (patterns that skip positions) survive spread mismatches
  at the same length; (c) iterative deepening: run the current cap first, only failing pairs at the deeper cap.
  Measure pairs gained at truth and the cost (more hits per shorter seed, mostly in repeats). Needs a proved index
  for the new seed shape (or a second index), and the bound proof for the new cap.

## Also queued (from PAUSE_2026-10-30.md)
Multithreading overhead (~40% extra CPU with 4 tasks in one process), danger regions and WFA on full hg38, the
heuristic's best settings for M2, glibc allocations and the bignum on the hg38 path.
