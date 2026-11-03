# repeat-check: the repeat witness at N = 200, K = 2 (branch `speed/repeat-check`, off festive-fermi 39ae4e8)

Ir = callgrind of the shim on the first 2000 pairs. SAM byte-identical to 39ae4e8 on the four full 200k sets and
both 2k subsets; `CI_check.sh` passes; exact `@[csimp]` rewrites.

| commit | change | NovaSeq | HiSeq | NovaSeq repeat check |
|---|---|---|---|---|
| 39ae4e8 | base | 1524.0M | 1476.9M | 46.7M (79 lookups) |
| cherry-pick of f1ee9cf | a seed whose bucket has < 200 slots is "no" without a scan (`scanAW_size`, `lookupPW_size`: at most one place per slot) | 1524.4M | 1476.8M | — |
| next commit | a mate with fewer than K = 2 buckets of ≥ 200 slots is "no" with no lookup at all (`bigB`, `bigB_of`; `repeatMate_eqF` via `countP_mono_left`) | 1504.5M (−1.3%) | 1469.9M (−0.5%) | 26.9M (55 lookups) |
The per-seed bound alone gives nothing: `countGE` already stops at 2 repeat seeds, and the cost was in
lookups of mates with one big bucket. Native user CPU, 200k, one run each, within noise (±5%): NovaSeq 26.4 →
25.1 s, HiSeq 26.1 → 27.7 s.

What is left (NovaSeq 2k): 55 lookups of buckets with ≥ 200 slots, ~340k Ir each. 46 of them reach 200
genome-checked places (true), so they are needed: the proof counts 200 checked places. Plus the in-chromosome
count of those 200 places, 5.5M (~600 Ir per place, a binary search over the chromosome starts). Going further
exactly needs a stored per-key count (S-G's table) or a faster chromosome test (e.g. the places are increasing,
so one walk over `offs` instead of 200 searches; needs the lookup's sortedness carried into `GaveUp`).

## For S-D (the walk's DP limit; from speed/small-costs)
On 3d63f4b NovaSeq 2k:
- `fallbackOfK` makes 342 `tryAt` calls, against ~295 at 0e48158, because `keep` rejects pairs under `junkScore`.
- Each call's `nearOf` → `TierHeur.nearY X pgs ws we 8 1000000 1000000 12 sv true false` runs `bandDPg` with
  limit 1e6: 107M over 222 calls, ~480k Ir each.
- A partner with penalty above `−junkScore` minus the walked mate's penalty makes the pair fail `keep`, so passing
  that as the DP limit is safe if `bandDPg` under a limit returns the same best whenever the best is within it.
  That is the proof needed (`bandcells_ab` checks only the `bandCellsJ` switch today).
