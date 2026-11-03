# small-costs: the new per-pair costs since 0e48158 (branch `speed/small-costs`, off festive-fermi 3d63f4b)

Ir = callgrind of the shim on the first 2000 pairs. SAM byte-identical to 3d63f4b on the four full 200k sets and
both 2k subsets; `CI_check.sh` passes; exact `@[csimp]` rewrites only.

| commit | change | NovaSeq | HiSeq |
|---|---|---|---|
| 3d63f4b | base | 1603.0M | 1598.8M |
| reqOf_eqF | `reqOf` from the mates' byte sizes. Rowan's `requiredMapBound` is a top-level function of the lengths, and `decodeRead_length` gives the length. `reqOf` is evaluated in several places per pair, so this saves more than one `decodeRead`. | 1527.3M (−4.7%) | 1481.7M (−7.3%) |
| fallbackOfK_eqL | the walk computes the partner search (`nearOf`) only when the walked mate has a report (`pairOf` needs both) | 1527.3M | 1478.9M |
Total NovaSeq −4.7%, HiSeq −7.5%. 0e48158: 960.6M / 1309.4M.
Native user CPU, 200k, one run each: NovaSeq 27.2 → 27.1 s, HiSeq 29.2 → 26.6 s, mason 30.3 → 27.1 s (±5% noise).

## Not changed
- Report re-check (+64M on NovaSeq vs 0e48158): the walk's `keep` filter (`junkScore`) makes `fallbackOfK`
  try more anchors than 0e48158's first-proper-pair walk (342 vs ~295 `tryAt` calls). Each try's partner
  search `nearOf` → `TierHeur.nearY` runs `bandDPg` with limit 1e6: 107M over 222 calls, ~480k Ir each.
  Passing the walk's floor as the DP limit would cut it. That is exact only with a proof that `bandDPg` under a
  limit returns the same best when the best is within it, and that a partner beyond the floor makes the pair
  fail `keep`. It is not a csimp-only change.
- Join stage (62M): `joinAt` → `tierNo` (56 calls, ~1M Ir each) is real seed-join work within its budget.
