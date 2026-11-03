# festive e187d30 vs baseline 0e48158: inclusive Ir growth (2k subsets, no shim patch on either)

Totals: NovaSeq 960.6M → 1476.4M (+515.8M); HiSeq 1309.4M → 1479.3M (+169.9M). Listed: functions whose
inclusive Ir grew by more than 5M, without thread wrappers, and without recursive `'2` entries whose inclusive
Ir double-counts (`bTableK'2`, `dedupAdj'2`, `mergeRuns'2`).

| function (inclusive) | NovaSeq Δ | HiSeq Δ | what it is | cheapest exact lever | owner |
|---|---|---|---|---|---|
| `afterRouter` (stages 3–6) | +476.1M | +110.5M | join + short look + gave-up + second look | below | — |
| `lookAt` → `pairsAt` → `hitsKPF` / `hitsKPFNG` | +387.1M (hits 304 + 64) | +73.0M | second look on non-repeat leftovers: candidate diagonals, filter, kernels | second index / fewer candidates | S-D |
| `fallbackOfK` → `walkAt` → `nearAt` | +134.6M | +89.9M | the walk past junk pairs; the partner band DP has limit 1e6 | DP limit at the floor, plus a `bandDPg`-under-limit proof | S-D |
| `joinAt` → `tierNo` → `noPairJS` | +61.8M | +20.5M | rarest-seed anchor join: lookups 32.5M, `List.merge` 13.1M, `toList` / map 4.4M | (a) reuse its lookups in the second look: the same `LookG.look` calls on the same `rareSel` seeds, up to 33.4M NovaSeq; (b) array merge, up to ~10M | (a) touches lookAt's inputs; (b) free |
| `scanAWF` / `scanAWK3` / `mzLookSP` | +81.9M / +63.6M | +24.3M | bucket scans of the lookups above (join 32.5M, second look 33.4M, repeat check 25.3M) | counted in the rows above | — |
| `repeatMateF` (gaveUp) | ~+27M | ~+10M | witness lookups (55 per 2k on NovaSeq) | per-key count table | S-G |
| `parseRecord`, `readFastqRecord`, `mateName`, `String.splitOn` | +60.1M + (Nova) | +87.2M, +53.5M, +24.5M, +23.1M | festive's frozen FASTQ shim: per-byte validation (`allBytesGo` 29M), quality as `String` (UTF-8 validate / strlen), `mateName` via `splitOn` | `Testing/notes/shim_speed.patch` (byte quality, `findNewline` on `USize`), plus `mateName` without `splitOn` | Rowan (frozen) |

## Recommendation for the next exact lever (not S-D's)
1. Join → second-look lookup reuse (up to 33M NovaSeq). `noPairJS`'s `anchSel` and `hitsSK`'s `lk` call
   `LookG.look ix G R (j·Ls) (R.size − j·Ls) (prep (seedHashAt R (j·Ls)))` for the same rarest seeds. The rare
   selection is `rareSel` (qsort by size) in the join and `ordG … take (sbound c + 1)` in the second look, so
   first check that the two pick the same seeds. Passing the arrays is pure common-subexpression sharing, with no
   new mathematics, but it threads through `afterRouter` → `lookAt` → `pairsAt` → `hitsKPF` / `hitsKPFN`. That
   sits next to S-D's lookAt work, so coordinate first.
2. `noPairJS` anchors as sorted arrays instead of `List.merge` (≤ 10M).
3. The FASTQ items are the largest non-S-D growth on HiSeq (~190M) but are frozen: Rowan's call.

## Result: join → second-look lookup reuse (measured on festive 2149f19, not kept)
Built exactly and proved: `afterRouter_eqF` used four lazy `Thunk`s of the join's rare-seed lookups, one per
mate and strand, and a per-seed cache in cached copies of `hitsSK` / `hitsSKNG` / `hitsKPF` / `hitsKPFN` /
`pairsAt` / `lookAt` (`CacheOk`, `cacheOf_ok`, `noPairJSC_eq`, `joinAtC_eq`, `lookAtC_eq`). SAM was identical,
but NovaSeq went 1476.7M → 1478.5M and HiSeq 1479.4M → 1479.8M. Lookups only dropped 65.9M → 64.0M:
- a failed join usually stops after its first strand pair (`f1`, `r2` near), so the second look still needs the
  other two strands;
- pairs whose join is skipped on budget share nothing;
- the second look's `ordG` choice and the join's `rareSel` choice break bucket-size ties differently.
The thunk and cache overhead outweighs the ~2M left, so the code was dropped.

`noPairJS` anchors as arrays: the merged list must stay identical for `nearAnyF`. Proving that an array k-way
merge equals the iterated `List.merge` needs the packed lookups' sortedness carried to `anchSel`. At most
~10M (`List.merge` 13.1M on NovaSeq); not done.
