# FLOOR_COST: where the report-floor work adds CPU (branch `speed/floor-cost`, 2026-11-03)

Measured, not changed: `speed/report-floor-proofs` @ 1266f07 (S-B) against festive-fermi 0e48158. `proof/gaveup`
(S-D) is at 704b7e3, not yet rebased on 1266f07; not measured (its own note reports an OOM on a low-quality real
pair, likely the same blow-up as below).

## 1. Totals (first 2000 pairs)
| | 0e48158 | 1266f07 | ratio |
|---|---|---|---|
| NovaSeq, callgrind Ir (shim, index load included) | 960.6M | **114,499M** | **119×** |
| NovaSeq, native user CPU (mapping; the rest of the run is the index load) | ~0.1 s | 11.2 s | ~100× |
| HiSeq, native user CPU | ~0.2 s | 8.0 s | ~40× |
(native: `Testing/scripts/timed.py`, one run each; the base's ~13 s total CPU is the index load in sys time.)
SAM differs from 0e48158, as expected (the floor changes answers).

## 2. Where it goes (NovaSeq, inclusive Ir)
| item | Ir | share | calls |
|---|---|---|---|
| `Spec.lookAt` (the second look at leftovers) | 113,424M | 99.1% | 85 of 2000 pairs, ~1.33G Ir per pair |
| ├ `LastResort.pairsAt` → `properPairsF` (every proper pair of the mates' hits) | 81,466M | 71.2% | `properPair` + `properPairU` self 55.2G: ~1.4G pair tests, ~16M per pair (~4k × 4k hits) |
| ├ `hitsKPFN` (mate-2 hits near mate-1's) | 23,525M | 20.6% | of which `keepN` (`List.any` over all mate-1 hits per candidate) 20.6G self |
| ├ `hitsKPF` (mate-1 hits within the cap) | 7,935M | 6.9% | banded checks `bTable` / `bRowUp` ~21G across both |
| └ `lookAnswer`, `cutAll`, `finalize` | 0.28G | 0.2% | |
| `reqOf` → `decodeRead` ×2 per pair | 60.0M | (6.2% of the base's whole run) | 3,974 decodes, ~15k Ir each (a `List Char` per mate) |
| `finalize` (report floor) | 2.0M | 0.0% | |
| main path (router, reporter, prep) | ~0.6G | same as base | |

## 3. Why, and cheap fixes
1. **`properPairsF` is quadratic within a chromosome + strand** (`keyA` / `keyB` group only by `2·chr + strand`), so
   repeat-rich leftovers with thousands of hits per mate test every pair. Fix: within a group, sort mate-2 hits by
   start once and take, for each mate-1 hit, only the window `properPairU` allows (`properPairU_near` already gives
   the bounds: `|b.start − a.start| ≤ hi + sl`, same chromosome). `lookAnswer` keeps only `topW dcost0 ps` (its
   theorem uses membership only), so the whole list need not be built: a streaming best-pair over the windows, with
   ties broken by (mate-1 index, mate-2 index) to keep today's `topW` choice, gives the same answer. Expect
   O((n1 + n2) log n2 + pairs in window) instead of n1 · n2.
2. **`keepN` is quadratic too**: each mate-2 candidate scans all mate-1 hits (`ys.any …`). Same fix: mate-1 hits sorted
   by (chr, start) once, binary search for `[D − (hi + sl + nR + gb) − len, D + hi + sl + gb − nR]`.
3. **Too many hits for these reads.** 85 leftovers carry ~4k hits per mate at the cap (`c ≤ 16`: up to 4 mismatches on
   repeats). Even with 1–2, collecting and checking the hits is ~8–24G (`hitsKPF` / `hitsKPFN`'s banded checks).
   Options: a hit-count ceiling that sends the pair to "gave up" (S-D's label) instead of enumerating; or deciding
   "no proper pair ≥ −c" / the best pair from per-chromosome sorted hits without materializing the lists.
4. **`reqOf` decodes both mates for every pair** (60M = +6% of the whole base run on NovaSeq). The default
   `requiredMapBound` only uses the mates' lengths (`capOfLens` of the shorter one), and `(decodeRead R).length =
   R.size`. Fix options: decode only when the second look runs (the floor's `finalize` needs `req` for every pair, so
   that alone does not help); or a length form of the setting (e.g. an `InsertSettings` field `requiredMapBoundLen :
   Nat → Nat → Int` with the spec's bound defined from it), so the shim computes `req` from `R.size` with no decode.
   That is a Spec / settings choice for Rowan.
5. `finalize` itself is cheap (2M).

Priority: 1 and 2 remove ~90% of the extra cost (both are exact rewrites with the existing `properPairU_near`
bounds); 3 caps the worst reads; 4 is the only cost on every pair.
