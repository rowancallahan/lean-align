# lookat-fast: the leftover path at 453394f (branch `speed/lookat-fast`, 2026-11-03)

Base 453394f (gaveUp merged). Ir = callgrind of the shim on the first 2000 pairs (index load included). Checks:
SAM byte-identical to 453394f on the 2000-pair subsets and on the four full 200k sets; `CI_check.sh` passes; no
Spec/, Main.lean or Shim edits; no sorry / native_decide / implemented_by / extern / unsafe / partial. Every change
is a `@[csimp]` rewrite with an equality proof. No definition used in a statement changed, so `alignPairs_correct`
(under `SettingsOk`) and `repeatMate_sound` are untouched.

## 1. Profile at 453394f
NovaSeq 2122.4M, HiSeq (hg002 2×250) 1905.8M. NovaSeq: `afterLeftover` 1047.6M, of which `repeatMate` 730.9M
(141 calls; 428M index lookups, 259M chromosome checks of every place) and `lookAt` 316.5M (42 calls: hit search
234M, CIGARs of the winner by `bandDoublingAlign` 78M). `decodeRead` (for `reqOf`, every pair) 60.4M.

## 2. Changes
| commit | change | NovaSeq | HiSeq |
|---|---|---|---|
| 453394f | base | 2122.4M | 1905.8M |
| 04040b0 | `repeatMate`: each seed's lookup stops after `gaveUpRepeats` places (`lookupPWk`, already in MzWord). Fewer than 500 returned = the whole result (`lookupPWk_small`, new), so the count is below 500; otherwise 500 counted among the first 500 decides `true` (prefix sublist, `lookupPWk_extract`); else the full count. `seedRepF_eq`, `repeatMate_eqF` | 1468.1M (−30.8%) | 1730.1M (−9.2%) |
| 2f66200 | `decodeRead` as one `Array.foldr` (no `List UInt8`): `decodeRead_eqF` | 1440.7M | 1689.0M |
| 4b9e79b | `bandedRun` (the CIGAR of the second look's winner): rows built without their dead prefix (cells with `lo > 0`, all `bCellNone`; 130k of 139k cells on NovaSeq). `bRowUp_dead`, `bTableK_eq`, `bandedRun_eqK` | 1402.8M | 1659.0M |
| 792dc25 | `bMkMain`'s three-way `Option.merge maxOn` compares scores first, conses only the winner (`pick3_eq`, `bMkMain_eqF`); same left-leaning ties | 1382.4M | 1647.2M |
| c633294 | `hitsKPFN` (mate 2 of the second look): a chromosome without a mate-1 hit is skipped, since `keepN` rejects every diagonal there (`keepN_gate`, `hitsSKNG_eq`, `hitsKPFN_eqG`) | 1327.6M | 1612.5M |
Total NovaSeq **−37.4%** (2122.4M → 1327.6M), HiSeq **−15.4%** (1905.8M → 1612.5M).

## 3. The parent's items
- (4) req from byte sizes: not possible as an exact rewrite without a Spec/Main change. `requiredMapBound` is a
  closure field of `InsertSettings`, so compiled code cannot tell it is the default formula. Done instead: the
  general `decodeRead` csimp (−27M NovaSeq, −41M HiSeq). A size-only `reqOf` would also need
  `requiredMapBound` to be a function of the lengths in Spec, or a flag in the settings.
- (1) `properPairsF` windowed: 10.0M (0.75%) on NovaSeq after the above. Not done. The hits of one group are not
  sorted by start (start = `dst D sh` over diagonals × shapes), so a window needs a stable sort plus a proof
  that the order is restored. Worst case: gaveUp now removes mates with a seed of ≥ 500 placed copies before
  `lookAt`.
- (2) `keepN` binary search: no longer in the profile. After c633294 it runs only on chromosomes where mate 1 has a
  hit.

## 4. Left
- `pairsAt`'s mate-1 search `hitsKPF` (~127M NovaSeq): the per-diagonal kernels (`fineE`, `kerHKG`: 73M) are the
  real work. Per-chromosome overhead: `slicesAt` binary searches 25M and `diagsM` on empty slices ~19M. A
  hit-chromosome set from the seed arrays would skip both, but it needs `lbA` facts.
- `repeatMate` 76M: the index lookups themselves (`lookupPWk`, ~100k Ir per seed, bucket scans).
- `deadK` recomputes `ys.length` per row (3.6M).

## 5. Native CPU (200k pairs, taskset 4 cores, same idle box)
TIMING
