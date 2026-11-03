# new-filter: a cheaper exact piece scan for the second look (branch `speed/new-filter`, off festive 6f9e0ca)

Ir = callgrind of the shim on the first 2000 pairs (`Testing/repro/ir.sh`), whole run, no shim patch.
SAM byte-identical to 6f9e0ca on both 2k subsets and both full 200k sets (NovaSeq, HiSeq).
`FUZZ=1 Testing/scripts/CI_check.sh` passes. Both changes are exact `@[csimp]` rewrites; no Spec / Alignment /
Mapping / Shim file is touched.

| | NovaSeq 2k | HiSeq 2k | NovaSeq filter functions |
|---|---|---|---|
| 6f9e0ca | 1476.5M | 1479.4M | `lanesAnyW` 83.3M, `fineEV` 26.4M, `suppA` filter 12.1M |
| + `fineE_eqC` (rolling scan) | 1435.0M (−2.8%) | 1470.3M (−0.6%) | `lanesAnyR` 49.4M, `fineEU` 16.0M |
| + `suppA_eqC` (countP) | 1426.0M (−3.4%) | 1470.4M (−0.6%) | `suppA` count 5.8M |

## Why not a different filter algorithm
In the second look (`lim ≤ 16`: `r = 10`, `sb = 4`) a false diagonal is rejected after `sb + 1 = 5` failed pieces,
i.e. two read words × (2r + 1) shifts ≈ 44 lane steps of 4 pieces each. Every alternative needs as much work:
- an 8-mer set of the read probed per window position: ≈ 8(sb + 1) + 2r = 52 positions, and the exact answer
  still needs each piece's own band (a 64k table per read is also cache-hostile);
- one piece replicated over 4 shifts per word: 8 steps per piece, 40 for 5 pieces;
- a counting q-gram lemma over all overlapping 8-mers: more work per diagonal, not less.
A stronger (sound) filter would not pay either: of ~280 filter-passing `lim = 16` diagonals on NovaSeq 2k only
~40 yield no hit, so it could remove at most ~15% of the kernel calls after the filter. The lever is the cost per
lane step (~44 Ir) and the word loop's `Nat` bookkeeping (~280 Ir per call).

## What changed (Aligner/mapper/FastGenWordFilt.lean, FastGenAlgo.lean)
- `lanesAnyR`: the 32 window fields are kept in one register `a`; each step shifts in one field from a pending
  word `b` (refilled every 32 steps from `GW.getU`), instead of `comb` with variable shifts and a word-index check.
- `zt`: the four 16-bit lanes of `wj ^^^ a` are tested for zero with one add,
  `~~~(((x &&& 0x7FFF…) + 0x7FFF…) ||| x) &&& 0x8000…`, instead of `fold`, the field mask and `laneZ`
  (the mask is not needed: lanes `< m` lie inside the read, and the rest are cleared by `full`).
- `fineEU`: the word loop on `USize` (`j`, `k`, `acc`, `m`, `need`), `fullLU` / `lcU` on machine words.
- `suppAC`: `List.countP` instead of `(filter …).length`.
- Removed: `fineEV` / `fineEV_eq` (replaced by `fineEU`). `lanesAny*` stay for the slow path `fineES`.

## Proofs
- `zt_bit`: bit `16i + 15` of `zt x` ↔ the 16 bits of lane `i` are clear (`lane_key`: the add is carry-free
  across lanes, by `Nat.add_div` and the lane's `/ 2^16i % 2^16`); `zt_lane`: ↔ the 8 fields agree.
- `roll_eq` + `RInv` / `rinv_step`: the rolling window equals `gAtW gs (T + 1)` after a step (by `dig`).
- `lanesAnyR_bit`: the scan's flag `i` ↔ some offset `< k` has lane `i` clear (as `lanesAny_bit`).
- `wordR_bit` + the existing `wordF_bit` + `lane_equiv` (`laneZ_bit`, `mdig0`) → `lc_word`: the same piece
  count per word; `fineEU_eq`: `fineEU … = fineE …` under the bounds that `fineEC` checks (else `fineES`).
- `fineE_eqC : @fineE = @fineEC` and `suppA_eqC : @suppA = @suppAC` are `@[csimp]`; standard axioms only.

## Not done
- A fused two-word scan (8 lanes per step, `lanesAny2`): prototype (unproved) a further −5M on NovaSeq (−0.35%).
- (Corrected below.) The second look's shape loop after the filter is 49M, not ~128M: most `ker16KWG` / `kerGKG`
  Ir comes from the router and mate stages that share the specialisation name.

## speed/next (off festive 6707632): the second look's per-diagonal setup
Stage profile (NovaSeq 2k, inclusive, total 1426.0M): `alignOneP` 969M: `afterRouter` 432M (`lookAt` 343M on 33 pairs,
`hitsCKT` 207M), router `tierPairBP` 254M (`routeGS` 219M), `answerOfPairP` 174M (`fallbackOfK` 135M); FASTQ
`readChunk` 266M and SAM `samLines` 152M are the shim (`shim_speed.patch`).
In `hitsCKT` (33.5k diagonals): the support `suppA` (countP + one binary search per seed) 33M, `pkU` / `usIn` /
`gapBound` per diagonal ~8M; the second look's shape loop is 49M in all (19.6k word kernels, ~2.1k Ir each), so a
banded pass per diagonal (~11 DP passes for 43 shapes) would not be cheaper.
- `hitsCKT`: supports of all diagonals by one sweep (`suppCntC`, already proved), `pkU` once, `kfiltVF` per diagonal;
  `hitsCK_eqT` re-proved (`zipIdx_flatMap`, `suppCntC_get`, `kfiltVF_supp`).
- `sweepA_eqF`: `sweepA = sweepAF` (`advF` without fuel, `Array.set` instead of `modify` with a closure).
- NovaSeq 2k 1426.0M → 1403.2M (−1.6%); HiSeq 1470.4M → 1463.6M (−0.5%). SAM identical (2k and full 200k, both sets).
- Tried and dropped: the same sweep in `hitsCKNT` (+2.1M: `sel` rejects most diagonals, so precomputing all supports
  costs more); `sweepAF` on `UInt64` (−1.5M only; the sweep is bounded by the anchors it walks); the byte slow path
  `fineOk` (19M, 289 diagonals of ~4 reads whose window touches a non-ACGT block) is data-specific.

## speed/answer (off festive 050ef82, new-format index): the walk
answerOfPairP 174.0M (NovaSeq 2k, 1240.2M total) = fallbackOfK 134.6M (290 pairs) + foundOfK 36.5M. fallbackOfK: walk
steps 113.6M → nearAt 107.4M (385) → nearY 89.8M: bandDPg 51.7M (173 DPs, ~300k Ir each, ~115 Ir per band cell),
voteD 20.1M (117 votes over the ~1000-letter pair window), winLgU 11.6M (~25 Ir per letter), seedVote 6.9M;
anchorsOf 12.0M; prepMate redone inside fallbackOfK ~8M. The floor as the DP limit (SMALL_COSTS) is already in.
- `fallbackOfKP`: the walk takes the router's mate preparations (`s1`, `s2`) instead of recomputing them;
  `fallbackOfKP_eq` (`prepMz_eq`) keeps `answerOfPairP_eq`. NovaSeq 1240.2M → 1231.5M (−0.7%), HiSeq 1433.3M →
  1425.1M (−0.6%). SAM identical (2k and full 200k, both sets); FUZZ=1 CI passes.
- Tried and dropped: `bandCellsJ` carrying the previous row's `H` in a register (+3.6M: the 13-argument cell loop
  gets slower). A real speed-up of the band DP needs a different kernel layout (machine-word arrays), not a
  source-level tweak.

## speed/banddp (off festive 9b81fb5): the band DP's traceback
`bandDPg` (NovaSeq 2k, 74.6M incl.): cells `bandCellsG` 53.0M over 218 DPs (~95 Ir per cell), traceback `while` loop
7.7M + `runsOf` 4.6M over 115 tracebacks (~390 Ir per step: the `while` in `Id.run` re-allocates its mutable state
each iteration), array frees 4.5M.
- `tbRun`: the traceback as a tail-recursive loop that builds the runs while prepending (same runs as `runsOf`).
  **Heuristic code, not proved**: the old loop is a `while` (`Loop.forIn`, opaque), so old = new cannot be stated as a
  theorem. `bandDPg` has no value theorem (only `bandDPg_jump`, about the cells, unaffected) and its result is
  re-checked downstream (`checkMove`, `mateOf`), so soundness does not depend on it; SAM identity is by test.
- vs festive 9b81fb5: NovaSeq 1217.4M → 1210.9M (−0.5%), HiSeq 1425.9M → 1411.6M (−1.0%). SAM identical on both 2k
  subsets and both full 200k sets; FUZZ=1 CI passes (456 theorems).
- Tried and dropped: the cells on 4-byte little-endian `ByteArray` storage (one bounds check per value, `set!` per byte):
  `bandCellsB` 69.8M vs `bandCellsJ` 55.2M on HiSeq 2k, i.e. 1.26x SLOWER, before counting the fill. `Array UInt32`
  holds tagged scalars on 64-bit (no heap boxes), so its per-access cost is a bounds check and a shift; a byte-wise
  cell costs four loads/stores plus shifts. Earlier: carrying the previous row's `H` in a register was +3.6M.

## speed/svany (off festive 3dde0e4): the unlooked-seed scan (HiSeq)
`unlookV` → `svAny` (the 25-letter seeds not looked up, tried at the 2r+1 shifts of a diagonal; ~5 per 2x250 read) was
50M on HiSeq 2k, 96% of it from the router's `stageKSPN` filter.
- `svAnyR` (0f62e7e): `svAny` on the rolling window of `lanesAnyR`; `svAnyR_eq` (`roll_eq`, `RInv`, `rinv_step`, moved
  above it; `rinv_start`). `svAnyU` removed.
- `unlookW` + `svsOf` (a0d83a6): the seeds' (start, word) pairs computed once per `stageKSPN` call instead of per
  diagonal (`unlookW_eq`); `gAtW_eqF`: `gAtW` on `USize` offsets / `GW.getU` everywhere (`gAtWU_eq`).
- 2k Ir vs festive 3dde0e4: NovaSeq 1165.0M → 1158.8M (−0.5%); HiSeq 1410.6M → 1387.5M (−1.6%). SAM identical on
  both 2k subsets and both full 200k sets; FUZZ=1 CI passes (457 theorems, standard axioms).
