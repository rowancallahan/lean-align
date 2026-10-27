# Review of Proofs/Bridge.lean and Proofs/Aligner.lean (task B3, read-only)

Result: **no false statement found.** `isProper_iff` is proved (commit on `proofs/proper-b3`).
Checked by reading core against Spec; nothing was compiled beyond the B3 proof.

## Checked clean
- `isProper_iff` (proved): strands, `fwdRev`, `stop - start` (needs `start ≤ stop`, from `fits`), dovetail terms.
- Step names: Spec `gapX` = reference only = old `gapX` (y only); `gapY` = query only. `oldStep` is right. Both `scoreWalk`s are the same function.
- `walk_of_path`: counts of diag+gapY / diag+gapX equal the sums of `xConsumed` / `yConsumed`. `score_eq_walkScore`: `sc0 = ⟨0,-4,-6,-2⟩` = `defaultScoring`.
- `hit_of_alignment`: `Strand.orient` reverse = `reverseComplement` = old `revComp` (same `complement`); a fitting placement has start ≤ stop ≤ n, so `⟨chr, start, stop-start⟩ ∈ allWindows` (len ≤ n − start); `windowSeq` = `reference` (start+len = stop ≤ n); best score ≥ alignment score ≥ T, so it is a hit.
- `alignment_of_hit`: hit ⇒ `windowSeq = some ys`, `getBestAlignment = some (path, s)`; `newPlacement` has stop = start+len ≤ n, take len = take (stop−start). Needs the converse of B1 (old walk → `Path`), which is true.
- `boundOf` per tag, against `TierOk` (mapper/TierRouter.lean ~555):
  - t1: `mapSpecBoth` unique best at its cap is the best of all hits ≥ cap; any alignment scoring above it would itself be a hit. So x.2+y.2 bounds every pair.
  - t1g/t1u: result is the same `(x,y)` for every cap ≥ g0; take caps ≥ max(g0, −s) covering the pair's hits; `bestPairD`'s `find?` gives `score ≤` (equal placements ⇒ equal score). `dcost0 = 0` so `pairScoreD = sum`.
  - t2b: direct (`dcost0`). t1gm/t1um/t0: bound 0 (`score_nonpos`; t0 impossible with both `some`).
  - t2/t3: floors from `MateFloor` (any T); with `pf = some G0` take P = max(G0, −s) ⇒ pair score < −G0, i.e. ≤ −G0−1. The `min` in `boundOf` matches.
- `answerOf_correct` obligations: `found = none`, `uniqueness = .unknown` make parts 1 and 3 trivial.
- `Aligner.lean`: `alignOne` (none/none gives `trimmedAway .one`, which holds), `noIndexAnswer_correct`, `loadIndex_buildIndex`, `alignPairs_correct` already compile modulo the B5 sorries.
- `encodes_decodeRead`: `Char.ofNat n` for n < 256 has `toNat = n` (valid scalar), sizes equal.
- `indexOk_sound`: `GenomeBytes` is `Array` size and per-chromosome `Encodes`; true if `indexOk` checks unpacked chromosome bytes = genome bytes and `decode` uses bytes < 256. `tierPair_sound` is fed `cutOk`, `GenomeBytes`, `check2P` exactly in this form.

## Notes for B5 (not errors)
- `MapSpec.Mz.MzIdx` and `MapSpec.Fast.PGen` have no `DecidableEq`/`BEq` visible (`PGen` derives only `Inhabited`). `roundTrips` must be a hand-written structural comparison (fields, `ByteArray`/`Array` equality via `.data`/`toList`), and `roundTrips_load` then needs that comparison to imply equality. Otherwise `roundTrips_load` is unprovable for an arbitrary Bool.
- `loadIndex` must be total on `ByteArray.empty` only; `roundTrips_load` is only about `saveIndex` output, so an unsound parser on junk is allowed.
