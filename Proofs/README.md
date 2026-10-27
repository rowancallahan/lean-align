# Proofs/: the spec with its proofs filled in

`Spec/` is the frozen statement (comparator challenge). `Proofs/` is the solution: same namespace
(`Spec`), same names, same statements, with every `sorry` replaced and the two holes
(`buildIndex`, `alignPairs`) defined.

| File | What | State |
|---|---|---|
| `Alignment.lean` | `cigar_decodes`, `allPaths_ne_nil`, `allPaths_complete`, `alignSpec_optimal` | proved |
| `Mapping.lean` | `exists_best` | proved |
| `Answer.lean` | `Spec/Aligner.lean` up to the holes, unchanged | (no proofs needed) |
| `Bridge.lean` (+ `Hits.lean`, `Tiers.lean`) | old router proofs (`tierPair_sound`, `TierOk`) → new spec | proved |
| `Aligner.lean` | `buildIndex`, `alignPairs` defined on the tier router; `alignPairs_correct` proved from the bridge (+ `Index.lean`) | proved |

`alignPairs_correct` is already proved *from* the open lemmas, so each one below is independent.

## Tasks (all proved 2026-10-27; M2 next)

- **B1** `walk_of_path`, `score_eq_walkScore`: a `Path` is an old `IsMonotoneWalk` with the same
  score (`scoreWalk` is the same function on both sides; map the steps).
- **B2** `hit_of_alignment`, `alignment_of_hit`: `hitsBoth` (old: windows × strands, each with its
  best score `windowScore` via `getBestAlignment`) against `GenomicAlignment`. Use
  `getBestAlignment_returns_a_maximum_score` / `_valid_walk` (old_spec/AlignmentSpec.lean) and B1.
  Note `oldPlacement` uses `stop - start`; `fits` gives `start ≤ stop`.
- **B3** `isProper_iff`: `Mapping.IsProper` vs `properPairU` (old_spec/PairSpecU.lean). Same
  conditions; arithmetic.
- **B4** `encodes_decodeRead`: `Encodes` (kernels/mapper_band/MapperBandKernel.lean) holds for
  `decodeRead` (`Char.ofNat` of a byte has that byte's `toNat`).
- **B5** the index (`Aligner.lean`): define `buildLoaded` (the fast builders the freeze used:
  bench/WholeGenome.lean `build` / `pmap` modes), `saveIndex` / `loadIndex` (one ByteArray;
  `loadIndex ByteArray.empty = none`, e.g. a magic header), `indexOk` (cutOk, check2P, and the
  unpacked chromosomes equal the genome's bytes), `roundTrips`; prove the three lemmas.
- **B6** `answerOf_correct` (`Bridge.lean`): case on the tag. Bounds: t1 (each mate's unique best at
  its cap is its global best, so `x.2 + y.2` bounds every pair), t1g / t1u (`pairSpecUT` for every
  cap ≥ g0, so take caps below any competitor), t2b (direct), t2 / t3 (`FloorOk`: floors per mate,
  and `pf`), t0 impossible (both mates are `some`), t1gm / t1um bound 0. Uses B2, B3.
- **M2** (after M1 is green): report the found pair with a CIGAR and `unique` / `multimapper`
  (notes/NEW_SPEC_ADAPTERS.txt R1, R2; T1's pairs need the dovetail check, R2/M4).

## Names to know (so the old code is not confusing)

- `sc0` (old code, `MapSpec.sc0`, used in ~63 files under mapper/, index/, kernels/) **is**
  `defaultScoring` from the spec: match 0, mismatch −4, gap open −6, gap extend −2. It is the same
  numbers in the old `AlignmentSpec.Scoring` type. The bridge calls it `oldDefaultScoring`. Renaming
  it in the old code is left for the proof-golfing pass; do not rename it while proving.
- Other old → new names: `Window` (chromosome, start, length) × `Strand` (`fwd` / `rev`) is the old
  placement; the new `Placement` uses (chromosome, start, stop, `forward` / `reverse`), see
  `oldPlacement` / `newPlacement`. Old `revComp` = new `reverseComplement`. Old "penalty" P is
  score −P. `dcost0` (distance cost 0) makes the old pair score the plain sum of the two mates' scores.
- Milestone M1 is deliberately bounds-only: `answerOf` reports no pair and `uniqueness := .unknown`.
  That is correct and intended for the first green proof, not a bug. M2 adds the reported pair.

## Rules

- Do not edit `Spec/` (frozen; `Spec/FROZEN.sha256`). Statements in `Proofs/` must stay identical
  to `Spec/` (comparator checks this after the Lean 4.35 bump).
- No new axioms; no `sorry`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `partial` in
  finished proofs. Check with `#print axioms Spec.alignPairs_correct`.
- Build: `lake build Proofs`. Full re-check: `sh scripts/check.sh`.
