# Report floor: proofs (branch speed/report-floor-proofs, base spec/report-floor @ e24e8df)

## Status: BLOCKED after Step 0 (no Lean in this container)

The container had no elan or Lean toolchain. The network policy refused raw.githubusercontent.com,
github.com/releases and releases.lean-lang.org (403 connect_rejected), so `lake build` could not run.
Nothing below was checked by Lean. Step 2 (a)-(c) was not started, and no chr21, NovaSeq or HiSeq
measurements were made. Fix: allow those hosts in the environment's network settings, or use a
release with a toolchain or build cache. Then rerun this task.

## Step 0 (done)

- `Proofs/Answer.lean` is now `Spec/Aligner.lean` up to `/-! ## The index and the aligner`, with
  `import Spec.Mapping` changed to `import Proofs.Mapping`, plus one comment line at the top and `end Spec`.
  It now has `requiredMapBound := -16`, `junkScore := -50`, the clause-1 floor `pair.score >= junkScore`,
  and `.unknown`/`none` with `bestPossibleScore < requiredMapBound`.
- `Testing/scripts/CI_check.sh` now compares the two textually, like the Fasta/Fastq/Sam mirror checks.
  It passes on the new file and FAILS on the old file at e24e8df (checked with the shell; this step needs no Lean).
- Why not import Spec directly: `Spec/Aligner.lean` also holds the `sorry` holes `buildIndex` and
  `alignPairs`, and `Proofs/Aligner.lean` defines the same names in `namespace Spec`. Importing it
  would clash and pull in the `sorry`. Making that clean needs a split of Spec, which is frozen.
- Not checked by CI either (outside this task): `Proofs/Alignment.lean` and `Proofs/Mapping.lean`
  against `Spec/`. They differ by design, because the proofs are inlined.

## Where the build breaks (from reading the code; not confirmed by a build)

Only `PairAnswer.Correct` changed. `CorrectU` (Bridge.lean:190) is internal and has no floor, so
Bridge, Report, Whole and `noIndexAnswer_correct` still elaborate. Only
`LastResort.finalize_correct` (LastResort.lean:107) targets `.Correct`. It breaks in four places:

1. Degenerate branch (`some c`): the all-insertion pair scores -(6+2·len1) - (6+2·len2) (-612 for 2x150).
   That is below junkScore -50, so `pair.score >= junkScore` is false, not merely unproved.
2. Pass-through (`else a`) and the `none` arm: every `found = some` from the router or fallback
   (`foundOf`, `fallbackOf`, ties) needs `score >= junkScore`. `CorrectU` gives only `IsProper`.
3. `none` arm, `.unknown` clause: `bestPossibleScore := junkScore - 1` must be `< requiredMapBound`.
   That holds for the defaults (-51 < -16) but not for every `InsertSettings`.
   Use `requiredMapBound - 1`.
4. Pass-through, `.unknown` with `found = none`: the guard `junkScore ≤ bestPossibleScore` gives only
   `bestPossibleScore < junkScore`. The guard must use `requiredMapBound`.

`alignOne_correct` (Aligner.lean:313, 352) uses `finalize_correct`, so it fails with it. Nothing else
should fail. `fallbackFrom` (Aligner.lean:116) still starts the fallback at `junkScore`, which is now
-50. The proof does not depend on that value, but the fallback should start at `requiredMapBound`.

## Plan for finalize (unproved design)

Each step is a decidable check on the answer in hand. The main theorem's statement does not change.

0. `found = some rep`, with `rep.mate1.score + rep.mate2.score >= junkScore`: keep it.
   This is decidable on the report, because `pair.report = rep` gives `pair.score` = the sum of the report's scores.
   This fixes break 2 for every pair that is printed.
0'. `found = some rep` below junkScore, labelled `.unique` or `.multimapper`: the pair is a best proper pair.
   So `bestPossibleScore := its score` is a proved bound. Answer `none` if that score is `< requiredMapBound`.
   This always holds when `junkScore ≤ requiredMapBound`. It costs nothing.
1. (b) Discordant: sort-merge the mate-1 and mate-2 hits. If no FR pair lies within `range` (plus dovetail
   slack), no proper pair has both mates at their hits. Combined with (a), that gives a bound `< requiredMapBound`.
2. (a) Pigeonhole: if pair >= -16 then each mate >= -16, so each mate has at most 4 errors. With at least
   5 non-overlapping exact seeds, plus 1 for each seed `capBudget` skipped, a seed hits at the true place.
   Then the hit lists from (b)/(c) are complete for pairs >= -16. Reuse the existing seed and bound lemmas.
3. (c) Few hits: align each mate in a window around each hit (the window the bound lemma needs) with the
   proved kernel or checker. If every hit pair is `< requiredMapBound`, answer `none` with that bound.
4. `leftover`: none of the above went through. The answer goes out through an explicit `gaveUp`
   placeholder that claims nothing. This is the one place where the proof does not yet go through.
   Its Spec meaning is Rowan's to decide; nothing is invented here.

Needed from Rowan for `leftover`: a Spec answer for "best pair found < junkScore, bound not proved
< requiredMapBound". A likely form is unmapped with no bound claim ("gave up" / "too many places").
Until it exists, `alignPairs_correct` cannot be fully proved for those reads.

## Measurements

None. Lean could not be installed, so no measurements were possible. The reads exist as release assets
(`bench-release`: hg38_mason/low, novaseq_200k, hg002_1M) and can be fetched with `gh api`, but they are no use without a build.
