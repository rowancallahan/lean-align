# Report floor: proofs (branch speed/report-floor-proofs, base spec/report-floor @ e24e8df)

Spec (Rowan): `requiredMapBound := -16` (an answer without a pair needs `bestPossibleScore < requiredMapBound`),
`junkScore := -50` (every printed pair, any label, has `pair.score >= junkScore`). `Proofs/Answer.lean` mirrors it
(CI checks the mirror).

## Status (round 2: Rowan: no `gaveUp`, close the leftover in code)

`lake build` and CI pass (standard axioms, no sorry outside Spec/). Proved:
- `alignPairs_correct_or_leftover`: every result is `Correct` or `IsLeftover`. It has no hypothesis.
- `alignPairs_correct_of_long`: Spec's exact statement, with NO leftover hypothesis, for `-16 ≤ requiredMapBound`,
  `junkScore ≤ requiredMapBound` (the defaults) and mates of at least 125 letters.
- `alignPairs_correct`: Spec's statement plus `hNoLeftover`, for any settings and lengths.

The second look at a leftover (`lookAt` / `lookSpec`, `LastResort.lookAnswer`) lists every proper pair within the
cap `c` that scores at least `-c` (`pairsAt_mem`, any `c ≤ 16`). If the list is empty, the bound is `-(c+1)`. If not,
the top pair is printed. Its CIGAR comes from the proved optimal aligner (`bandDoublingAlign = getBestAlignment`,
`cigarOk_of_hit`), so there is no re-check that could fail. Its score is a proved bound, through a `t2b`-style
`TierOk`. Uniqueness is `.unknown`.
1. Seen pair, CIGAR re-check failed: closed (no re-check).
2. Index check failed: the record now holds the genome (`chromsNats`/`ungen`, `ungen_chromsNats`). `lookSpec`
   searches every window with `hitsF = hitsBoth` (total; slow; only for genomes that do not `Fit`). The answer is
   proved on the record's genome and moved to the named genome (`correct_transfer`, same letters).
3. Short mates: `lookCap s R1 R2` (now `min 16 (-requiredMapBound)`) is a parameter. `errorsChecked`, `capOfLens`,
   `capOfLens_le`, and `fastT_capOfLens` are ready: every mate of 25 letters or more has the seeds for
   `4 * errorsChecked (shorter)`. When the Spec lands, set `lookCap := capOfLens R1.size R2.size`.
   `alignOne_not_leftover` then needs only the 25-letter minimum in place of 125.

The leftover now remains only for:
(a) a mate without the seeds for the cap, i.e. under 125 letters at cap 16 (case 3, until the Spec lands);
(b) settings with `requiredMapBound < -16`, or `junkScore > requiredMapBound`.

For (b) with `junkScore > requiredMapBound`, the Spec itself has no correct answer. Example: junk -10, required
-16, best proper pair -12. No pair can be printed, and the bound cannot go below -12. So the Spec needs
`junkScore ≤ requiredMapBound`, as a constraint on `InsertSettings` or by clamping. With the length-scaled bound,
that means `junkScore ≤ -16`.

Measured on chr21 after round 2: mason 197,434 reported / 2,566 none (bound < -16) / 0 leftover;
low 199,318 / 682 / 0. Same counts as round 1.

## Round 1

## Where the build broke (confirmed with Lean)

Only `LastResort.finalize_correct` (5 errors: the degenerate pair is below junkScore; the pass-through and the
`none` arm had no `>= junkScore` proof; the `.unknown` guard used junkScore) and, through it, `alignOne_correct`.

## What is proved

`Proofs/LastResort.lean`:
- `finalize`: a pair with printed score `>= junkScore` is kept (`score_of_report`: the printed sum is the pair's
  score). A pair below junkScore is dropped. Its bound is `provedBound`: the answer's own bound, or the pair's
  score if the pair is `.unique` / `.multimapper` (`provedBound_ok`). With no pair (`boundOnly`), the answer is
  correct if the bound is `< requiredMapBound`, or if no proper pair exists at all (`noPair`, `no_proper`), when
  it becomes `requiredMapBound - 1`. Anything else is a `Leftover`. The degenerate all-insertion pair is gone.
- `finalize_correct`: `Correct ∨ (Leftover ∧ CorrectU)`, with no hypothesis. A leftover's bound is still true.
- `search16` / `search16_ok` (steps (a)+(b)+(c) in one): the existing exact pair search `pairGXE` at `Gc = 16`
  (`pairGXE_sound`; its hit lists come from the seed pigeonhole `hitsKPF_mem` and the near-partner list
  `hitsKPFN`, so they are complete for mates `>= -16`). If it sees no proper pair `>= -16`, that gives a T3 with
  `pf = 16`, i.e. bound `-17` (via `FloorOk`). If it sees one, the best is unique (T1u, printed) or a proved tie
  (T1um, one tied pair `tie16` printed after re-checking). No new seed or bound machinery was needed.

`Proofs/Aligner.lean`:
- `fallbackFrom` starts at `requiredMapBound`.
- `answerOfReads`: router, re-check, finalize. A leftover is answered again from `search16` of the router's output.
- `alignPairs_correct_or_leftover` (no extra hypothesis): every result is `PairResult.Correct` or `IsLeftover`.
- `alignPairs_correct` / `alignPairs_end_to_end`: Spec's statements plus ONE hypothesis
  `hNoLeftover : ∀ i result, (alignPairs …)[i]? = some result → ¬ result.IsLeftover insertSettings`.

(Round 1 proposed a `.gaveUp` answer for the leftover. Rowan declined it, and round 2 closes the leftover in code.)

## Measurements (chr21, index c21m2.idx, `lean-align map … 100 1000`, 200,000 pairs each)

| set | reported (>= junk) | none, bound < -16 | leftover | time |
|---|---|---|---|---|
| chr21_mason | 197,434 | 2,566 | 0 | 8 s |
| chr21_low   | 199,318 |   682 | 0 | 6 s |

Before `search16` (guard fixes only): mason 196,927 / 2,049 / 1,024 leftover; low 198,701 / 494 / 805 leftover.
All of those leftovers were true proper pairs inside the range: mates with tied best placements in repeats, where
the router stopped (T2/T3) or found a tie it could not print. Raising the router's budgets only, with no `search16`,
left 863 / 517.
