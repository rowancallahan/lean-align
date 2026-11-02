# Report floor: proofs (branch speed/report-floor-proofs, base spec/report-floor @ e24e8df)

Spec (Rowan): `requiredMapBound := -16` (an answer without a pair needs `bestPossibleScore < requiredMapBound`),
`junkScore := -50` (every printed pair, any label, has `pair.score >= junkScore`). `Proofs/Answer.lean` mirrors it
(CI checks the mirror).

## Status

`lake build` and `sh Testing/scripts/CI_check.sh` pass (standard axioms only, no sorry outside Spec/).
`alignPairs_correct` is proved for every result except a LEFTOVER, which Spec has no answer for yet. The leftover
is one named predicate, `Spec.LastResort.Leftover`, and one hypothesis, `hNoLeftover`. On chr21 no read is a leftover.

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

## The leftover: what Spec needs

`Leftover s a := a.found = none ∧ s.requiredMapBound ≤ a.bestPossibleScore`. This means no pair `>= junkScore`
in hand, and no proof that every proper pair is `< requiredMapBound`, even after `search16`. It can still happen
when:
- `pairGXE` returns `none`: a mate is too short for the pigeonhole at 16 (`fastT 16`);
- a pair `>= -16` was seen but its CIGAR did not re-check (the unproved banded DP failed) and the fallback found nothing;
- the index check failed at build time, so `noIndexAnswer` has bound 0.

The answer printed for a leftover is unmapped with its true bound (`XB >= -16`, `XU:unknown`). What Spec would
need to close the theorem is a new answer form whose `Correct` clause is only the bound (clause 2), with no
`< requiredMapBound` claim, e.g. a `Uniqueness`/result `.gaveUp` ("too many candidate places"):

    | .gaveUp => answer.found = none   -- bound clause (2) still holds; nothing else claimed

With that, `finalize` would label leftovers `.gaveUp`, and `alignPairs_correct` would follow from
`alignPairs_correct_or_leftover` with no `hNoLeftover`.

## Measurements (chr21, index c21m2.idx, `lean-align map … 100 1000`, 200,000 pairs each)

| set | reported (>= junk) | none, bound < -16 | leftover | time |
|---|---|---|---|---|
| chr21_mason | 197,434 | 2,566 | 0 | 8 s |
| chr21_low   | 199,318 |   682 | 0 | 6 s |

Before `search16` (guard fixes only): mason 196,927 / 2,049 / 1,024 leftover; low 198,701 / 494 / 805 leftover.
All of those leftovers were true proper pairs inside the range: mates with tied best placements in repeats, where
the router stopped (T2/T3) or found a tie it could not print. Raising the router's budgets only, with no `search16`,
left 863 / 517.
