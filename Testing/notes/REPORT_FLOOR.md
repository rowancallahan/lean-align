# Report floor (branch `speed/report-floor`, from spec/report-floor e24e8df), 2026-11-02 — work in progress

Spec now: every reported pair scores ≥ `junkScore` (−50); `.unknown` without a pair needs `bestPossibleScore <
requiredMapBound` (−16). There is no third valid answer, so every pair must get a pair ≥ floor or a proof that no
proper pair ≥ −16 exists. Status: the build is red (LastResort/Aligner not yet assembled) because one class has no
feasible valid answer (below); waiting on Rowan's Spec answer. Nothing pushed.

## Done (proved, local commit)
- Step 0: `Proofs/Answer.lean` = `Spec/Aligner.lean` up to the holes; `CI_check.sh` compares them.
- Walk: `Report.fallbackOfK keep` (the fallback keeps walking until a checked pair passes `keep`), `fallbackOfK_sound`.
- No good pair: `TierOpt.tierNo` — `noPairJ` at caps 16/16 (no proper pair of hits) or `pairGXE` at 16 seeing nothing
  → `T3` with `pf = some 16`, bound −17 (`tierNo_ok`, reuses `answerOf_correct` and the whole-genome transport).
- `Floor.bound_of_noPair`, `Floor.score_of_report`.

## Counts (bench `Testing/benches/FloorProf.lean`, today's answers, single thread, 200k pairs)
Pairs breaking the new Spec, resolved in order: walk 3 anchors / walk 16 / discordant (noPairJ 16) / complete search at
16 proves none / complete search finds a pair ≥ −16 / LEFTOVER (a mate < 125 bp, no cap-16 seed guarantee, nothing found).

| set, floor | breaking | walk3 | walk16 | discordant | complete: none | complete: pair | leftover |
|---|---|---|---|---|---|---|---|
| NovaSeq −50 | 12,431 (6.2%) | 2,569 | 170 | 1,066 | 4,870 | 486 | 3,270 (1.64%) |
| mason −50 | 4,811 | 1,486 | 145 | 3 | 2,012 | 1,165 | 0 |
| low −50 | 2,249 | 1,430 | 96 | 0 | 157 | 566 | 0 |
| HiSeq −50 | 9,086 | 2,359 | 205 | 105 | 4,080 | 385 | 1,952 (0.98%) |
| NovaSeq −100 | 9,971 | 2,011 | 89 | 903 | 3,798 | 404 | 2,766 (1.38%) |
| mason −100 | 3,902 | 1,131 | 51 | 3 | 1,767 | 950 | 0 |
| low −100 | 1,643 | 1,011 | 32 | 0 | 123 | 477 | 0 |
| HiSeq −100 | 7,227 | 2,052 | 100 | 104 | 3,068 | 330 | 1,573 (0.79%) |

Cost (NovaSeq −50): walks 4.9 s, discordant 18.6 s, complete search 237 s (128 s of it for the 486 "pair" pairs), vs
~20 s CPU for the whole mapping. The "pair exists, walks miss it" class are mates in repeat families (~2,000 hits within
16 each); the complete search is 20% hit enumeration, 80% partner search near every hit. A checked walk over the exact
hit list (best first, ≤ 64 hits, stop at the first pair ≥ floor) finds 18 of 20 at 1/4 of the cost; anchor walks from
the rarest seed do not (it is usually spoiled on these reads).

## Open (Rowan)
1. Short mates (< 125 bp) with no pair found: no feasible complete search (only the spec-level whole-genome scan).
2. A budget for the complete search on repeat pairs (else ~25 ms+ per such pair).
Both point to one Spec result for "gave up / too many candidate places".
