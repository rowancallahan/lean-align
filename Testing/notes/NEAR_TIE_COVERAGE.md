# Near-tie coverage of the degenerate last-resort pair (hg38, M2 at 88bde0a, junkScore −16)

Question (parent / Rowan): for pairs that end with the degenerate last-resort pair (no proper pair found, bound ≥ −16), how
many would a "near-tie" report cover? Debug measurement only: `WG_LASTRES=1` in the bench (**not pushed**: a local debug
commit on top of 88bde0a, patch kept off the branch); nothing in Spec/, Main.lean, Proofs/ changed.

Method: per pair the bench reruns the shim's own decision (`Spec.tierCfg`, `tierPair`, `Report.answerOfPair` with
`reportTies`, `fallbackFrom`, `mateRescue`, whole-genome pgs); a pair is degenerate when `found = none` and `junkScore ≤ bound`
(what `LastResort.finalize` turns into the degenerate pair). For those: with bound b, the distinct proper pairs of score
≥ b − g (g = 4, 8, 16) enumerated from one mate's hits (`hitsAtQ` + `pairsQC`, as the T1gm dump), and each mate's hit count at
depth b + 16. The pair guarantee only reaches caps with `fastT` (`sbound P < len/25`: about cap 17–19 for 150 bp), so the
enumeration is cut to the deepest feasible cap; the gap really reached is recorded and used below. hg38 bench index,
200k pairs per set, mates trimmed as in the shim. Bench run: `tasks 4` on `taskset -c 0-3`.

## How many pairs are degenerate (this measurement)
| set | pairs | degenerate | by tag | bounds |
|---|---|---|---|---|
| mason | 200,000 | 1,841 (0.92%) | T3 1,829, T2 12 | 0: 1,176; −13: 665 |
| NovaSeq | 200,000 | 5,247 (2.62%) | T3 4,823, T2 312, T1 112 | 0: 2,459; −13: 2,031; −12: 357; −4/−8/−16: 392 |
| HiSeq (hg002) | 200,000 | 2,232 (1.12%) | T3 1,927, T2 185, T1 120 | 0: 1,636; −13: 257; −12: 113; rest 226 |
These are higher than the stage-5 note's printed counts at −16 (mason 1,261, NovaSeq 1,938, HiSeq 1,112) and than the parent's
0.2–1%: not explained here (the bench runs the shim's functions but not the shim; e.g. a chromosome-boundary or the
`fit` condition could differ). Treat the split below as a split of *this* set, and recheck the totals with the shim.

## Split
(a) ≥ 2 distinct proper pairs (different placements) of score ≥ b − g; (b) not (a): hits for both mates but no proper pair;
(c1) exactly one proper pair within the gap; (c2) a mate has no hit at all within the depth reached; unknown: no enumeration possible.

(a) by gap g (pairs where the gap g was reached in full / of all degenerate):
| set | g = 4 | g = 8 | g = 16 |
|---|---|---|---|
| mason | 0 of 1,841 | 55 of 1,491 (3.7%) | 386 of 1,176 (+2 where only a shallower gap was reachable) |
| NovaSeq | 31 of 4,696 | 105 of 3,156 | 270 of 1,991 (+21 shallower) |
| HiSeq | 96 of 2,110 | 185 of 1,957 | 402 of 1,800 (+16 shallower) |

Classes at the deepest gap reached (≤ 16):
| set | (a) ≥ 2 pairs | (b) hits both mates, no proper pair | (c1) exactly 1 pair | (c2) a mate has no hit | unknown |
|---|---|---|---|---|---|
| mason | 388 (21.1%) | 1,139 (61.9%) | 261 (14.2%) | 53 (2.9%) | 0 |
| NovaSeq | 291 (5.5%) | 2,655 (50.6%) | 153 (2.9%) | 1,915 (36.5%) | 233 (4.4%) |
| HiSeq | 418 (18.7%) | 864 (38.7%) | 179 (8.0%) | 703 (31.5%) | 68 (3.0%) |

## Reading
- A near-tie report (two or more proper candidates within g of the bound) covers, among the pairs where the gap was reached in full:
  g = 4: 0% (mason), 0.7% (NovaSeq), 4.5% (HiSeq); g = 8: 3.7%, 3.3%, 9.5%; g = 16: 33%, 14%, 22%.
  As a share of all degenerate pairs at the deepest gap reached (class table): 21% mason, 5.5% NovaSeq, 19% HiSeq.
- The biggest class is (b): both mates have hits but no proper combination (39–62%): a cheap "no good proper pair" proof for these
  could push the bound below junkScore. (c2) (a mate has no hit at the reached depth) is 3% on mason but 32–37% on the real sets;
  the pair bound is already limited by the missing mate there.
- (c1): one proper pair exists within 16 but the fallback did not print it (3–14%): a fallback miss, not a tie.
- Caveats: the enumeration is cut at the guarantee's depth (many pairs never reach g = 16); (a) counts candidate *pairs*
  (one mate's placement differing counts as different); the totals differ from the stage-5 note (above).
