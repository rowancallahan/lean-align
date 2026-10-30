# n29-heur: the tier 2 heuristic's pairs at (almost) no extra cost (2026-10-30)

Branch `speed/n29-heur` on tree f8b83fe. **No chr21 numbers:** the network policy blocked the data
hosts (ngi-igenomes S3, storage.googleapis.com, giab S3), so everything below is on a synthetic genome
(Testing/scripts/sim_genome.py, 46 Mb, 1 chromosome, seed 21; uniform random + repeat families, far fewer
repeats than chr21) with `sim_pairs.py` mason / low (200k, seed 7) and an "off-target" set (192k low pairs
from another synthetic genome + 8k on-target, like real reads on chr21). Re-measure on chr21 before use.

Metric: callgrind Ir inside `tierPair` (20k pairs, 1 task; deterministic). Wall CPU on this box varied
±1.5 s between identical runs, so it is a sanity check only. "kept" = RTX kept (T1, T1g, T1u).

## Why `cmax 16` works
The heuristic only adds RTX pairs through T1u: `tierXE` runs the exact pair search only when the summed
ceiling is ≤ 16. So a mate's search can stop at `16 + 1 − other mate's floor`, and a pair whose floors
already sum over 16 has nothing to gain. Lower ceilings also make the exact pair search cheaper (on
syn low XH=1 is already cheaper than XH=0). Side effect: pairs left with summed ceiling > 16 become T3
instead of T2 (syn mason: 9495 at-truth T2 pairs with ceilings 20–40 lose their found pair). Kept is
unchanged, but for M2 (found pair + CIGAR) those found pairs would be gone; use cmax 40 or off if M2
wants them (cmax 24/32/40 cost almost as much as off).

## Results (Ir in tierPair, kept; 20k pairs)
| config | mason | low | off-target |
|---|---|---|---|
| XH=0 | 8.23G 17229 | 5.29G 18904 | 2.60G 759 |
| XH=1 (old) | 9.51G 17793 | 4.63G 19578 | 2.87G 784 |
| cmax 16 | 8.90G 17793 | 4.49G 19578 | 2.66G 784 |
| cmax 24 / 32 / 40 | 9.32 / 9.47 / 9.49G | 4.59 / 4.61 / 4.62G | 2.67 / 2.72 / 2.86G |
| cmax 16 + chk off | 8.77G 17793 | 4.35G 19578 | 2.65G 784 |
| + bucket limit 500 | 8.73G 17793 | 4.30G 19578 | 2.65G 784 |
| **+ bucket limit 100 (proposal)** | **8.68G 17795** | **4.21G 19579** | **2.65G 784** |
| + bucket limit 50 / 20 | 8.65 / 8.63G | 4.14 / 4.15G | 2.65G |
| + 4 diagonal pairs (np 4) | 8.64G 17794 | 4.17G 19579 | 2.64G |

Gained pairs, proposal settings vs XH=0 (200k): mason 5802 (5791 at truth, both mates within 10 bp; 2 lost),
low 6251 (6248 at truth; 0 lost).

## Wall CPU (200k pairs; this box: ±1–1.5 s between identical runs)
| | XH=0 | XH=1 (old) | proposal |
|---|---|---|---|
| mason, 4 tasks (median 3) | 13.65 s 172819 | 16.88 s 178611 | 15.70 s 178619 |
| low, 4 tasks (median 3) | 11.17 s 189384 | 12.44 s 195620 | 12.45 s 195635 |
| low, 4 tasks, another pair of runs | 11.95 s | | 11.82 s |
| off-target, 4 tasks (median 3) | 8.32 s 7572 | 9.58 s 7829 | 9.18 s 7828 |
| low, 1 task (median 2) | 8.98 s | 8.51 s | 8.12 s |
| low, 4 processes × 50k, 1 core each (median 2) | 8.49 s | 8.72 s | 8.29 s |

Finding: one 4-task process costs ~40% more CPU than 4 single-task processes on the same pairs, for XH=0
too (low: ~12 s vs 8.5 s). Chunk size (16 vs 1024) does not change it. Likely shared-object refcount
traffic between threads (`lean_dec_ref_cold` is ~6% of Ir under 4 tasks); not investigated further.
Without that contention, the proposal costs less than XH=0 on low (−10%) and ~+10% on mason.

## Did not help
- `xb` (skip when the exact pair search's budget at the floors is over 1500): −5M Ir, smallK costs eat it.
- `fin` (stop at a proper pair on the summed floors): −17M mason, noise level.
- `skp` (skip pairs already at ≤ 16): +2.4 s wall on low — the heuristic's lower ceilings are what make
  the exact pair search cheap there.
- Word-level Hamming (2-bit packed compare, 32 letters/step, checked equal to `hamD` on 600k pairs):
  +50M Ir; `hamD` already stops at the limit and packing the reads costs more.
- r 1 (one rarest seed): −125M but −89 pairs. np 2: −2 to −10 pairs.

## Left
- The router's re-check `rescoreRunsA` (~230M on syn mason, Array Char per letter) and `hamD`
  (145M, per-letter `PGen.get`) are the largest remaining heuristic costs; the first needs a proved
  `@[csimp]` (it is in the router), and would speed XH=0 too.
- chr21 / hg38 confirmation, especially of bucket limit 100 (chr21 repeats).
