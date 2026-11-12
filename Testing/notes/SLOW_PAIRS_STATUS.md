# Slow pairs: fixed (2026-11-10)

Merged into festive: fix/fast f465a57. Below the Spec, proved, FUZZ=1 CI green, SAM byte-identical.

## Cause
Single read pairs trimmed or adapter-cut to 25-42 letters, in poly-A, 2-letter repeats or repeat families, took 1-60 s in the last pair-search stage (hits x hits scans). Output is in order, so other workers idled.

## Fixes (all exact-equality swaps)
- keepQ: binary-search partner filter (351301d).
- chromosome gate as a table lookup (c2e0bb6).
- pair window: only second-mate hits that can start within range are checked (a50a67a).
- jobs of 4000 pairs, 32 in flight.

## Results, 4 threads
| run | before | after | minibwa |
|---|---|---|---|
| HiSeq 5M gz wall | 111.0 s | 84.0 s (6164113) | 474.0 s |
| NovaSeq 5M gz wall | 96.8 s | 83.1 s (6164113) | 255.6 s |
| NovaSeq streamed 10M | 303.5 s | 196.1 s | 742.8 s (159 s load) |
| NovaSeq streamed 20M | 717.7 s | 389.0 s | no valid run yet |
| NovaSeq streamed 40M | - | 778.5 s, 55.9 Gbp/hr | no valid run yet |
| HiSeq 34M traced, wall | 1317 s | 683 s | running |
| NovaSeq 40M traced, wall | 1327 s | 757 s | - |
| jobs > 5 s (HiSeq 34M / Nova 40M) | 25 / 40 | 0 / 0 | - |
| time with < 4 jobs running | 50% / 39% | 8.5% / 0.3% | - |

Slowest pair after the fix: 0.70 s (HiSeq), 0.57 s (NovaSeq). No pair >= 1 s in 34M + 40M pairs.
SAM md5 identical: 5M gz both sets, streamed 10M.

## Not done
- First score-0 pair stop: not needed.
- Seed reordering / low-complexity index part: not needed; router order would change output.
- Test pairs: branch bench/slow-pairs.
