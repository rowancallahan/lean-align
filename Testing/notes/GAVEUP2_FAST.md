# gaveup2-fast: the ManyPlaces prototype (d18dbbd) vs festive-fermi 0e48158 (branch `speed/gaveup2-fast`)

Ir = callgrind of the shim on the first 2000 pairs. Exact rewrites only: SAM byte-identical to d18dbbd on the
four full 200k sets and both 2k subsets; `CI_check.sh` passes; every change is a `@[csimp]` with an equality
proof; no Spec/Main/Shim edits.

## 1. Where d18dbbd's extra Ir is (gaveUpPlaces = 50, gaveUpRepeats = 500, gaveUpSeeds = 2)
| | 0e48158 | d18dbbd | extra |
|---|---|---|---|
| NovaSeq | 960.6M | 2732.1M | +1771.5M |
| HiSeq | 1309.4M | 1993.3M | +683.9M |
NovaSeq `afterLeftover` 1685.8M:
- mate 1's `hitsX`: 1247.4M over 63 calls.
- mate 2's `hitsY`: 273.9M.
- `repeatMate`: 150.4M. It counts all grid seeds, since 2 repeat seeds are needed and `countP` never
  short-circuits.
HiSeq `afterLeftover` 525.8M: `hitsY` 252.9M, `hitsX` 177.3M, `repeatMate` 84.2M.

## 2. Is stopping hitsKPF early the lever? Only partly
Implemented exactly (`walkIn` / `walkOut` / `walkSK`, `hitsXS_spec`, `lookAtG_eqF`): mate 1's hits are
enumerated chromosome by chromosome and diagonal by diagonal, and the walk stops (`.gaveUp`) once the hits
scoring `≥ req` reach `gaveUpPlaces` distinct placements. Proof facts used:
- `distinctGo` on a concatenation is `distinctGo` of the prefix, continued (`distinctGo_append`).
- It is stuck once `k` are collected (`distinctGo_stop`).
- So a prefix that reaches `k` decides `manyHits` on the whole list. No change to Spec or to any statement.
Result: only 6 of 63 NovaSeq calls stop early, so the saving is −113M. The expensive mates have many candidate
diagonals (118k walked on NovaSeq, ~7k Ir each) but fewer than 50 placements within the cap. Costs on NovaSeq:
- per-diagonal word filter (`fineE` / `lanesAnyV`): 379M.
- shape kernels: ~430M.
- seed lookups of the `sbound + 1` rarest seeds: 158M.
These mates are semi-repetitive: seeds under 500 places, or fewer than 2 repeat seeds.

## 3. Changes
| commit | change | NovaSeq | HiSeq |
|---|---|---|---|
| d18dbbd | base | 2732.1M | 1993.3M |
| (cherry-pick of efc8ac8) + 0ea70cc | empty-slice gate; mate 1's walk stops at 50 distinct placements (`hitsXS_spec`, `lookAtG_eqF`) | 2619.1M | 1896.5M |
| next commit | `repeatMateF` stops at `gaveUpSeeds` repeat seeds (`countGE_eq`). `hitsSKNG` does no lookups when no chromosome passes the gate (mate 2 when mate 1 has no hit). | 2348.3M | 1734.4M |
Total from d18dbbd: NovaSeq −14.0%, HiSeq −13.0%. Against 0e48158: NovaSeq +1387.7M (2.44×), HiSeq +425.0M
(1.32×).

Native user CPU, 200k pairs, 4 cores, one warm run each:
| | 0e48158 | d18dbbd | this branch |
|---|---|---|---|
| NovaSeq | 19.5 s | 48.0 s | 42.6 s |
| HiSeq | 21.8 s | 53.0 s | 41.4 s |

## 4. The repeat witness at N = 200 vs 500 (gaveUpRepeats; measured on this branch, local change, not committed)
| | N = 500 | N = 200 |
|---|---|---|
| NovaSeq total | 2348.3M | 1565.8M |
| NovaSeq witness (`repeatMate`) | 115.3M (730 seed lookups) | 63.5M (681) |
| NovaSeq second looks (`lookAtG`) | 63 calls, 1185.7M | 55 calls, 455.2M |
| HiSeq total | 1734.4M | 1682.9M |
| HiSeq witness | 47.2M | 25.4M |
| HiSeq second looks | 28 calls, 218.4M | 25 calls, 188.5M |
| SAM lines changed vs N = 500 | — | NovaSeq 14, HiSeq 4 (2k subsets) |
A true seed costs about `N` genome-checked places (~1.8k Ir each) plus the in-chromosome count of `N` places
(~480 Ir each). At N = 200 the true-seed verification is ~2.5× cheaper. More importantly, the 8 NovaSeq pairs
that now give up before the second look were the expensive semi-repetitive ones.

## 5. What would close the rest
- The second look on semi-repetitive mates is the cost: candidate diagonals × (filter + kernels). Exact cuts
  left are kernel-level (the word filter is already lane-parallel; ~3.2k Ir per diagonal).
- Spec-side, cheapest first: a lower `gaveUpRepeats` (N = 200 above), or `gaveUpSeeds = 1`, catches these
  mates before the second look. A diagonal-count trigger is not a witness: candidates are not alignments.
- mate 2 (HiSeq `hitsY` 127M): the same early stop applies (`hitsKPFNG` through `walkOut` with the gate). Not
  done; on HiSeq it would help only if mate 2 reaches 50 placements.
