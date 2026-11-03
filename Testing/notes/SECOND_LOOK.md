# second-look: the floor's second look on non-repeat leftovers (branch `speed/second-look`, off 565d1e8)

Base festive-fermi 565d1e8 (Rowan's Spec, proved; N = 200, K = 2). Baseline: 0e48158 (no floor). Ir = callgrind of
the shim on the first 2000 pairs. `CI_check.sh` passes. SAM byte-identical to 565d1e8 on the four full 200k
sets, both 2k subsets and 20k-pair samples.

## 1. The leftover pairs
`Testing/benches/SecondLookBench.lean` (`lake exe second_look_bench`, unproved, measurement only) replays the
pipeline's stage logic and lists the pairs that reach the final `lookAt`: 33 on NovaSeq 2k, 16 on HiSeq 2k,
302 / 174 on the first 20k pairs.
- On NovaSeq 2k, 27 of 33 find no pair (`boundsOnly`, bound −17 < −16).
- Hits per mate within the cap are few (0–150, one mate at 16,099), so the hits do not cost.
- Candidate diagonals that yield nothing cost: filter plus kernels on seeds of a few hundred places each.
- Mate 1's full search costs as follows (bench, native µs, NovaSeq 2k):
  - one pair 29,901 (mate 2: 512);
  - four pairs 3–13 ms;
  - the rest ≤ 1 ms.

Per-pair cost of each mate's full search (bench, native, ms):
| sample | mate 1 first (565d1e8) | cheaper mate (oracle) | by `costP` / `rareCost` estimate |
|---|---|---|---|
| NovaSeq 20k (302 pairs) | 657 | 121 | 133 |
| HiSeq 20k (174 pairs) | 687 | 35 | 42 |

## 2. Change (one commit)
`LastResort.pairsAt`: the mate whose `sbound c + 1` rarest seed buckets cost less (`costP`, per strand, worse
strand) is searched in full first; the other only near its hits (`hitsKPFN`, `keepN`).
- `pairsAt_mem` is proved for both orders: `pp_near_left` / `pp_near_right` with the existing `hitsKPFN_near`;
  `Partner` is symmetric.
- `lookAnswer` only needs membership, so `alignPairs_correct` is unchanged.
- Swapping can only reorder the pair list, so only a tie between equal-score pairs could change the reported
  pair. None did on any set measured (SAM identical).

| | 0e48158 | 565d1e8 | this branch |
|---|---|---|---|
| NovaSeq 2k Ir | 960.6M | 1754.4M | 1602.6M |
| HiSeq 2k Ir | 1309.4M | 1602.2M | 1598.7M |
| NovaSeq 20k, user s | 2.1 | 3.8 | 2.9 |
| HiSeq 20k, user s | 2.3 | 4.5 | 2.9 |
| NovaSeq 200k, user s | 16.6 | 34.7 | 26.1 |
| HiSeq 200k, user s | 20.4 | 36.0 | 26.2 |
| mason 200k, user s | — | 28.6 | 28.7 |
| low 200k, user s | — | 17.5 | 19.7 |
Native times are one warm run each (±5% noise). The 2k subsets understate the change: HiSeq 2k has no pair
where mate 1 is the expensive one; the 20k and 200k sets do.

## 3. What is left (NovaSeq 2k, 1602.6M vs 960.6M)
- second look 405M (33 calls), mostly pairs where both mates' searches find no hit: 1839 (13 / 18 ms),
  1065 (6 / 14), 1654 (4 / 12). Proving "no pair ≥ req" needs one full search there, so a bound-first exit
  cannot help. "Stop at the first pair ≥ junkScore" helps only the 6 calls that find a pair, and it would
  change the reported pair (still a valid `.unknown` answer).
- the join stage 62M, the report re-check +64M, and `decodeRead` for `reqOf` 32M (every pair). The baseline
  had none of these.
- Remaining exact levers are kernel-level (candidate-diagonal filter ~3.2k Ir per diagonal) or the join's
  budget.

## 4. Rowan's question: are the skipped big-bucket seeds actually rare? (2k subsets, 565d1e8's leftovers)
`second_look_bench … seeds` prints, per leftover pair, mate and strand, `bucket:exact` for every grid seed
(`hiB − loB` : `mzLookSP` result size) and how many seeds the pigeonhole needs (`sbound c + 1`).
- Most leftovers' seeds are rare (exact 0–30). Those pairs are cheap already: each mate's full search takes
  ≤ 1 ms.
- The expensive leftovers need 5 of 5 seeds (trimmed 125–149 bp mates have 5 grid seeds and cap 16 needs 5),
  or 5 of 6 with two repeat seeds. Their big buckets really are repetitive: bucket and exact count track each
  other (7033 : 4929, 5632 : 4451, 26120 : 21098). A few mixed buckets exist (5632 : 188, 5632 : 252), but
  never on the seeds that decide.
- Rare-only completion (look up only seeds with < 50 exact hits; a mate is settled when both strands have
  ≥ `need` rare seeds):

| | pairs covered | their cost, mate 1 first (565d1e8) | their cost, cheaper mate first (speed/second-look) | uncovered pairs' cost |
|---|---|---|---|---|
| NovaSeq | 30 / 33 | 38.7 ms | 6.3 ms | 23.6 ms (pairs 1065, 1654, 1839) |
| HiSeq | 15 / 16 | 2.5 ms | 2.4 ms | 0.8 ms (pair 1667) |
- A covered pair is one where one mate's rare seeds settle it. That mate's full second-look search is then
  already cheap, and the cheaper-mate-first change (§2) picks it. For example pair 518: mate 2 has 5 rare seeds
  of 6, and its search takes 0.5 ms. So a separate targeted completion would add nothing exact beyond §2.
- The uncovered pairs (79% of NovaSeq's remaining second-look time) have both mates with two ~4.5k-hit seeds
  among the 5 needed, so no choice of seeds avoids them. Cheaper proofs there need a finer pigeonhole: more,
  shorter or overlapping seeds, so that the ~4.5k-hit ones can be dropped. That changes the seed bound
  (`sbound`, `seedBoundE`) and its proof; it is not a lookup-order change.
