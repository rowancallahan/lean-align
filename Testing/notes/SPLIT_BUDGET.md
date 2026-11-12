# Budget split in the second look (`speed/split-budget`, off festive-fermi b8bae7e; SEARCH_IDEAS #1)

`LastResort.pairsAtS` (`lookAt` now calls it):
- `splitOf` picks a split `a < c` per pair. Its cost is `costP a` (mate 1) + `costP (c-a-1)` (mate 2), the summed
  rarest-bucket sizes, against today's `min (costP c)`. If no split is cheaper, `a = c` and today's `pairsAt` runs.
- `splitEmpty`: mate 1 is searched in full at cap `a` with mate 2 near its hits at cap `c`, then mate 2 in full at
  cap `c - a - 1` with mate 1 near its hits at cap `c`. Only pairs scoring `≥ -c` count.
- If nothing is found, the answer is `[]`, and today's search finds nothing too. Otherwise today's `pairsAt` runs,
  so the list is identical.

Proof (Proofs/LastResort.lean):
- `splitEmpty_none`: a pair `p` of hits within `c` scoring `≥ -c` has `s1 + s2 ≥ -c`, so `s1 ≥ -a` or
  `s2 ≥ -(c-a-1)`. The case's full search lists that mate's hit (`hitsKPF_mem` at the lower cap). The near search
  lists the partner (`hitsKPFN_near` with `pp_near_right` / `pp_near_left`). So the part's `any` is true,
  which contradicts `splitEmpty = true`.
- `pairsAtS_mem`: the same statement as `pairsAt_mem`. `alignPairs_correct` is unchanged.

| | b8bae7e | this branch |
|---|---|---|
| NovaSeq 2k Ir | 1218.9M | 1172.4M (−46.6M, −3.8%) |
| HiSeq 2k Ir | 1425.1M | 1424.5M (−0.04%) |
- SAM is byte-identical on both 2k subsets and on the full NovaSeq and HiSeq 200k sets.
- CI with FUZZ=1 passes: 457 theorems, standard axioms only.
- HiSeq's second look is small here (52M of ~1430M), so there is little to gain.
- Native user CPU, one run each: NovaSeq 20.9 → 21.2 s, HiSeq 24.6 → 22.8 s (noise ±1 s; wall includes a cold index load).

Where the second look goes after the split (NovaSeq 2k, prototype profile):
- near searches 67M (kernels on kept diagonals 46M, lookups + slices ~14M)
- full searches 42M
- the re-run of `pairsAt` on calls that find a pair 64M

## Follow-ups
- Avoid re-running `pairsAt` when the split finds pairs (~64M, up to ~4% NovaSeq). The split's lists hold the
  same pairs in a different order. This needs either today's order rebuilt from them, or a proof that
  `lookAnswer`'s choice (`topW` among tied top pairs) does not depend on list order.
- SEARCH_IDEAS #2 (region lookups for the partner): at most ~14M (~1.1%), since the near search's cost is kernels.
  Skipped.
- The same split for the join (`noPairJS`, stage 3): not done.
