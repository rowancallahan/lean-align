# fine-filter: the second look's word filter (branch `speed/fine-filter`, off festive-fermi 1034f63)

Ir = callgrind of the shim on the first 2000 pairs. SAM byte-identical to 1034f63 on the four full 200k sets and
both 2k subsets; `CI_check.sh` passes; exact `@[csimp]` rewrites (`FastGenWordFilt.lean`).

| | NovaSeq | HiSeq | NovaSeq `fineE` + `lanesAny*` |
|---|---|---|---|
| 1034f63 | 1585.7M | 1618.8M | 133.0M (`fineE` self 41.7M, `lanesAnyV` 91.2M) |
| `lanesAnyV_eqW` | 1579.3M | 1618.0M | `lanesAnyW` 83.3M |
| + `fineE_eqC` | 1565.5M (−1.3%) | 1614.3M (−0.3%) | `fineEV` 26.4M + `lanesAnyW` 83.3M = 109.7M |
- `lanesAnyV_eqW`: the shift scan keeps the two window words of `gAtWU` while the word index `(t >>> 5) + jU`
  is unchanged. It re-reads them (`GW.getU`, a branch tree) only when the index moves. The proof is a plain
  case split, no arithmetic (`lanesAnyW_eq`).
- `fineE_eqC`: under one bound check (`o + 2r + 1 + 32(j + k) < 2^31`) the loop uses `gAtWU`, a precomputed
  field mask and `lanesAnyV` directly (`fineEV_eq`: `gAtWU_eq`, `lowF_eqM`, `lanesAny_eq_lanesAnyF`). Otherwise
  it runs a verbatim copy (`fineES`).
Native user CPU, 200k, one run each, within noise: NovaSeq 24.9 → 24.3 s, HiSeq 23.9 → 26.6 s.

## What is left
`lanesAnyW` is now ~45 machine instructions per shift step: 1.87M steps over 93k calls on NovaSeq 2k. The cost is
the algorithm: each 8-letter lane of a read word is compared with the genome at each of `2r + 1` shifts until all
lanes match. Cutting it needs a different filter, e.g. a q-gram or 8-mer set of the window built once per
diagonal and probed per lane, with its own proof. `fineEV` keeps `Nat` counters (~190 Ir per word); a
`USize` loop would save perhaps another 10–15M. `suppA` is 8M.
