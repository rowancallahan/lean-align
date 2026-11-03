# lookat slices (`speed/lookat`, off festive-fermi 6ef8212)

Change: `hitsSK_eqV` (Aligner/mapper/PairHitsKP.lean) is an exact `@[csimp]` rewrite. The full hit search (the
second look's first mate, `hitsKPF`) used to slice every seed's anchors for every one of the 2 × 195 strand
chromosomes, with 2 binary searches per seed per chromosome. When every anchor array is strictly increasing
(`incB`) and the chromosome table is in order (`layoutOk`: `offs.size = n`, increasing, gaps), each anchor marks
the one chromosome a single binary search over `offs` finds (`chromOfA_eq`). Unmarked chromosomes have only empty
slices (`slices_empty`, via `mem_lb_extract`), so `hitsCK` returns `[]` there. If a check fails, the original loop runs.

| | 6ef8212 | this branch |
|---|---|---|
| NovaSeq 2k Ir | 1257.5M | 1239.9M (−17.6M, −1.4%) |
| HiSeq 2k Ir | 1446.3M | 1433.1M (−13.2M, −0.9%) |
- SAM is byte-identical on both 2k subsets and on the full NovaSeq and HiSeq 200k sets (heavy.idx).
- CI with FUZZ=1 passes: 454 theorems, standard axioms only.
- Native user CPU on 200k (one run each): NovaSeq 21.8 → 22.1 s, HiSeq 23.3 → 23.4 s. That is within noise, as
  expected for −1%.

## Router (tierPairBQ, NovaSeq 2k, ~263M; the same at 0e48158, so not part of the floor's gap)
- `mateKPPO` 184M:
  - index lookups `mzLookSP` → `scanAWK3` / `scanAWF`: ~88M (minimizer bucket scans)
  - kernel staging `chromKBFGK` → `stageKSPN`: ~67M
  - `foldUpN` folds, `suppCntC`: 11M; `diagsM`: 11M
- `tierRestS` / `tierB`: ~21M
No cheap exact lever: the cost is the lookups and kernels themselves. Bucket scans would need an index layout change
(e.g. entries sorted by key within a bucket, so that a bucket can be binary-searched), with the builder and checker
proofs redone.
