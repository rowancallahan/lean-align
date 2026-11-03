# join arrays (`speed/join`, off festive-fermi 050ef82)

`joinAt` → `tierNo` → `noPairJS` (leftovers only: 56 calls on NovaSeq 2k, 59M Ir):
- 668 seed lookups: 32.5M
- `List.merge` of the place lists (`anchSel`): 13M, plus the frees

Two exact `@[csimp]` rewrites in Aligner/mapper/PairJoin.lean:
- `noPairJS_eqL` (a plain lemma): when one strand's anchors are empty, the other mate's opposite-strand lookups
  are skipped (`nearAnyF` on `[]` is false).
- `noPairJS_eqA` (the csimp, via `noPairJS_eqL`): anchors merged as arrays (`mergeA`, `mergeA_toList`: equal to
  `List.merge`), and the near test runs over the arrays (`nearGo_eq`: equal to `nearAnyF`).

| | 050ef82 | this branch |
|---|---|---|
| NovaSeq 2k Ir | 1240.1M | 1223.4M (−16.7M, −1.35%) |
| HiSeq 2k Ir | 1433.1M | 1429.7M (−3.5M, −0.24%) |
- SAM is byte-identical on both 2k subsets and on the full NovaSeq and HiSeq 200k sets (400,000 records each).
- CI with FUZZ=1 passes: 455 theorems, standard axioms only.
- The empty-strand skip alone gave −2.8M on NovaSeq. On these repetitive leftovers both strands usually have
  anchors, so most of the gain comes from the arrays.
