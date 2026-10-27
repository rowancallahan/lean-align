# Codec `wfa_fast` — executed-path variants of `wfaAlign` (`wfai`, `wfaf`, `wfal`)

**Symbols.** `wfaAlignI` (inlined helpers), `wfaAlignF` (fused level), `wfaAlignL` (fused level + lazy
candidate selection + no-alloc extend) — runner kernels `wfai`, `wfaf`, `wfal`.
**Claim.** Function equality with the proven kernel: `wfaAlign? sc xs ys = wfaAlign sc xs ys` (`wfaAlignI_eq`,
`wfaAlignF_eq`, `wfaAlignL_eq`), so the three `wfa` theorems transfer by rewriting.
**How.** Same list-of-cells representation as `wfa`; fewer passes and allocations per level
(`nextLevelF_eq`, `nextLevelL_eq`).  Superseded in speed by `wfa_offsets`/`wfa_runs`.
**Files.** `AlignmentWfaFused.lean`, `AlignmentWfaLazy.lean`, `AlignmentWfaLazyLevel.lean`,
`AlignmentWfaFast.lean`, `Certificate.lean`.
**Check.** `lake env lean alignment/codecs/wfa_fast/Certificate.lean`
