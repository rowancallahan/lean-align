# n39: HiSeq, the items after n38 (branch `speed/n39`, 2026-11-03): nothing kept

Base 0e48158 (n38 + shim patch file): HiSeq (hg002 2×250, 2000 pairs) 1309.4M Ir. Each item below was measured
(callgrind, instruction-level where noted) or prototyped; none is worth a change plus its proof.

| item | HiSeq share | finding |
|---|---|---|
| `bandCellsJ` (banded DP; fallback + `alignAt`) | 4.7% | Instruction profile: stack loads 9.0M + stores 6.1M of 61.8M (25%), branches 15%, the rest the cell's arithmetic and the `Array UInt32` set / bounds / exclusivity checks. Prototype `bandCellsJC` (the seven loop constants `X W K c0s m lim n` in one structure, fewer live arguments; differential test equal, SAM identical): **61.8M → 74.9M, worse** (field loads per use cost more than the spills). n36's `uget` / carried-letter variant gave −4.7% of the DP (−0.25% total). The DP's per-cell cost is the compiled loop; `bandCellsJ` is also proved now (`BandCellsJProof.lean`), so any variant needs its own `_eq`. |
| `prepLoop` (seed preparation) | 2.6% | ~485 instructions per seed (69k seeds), compute-bound: 21 multiplies per seed (20 minimizer candidates of `mini20` + the seed hash), no out-of-line calls besides the `Array.push`. Nothing to remove without changing the minimizer scheme. |
| router kernels (`svAnyU`, `scanAWF`, `stageKSPN`, `ker16KWG`, `hamWU`, `unlookV`) | ~1.4–2.4% each | No `Nat` runtime calls (`lean_nat_shiftr` / `mod` / `div`, GMP literals) remain in any hot path after n37 (checked all callers): they are machine-word loops already (n32). |
| allocation / free | ~9% (`lean_dec_ref_cold` 3.1%, `mi_free` 2.3%, `lean_del_core_other` 2.0%, alloc 1.6%) | The largest single site is the end of each pair in `alignOneP` (16.3M; 43.6k frees, ~375 Ir each): the preparations' `Array MzP` (5 boxed fields each) and the packed reads' `RP.w : Array UInt64` (every word a boxed object). Making `RP.w` unboxed (a `ByteArray` of words) would touch every k250 kernel and its proofs. |

What is left that is worth doing on HiSeq is outside these: the frozen shim (`Testing/notes/shim_speed.patch`,
−9.7% HiSeq measured at 562a2f5) and `fallbackOf` (S-B).
