# Notes for whoever (or whatever) picks this up next

Written 2026-09-11 during the session that built the third kernel (`wfau3`).
Placeholder prose; Rowan rewrites anything public.  Facts first, ideas after.

## TODO: separate proved kernel for long sequences

Requested by Rowan after the final U3 comparison (2026-09-11).

- [ ] Develop a separate long-sequence kernel and dispatch to it above a
  measured length threshold. Keep the exact 1–2-substitution shortcut first,
  so long, nearly identical inputs still use that cheap path.
- [ ] Measure the crossover against U3 on longer pairs (including 100 kb,
  500 kb and 1 Mb), several divergence rates and unequal lengths. Record
  runtime, memory and dispatch/setup overhead. Define which input-length
  measure controls dispatch; choose the threshold from data, not a guess.
- [ ] Evaluate an A*PA2-inspired bit-parallel/seed-guided unit-cost kernel;
  consider affine support separately, retaining the proved U3 fallback.
  Reference: [A*PA2, WABI 2024](https://doi.org/10.4230/LIPIcs.WABI.2024.17).
- [ ] Prove the new executable kernel's optimal score, traceback validity
  and totality, then prove the combined shortcut/length-dispatch/fallback
  wrapper against the unchanged specification for all inputs and scoring.
- [ ] Admit it to verified plots only after the complete proof and audit;
  repeat comparisons on identical inputs with traceback and any extra
  packing/index construction included consistently in the timed work.

This is a TODO, not an implemented dispatch or a chosen threshold. The U3
proof below is now complete (source checkpoint 487206e).

## Two findings that were worth a day

1. **Cross-translation-unit calls are not inlined.**  Lean compiles every
   module to its own C file.  The LCP loop `lcpU` (AlignmentWfaU32Fill.lean)
   is called from the free-extension step of every cell; when the cell loop
   lived in a different module the call was a real call (clang cannot inline
   across `.c` files), and the general path was ~35 % slower (10 kb, 5 %,
   affine: 5.4 ms vs 4.0 ms per pair) with byte-for-byte identical Lean.
   All three cell loops (`uFillGo2`, `uFillS`, `uFillGo3`) now live in
   AlignmentWfaU32Fill.lean next to `lcpU`.  Rule: a hot callee and its
   caller go in the same file.  Diagnose with `.lake/build/ir/<Module>.c`.
2. **Nat literals above 2^32 are parsed from a string at runtime.**  The
   compiler emits `lean_cstr_to_nat("4294967296")` for `2 ^ 32` and
   `UInt32.size`; a `Decidable` instance for a Prop with six such bounds paid
   about a microsecond per level.  `lt32 a := a >>> 32 == 0` (with
   `lt32_iff`) is the scalar form; the once-per-level checks are now Bool
   functions (`levelCheckB`, `levelCheckSB`, `levelCheckB3`) with a lemma
   `…_true` giving the Prop the proofs use.  Rule: grep the generated C for
   `cstr_to_nat` after touching anything per-level.

Things that measured as noise at 10 kb 5 % affine: branchless max
(`ubetterC`), wrapping instead of saturating `ujoff`, one block array per
level instead of three (the block layout helps only through the array
history and one allocation per level, ~10 % at 1 kb).

## Where things stand

- `wfau3` (`wfaAlignU3`): general path = probe-combo's block layout with
  array history and the run-wide zero array; single-source path shared with
  `wfau2`.  Within ~5 % of probe-combo on the affine cases, faster on the
  unit cases.  Proof files: AlignmentWfaU32FillSpec3 (loop spec),
  AlignmentWfaU32Loop3 (view/history bookkeeping), AlignmentWfaU32Level3
  (`uLevel3_some`: a returned level views to `uLevel` of the views),
  AlignmentWfaU32Kernel3 (loop, run, kernel theorems).
- Profilers: macOS `sample` captured nothing; Xcode/`xctrace` not installed.
  `lean_exe stage_probe` (alignment/probes/StageProbe.lean) times the forward
  run and the full kernel separately; ablation builds plus the generated C
  are the working tools.

## Ideas, roughly in the order I would try them

1. **Word-parallel free extension.**  WFA2-lib compares 8 bytes at a time in
   `wavefront_extend`.  In Lean: once per pair pack both sequences into
   `ByteArray` (fallback when a character is ≥ 256), then `lcp` by XOR of
   `UInt64` words and a trailing-zero count (`x &&& (0 - x)` isolates the
   lowest bit; `Nat.log2` is an extern).  Proof: `lcpArr = lcpBytes` by
   induction on words.  Measure the extension share first (stub `lcpU` to
   return immediately in a scratch build; results are wrong, timing is
   right).  Pays most at low error rates (long matches).
2. **Skip source reads that the invariant makes redundant.**  With
   `pe = px` the X source of level `L` at diagonal `t-1` and the D source at
   `t` come from the same level; nothing to merge there.  But with the
   invariant `X ≤ M` per level (AlignmentWfaU32Single.lean) the `xe` read
   (X front of level `L - pe`) is bounded by the M front of the same level
   read at the same index: when `pe = po` the two X candidates collapse to
   one read of M at `t - 1` of level `L - pe`.  Only helps cost models with
   `pe = po`, which pa-bench's do not use.
3. **Traceback reads through `hist.getD` into boxed structs**: cache
   `lo/w/blk` per level once per step.  Small, high error rates only.
4. **BiWFA-style two pass** (score with a ring of `max pe po px + 1`
   levels, then divide-and-conquer traceback): halves memory traffic and
   removes the per-level allocation, at the cost of a second proof layer.
5. **Do not re-chase the primitives** (see the noise list above).
