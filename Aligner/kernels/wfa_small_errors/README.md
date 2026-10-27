# Codec `wfa_small_errors` — exact shortcut for ≤ 2 substitutions (`wfah`, `wfahc`)

**Symbols.** `wfaAlignH` (kernel `wfah`), `wfaAlignHC` (compact run-length output, kernel `wfahc`).
**Claims.** `_score`, `_sound`, `_isSome`; for `wfaAlignHC` soundness is stated for `expandCigar` of the compact
output (`wfaAlignHC_refines`).
**How.** For equal-length inputs under unit mismatch/extension penalties and non-positive gap-open, any gapped
walk costs at least two (`two_errors_optimal`), so a diagonal walk with at most two mismatches is optimal; the
scan stops at the third mismatch and everything else falls back to `wfa_offsets`.
**Files.** `AlignmentSmallErrors.lean`, `AlignmentCompact.lean`, `Certificate.lean`.
**Check.** `lake env lean alignment/codecs/wfa_small_errors/Certificate.lean`
