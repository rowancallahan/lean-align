# Codec `wfa` — the proven wavefront algorithm (WFA)

**Symbol.** `wfaAlign` (runner kernel `wfa`).
**Claims (three theorems).** `wfaAlign_score`: the returned score equals the frozen optimum;
`wfaAlign_sound`: any returned walk is a valid alignment carrying its true score; `wfaAlign_isSome`: a result
is always returned.  Outside the runtime gate `wfaGateB` (scoring not reasonable) it falls back to `gotoh`.
**How.** Forward wavefront over penalty levels with furthest-reaching cells (Marco-Sola et al. 2021, WFA);
`AlignmentExchange.lean` proves the free-extension lemma at the spec level; `AlignmentWfa.lean` proves
soundness + completeness of the levels and optimality of the loop (`wfaLoop_opt`), then banded (`wfaRunT_eq`)
and array (`wfaRunA_eq`) refinements.  Every faster codec below is proven against `wfaAlign`.
**Files.** `AlignmentExchange.lean`, `AlignmentWfa.lean` (~5100 lines), `Certificate.lean`.
**Check.** `lake env lean alignment/codecs/wfa/Certificate.lean`
