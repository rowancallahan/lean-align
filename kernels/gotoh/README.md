# Codec `gotoh` — Gotoh / Bellman dynamic programming

**Symbols.** `gotohFusedAlign` (runner kernel `gotoh`); also `gotohAlign`, `bellmanAlign`.
**Claim.** Full equality with the frozen specification: `gotohFusedAlign sc xs ys = getBestAlignment sc xs ys`
for every scoring and every pair of strings (walk and score, including the tie rule).
**Files.** `AlignmentAlgorithms.lean` (definitions + proofs), `Certificate.lean` (generated; restates the
exported theorem, prints axioms of the whole chain).
**Cost.** O(m·n) time and memory; the slowest proven codec, used as the exact fallback by others.
**Check.** `lake env lean alignment/codecs/gotoh/Certificate.lean`
