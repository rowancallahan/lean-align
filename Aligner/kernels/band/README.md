# Codec `band` — banded DP with band doubling

**Symbol.** `bandDoublingAlign` (runner kernel `band`).
**Claim.** Full equality with the frozen specification: `bandDoublingAlign sc xs ys = getBestAlignment sc xs ys`.
**How.** Runs the DP inside a diagonal band; the off-band bound (`two_score_le_offBandBound`) certifies when
the banded optimum is the global one, otherwise the band doubles.
**Files.** `AlignmentWavefront.lean`, `Certificate.lean`.
**Check.** `lake env lean alignment/codecs/band/Certificate.lean`
