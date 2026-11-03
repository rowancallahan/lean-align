import PairMapper
import FastMapperMz

/-!
# Codec `pairFastJ`: joint strand search (one shared `Best`) and proper pairs

Both strands share ONE `Best`: the reverse strand is searched as extra virtual
chromosomes `n + c` (same genome bytes, read = reverse complement).  The proved
per-chromosome step `mapChrom2_inv` uses the chromosome index only as a tag and
its stop test compares against the shared best, so once one strand has a good
hit the other stops after few lookups.  The same window on the two strands is
two different virtual windows, so a tie is ambiguous (unmapped), as
`mapSpecBoth` requires.  Against the DRAFT spec `spec/PairSpec.lean`; fast path
(`fastOk`), sc0, T = −12.

    … → mapFastJ lk gbs idxs R = mapSpecBoth sc0 (-12) g read              (mapFastJ_eq_mapSpecBoth)
    … → pairFastJ lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastJ_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-! ## Penalties -/

/-! ## Lemmas -/

/-! ## Top theorems (from the lemmas) -/

end MapSpec.Fast

