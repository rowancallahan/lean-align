import PairJoint
import MapperInterleave

/-!
# Codec `pairFastI`: both strands interleaved, one lookup at a time

As `pairFastJ` (codecs/PairJoint.lean: the reverse strand is the virtual
chromosome `n + c`, one shared `Best`), but on each chromosome the two strands'
seed lookups are interleaved (`ilLoop`, pool/mapper/MapperInterleave.lean): the
next lookup goes to the strand with fewer lookups, then the smaller bucket, as
the prototype's `mapStreams` (bench/Proto.lean).  A strand stops once the shared
best is below `4·(its lookups)`, so a good hit on either strand stops the other
early whichever strand is searched first.  Against the DRAFT spec
`spec/PairSpec.lean`; fast path (`fastOk`), sc0, T = −12.

    … → mapFastI lk gbs idxs R = mapSpecBoth sc0 (-12) g read              (mapFastI_eq_mapSpecBoth)
    … → pairFastI lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastI_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-! ## Proofs -/

end MapSpec.Fast

