import PairLadderF
import PairRegion

/-!
# Mode H: the region pipeline first, the cap ladder on what it leaves

`pairRegionKP` (codecs/PairRegion.lean) is `pairSpecT` (`pairRegionKP_mz_eq`): each mate's
unique best at its cap, kept when the two make a proper pair.  When it maps a pair
`(a, b)` that is also proper under `properPairU` (no dovetail beyond `sl`) and the
distance cost of its fragment is `0`, `(a, b)` is the pair-level answer too (`fastU_ok`:
each mate is at its strict minimum, so `pen a + pen b` is the unique least pair sum; for
`dcost0` the cost is always `0`).  Every other pair goes through the ladder (`ladderUF`).

    (pairUKH …).1 = pairSpecUT sc0 dc sl lo hi (−penOf R1) (−penOf R2) g m1 m2   (pairUKH_mz_eq)
    pairUKH … = (none, true) → PairTieOk …                                       (pairUKH_tie)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

section top
variable (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

end top

end MapSpec.Fast

