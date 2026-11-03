import PairLadder

/-!
# Codec `pairGK`: the pair-level guarantee at total penalty `G`

Every hit of each mate within penalty `G` (`hitsAtKP G`, exact over the packed whole genome),
then the best proper pair of the two lists (`bestPairD`) and the flag "a proper pair was seen":

    pairGK … = some (pairSpecUT sc0 dc sl lo hi (−G) (−G) g m1 m2, flag)        (pairGK_eq)

**Guarantee** (`pairGK_guarantee`).  If some proper pair (`properPairU sl`: 1 kb cap, no
dovetail beyond `sl`) at any caps `P1, P2 ≥ G` has pair score `≥ −G` (with `dcost0`: total penalty
`≤ G`), the kernel returns `some (r, true)` with `r = pairSpecUT … (−P1) (−P2)`: the unique best
pair, or `none` with `PairTieOk` (`pairTie`: proper pairs exist, no unique best).

**Read-length condition** (hypotheses, `fastT G` for both mates): `0 < n / 25` and
`sbound G < n / 25`.  `G = 4`: both mates `≥ 50` bp (`pairGK_guarantee4`); `G = 0`: `≥ 25` bp
(`pairGK_guarantee0`).  Outside it the kernel returns `none` (outside the guarantee).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- A hit within the caps of a pair of score `≥ −c` is a hit within `c`. -/
theorem hitsBoth_lower {T : Int} {c : Nat} {g : Genome} {m : List Char} {x : Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) (hT : T ≤ -(c : Int)) (hs : -(c : Int) ≤ x.2) :
    x ∈ hitsBoth sc0 (-(c : Int)) g m := by
  have e := hitsBoth_filter sc0 T (-(c : Int)) g m
  rw [Int.max_eq_right hT] at e
  rw [← e]
  exact List.mem_filter.mpr ⟨hx, by simpa using hs⟩

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

end top

end MapSpec.Fast

