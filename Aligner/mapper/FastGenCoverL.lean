import FastGenCover

/-!
`cover` for any lookup length `l` (`MatchAtL`: `l` letters match), for seeds
shorter than the index's 25 letters.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- `l` letters of `R` from `s` occur in `G` at `p`. -/
def MatchAtL (G : ByteArray) (p : Nat) (R : ByteArray) (s l : Nat) : Prop :=
  p + l ≤ G.size ∧ ∀ k, k < l → G.get! (p + k) = R.get! (s + k)

end MapSpec.Fast

