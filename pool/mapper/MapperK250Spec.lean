import MapperK250
import MapperGenScore

/-!
# `gappedPen3` and `kerG3` (byte level)

`gappedPen3` is `gappedPen2` with a third level (two mismatches around the gap):
the one-gap formula capped at `lim + 1` for `lim ≤ 17` (`gappedPen3_spec`).  Hence
`kerG3` is the window formula `fB` capped at `lim + 1` (`kerG3_eq`), and `kerG` for
`lim ≤ 15` (`kerG3_kerG`).
-/

namespace MapSpec.Fast

open MapSpec

theorem gappedPen3_spec (R G : ByteArray) (st len lim : Nat) (hne : len ≠ R.size) (hlim : lim ≤ 17) :
    gappedPen3 R G st len lim = min (6 + 2 * gapLen R.size len + 4 * minMis R G st len) (lim + 1) := by
  sorry

theorem kerG3_eq (R G : ByteArray) (st len lim : Nat) (hlim : lim ≤ 17) :
    kerG3 R G st len lim = if st + len ≤ G.size then min (fB R G st len) (lim + 1) else lim + 1 := by
  sorry

theorem kerG3_kerG (R G : ByteArray) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerG3 R G st len lim = kerG R G st len lim := by
  rw [kerG3_eq R G st len lim (by omega), kerG_eq R G st len lim hlim]

end MapSpec.Fast
