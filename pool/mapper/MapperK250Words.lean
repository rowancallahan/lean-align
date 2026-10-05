import MapperK250Loops
import MapperK250Spec

/-!
# Word kernels = byte kernels

Under `Rep P G` (the packed genome spells `G`), a packed read that passed its check
(`(packRP R).ok`), and a window inside flagged (pure ACGT) blocks, each word scan
equals the byte loop it replaces: `hamA_eq` (`hamming`), `fwdA_eq` / `fwdK_eq`
(`fwdMis`), `bwdA_eq` / `bwdK_eq` (`bwdMis`), `gappedW_eq` (`gappedPen3`),
and the kernel `kerGK_eq` (`kerG3`, with no hypothesis but `Rep`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

theorem gappedW_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat)
    (hw : wordOk R (packRP R) P st len = true) (hne : len ≠ R.size) :
    gappedW R G (packRP R).w P.w P.o st len lim = gappedPen3 R G st len lim := by
  sorry

/-- **The word kernel is `kerG3`.** -/
theorem kerGK_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) :
    kerGK R (packRP R) G P st len lim = kerG3 R G st len lim := by
  sorry

/-- **The word kernel is `kerG`** (`lim ≤ 15`). -/
theorem kerGK_kerG (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerGK R (packRP R) G P st len lim = kerG R G st len lim := by
  rw [kerGK_eq R G P hP, kerG3_kerG R G st len lim hlim]

end MapSpec.Fast

#print axioms MapSpec.Fast.kerGK_eq
#print axioms MapSpec.Fast.kerGK_kerG
