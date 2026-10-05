import MapperK250Chunk
import MapperK250Sel
import MapperFastKernel

/-!
# Word loops = byte loops

`hamA_eq` (`hamming`), `fwdA_eq` / `fwdK_eq` (`fwdMis`), `bwdA_eq` / `bwdK_eq` (`bwdMis`)
on read letters whose genome letters lie in flagged blocks (`WOk`, `WOkB`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- Word path conditions for read letters `[0, stop)` against the genome at `st + ·`. -/
def WOk (R G : ByteArray) (P : PGen) (st stop : Nat) : Prop :=
  Rep P G ∧ (packRP R).ok = true ∧ stop ≤ R.size ∧ st + stop ≤ P.n ∧
    ∀ x, x < stop → P.w.get! (17 * ((P.o + st + x) / 64)) = 1

theorem hamA_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (lim : Nat) :
    hamA (packRP R).w P.w (P.o + st) lim stop = hamming R G st lim 0 stop 0 := by
  sorry

theorem fwdA_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (k : Nat) (hk : 1 ≤ k) :
    fwdA (packRP R).w P.w (P.o + st) stop k = fwdMis R G st stop 0 k := by
  sorry

/-- Read letters `[lo, n)` against the genome at `d + ·` (the end diagonal). -/
def WOkB (R G : ByteArray) (P : PGen) (d lo : Nat) : Prop :=
  Rep P G ∧ (packRP R).ok = true ∧ d + R.size ≤ P.n ∧
    ∀ x, lo ≤ x → x < R.size → P.w.get! (17 * ((P.o + d + x) / 64)) = 1

theorem bwdA_eq (R G : ByteArray) (P : PGen) (st len lo : Nat) (hd : R.size ≤ st + len)
    (h : WOkB R G P (st + len - R.size) lo) (k : Nat) (hk : 1 ≤ k) :
    bwdA (packRP R).w P.w (P.o + (st + len - R.size)) lo R.size k = bwdMis R G st len lo R.size k := by
  sorry

theorem fwdK_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (k : Nat) (hk : 1 ≤ k) :
    fwdK R G (packRP R).w P.w (P.o + st) st stop k = fwdMis R G st stop 0 k := by
  sorry

theorem bwdK_eq (R G : ByteArray) (P : PGen) (st len lo : Nat) (hd : R.size ≤ st + len)
    (h : WOkB R G P (st + len - R.size) lo) (k : Nat) (hk : 1 ≤ k) :
    bwdK R G (packRP R).w P.w (P.o + (st + len - R.size)) st len lo k = bwdMis R G st len lo R.size k := by
  sorry

end MapSpec.Fast
