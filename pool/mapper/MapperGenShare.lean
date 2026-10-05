import MapperGen16

/-!
Mismatch profiles shared across window shapes.

A window `(st, len)` uses scans from the left on its start diagonal `st`
(`fwdMis … st stop 0 k`) and from the right on its end diagonal `st + len`
(`bwdMis … st len lo n k`).  Both are clamps of one scan over the whole read
(`fwdMis_min`, `bwdMis_max`), so the scans of a diagonal (`fwdProf`, `bwdProf`,
`k = 1, 2, 3`) serve every shape that starts or ends there.  The kernels with the
profiles passed in (`gappedPen2P`, `twoGapBP`, `filt16P`) are the kernels
(`gappedPen2P_eq`, `twoGapBP_eq`, `filt16P_eq`).
-/

namespace MapSpec.Fast

open MapSpec

/-- First three mismatches from the left on diagonal `st`. -/
@[inline] def fwdProf (R G : ByteArray) (st : Nat) : Nat × Nat × Nat :=
  (fwdMis R G st R.size 0 1, fwdMis R G st R.size 0 2, fwdMis R G st R.size 0 3)

/-- Last three mismatches from the right on the end diagonal `E` (read letter `x` ↔ `G[E + x − n]`). -/
@[inline] def bwdProf (R G : ByteArray) (E : Nat) : Nat × Nat × Nat :=
  (bwdMis R G E 0 0 R.size 1, bwdMis R G E 0 0 R.size 2, bwdMis R G E 0 0 R.size 3)

theorem fwdMis_min (r g : ByteArray) (st stop k : Nat) (hk : 1 ≤ k) (hs : stop ≤ r.size) :
    fwdMis r g st stop 0 k = min (fwdMis r g st r.size 0 k) stop := by
  obtain ⟨-, y2, y3⟩ := fwdMis_spec r g st stop _ 0 k rfl (Nat.zero_le _) hk
  obtain ⟨-, x2, x3⟩ := fwdMis_spec r g st r.size _ 0 k rfl (Nat.zero_le _) hk
  generalize fwdMis r g st stop 0 k = y at *
  generalize fwdMis r g st r.size 0 k = x at *
  have a := (y3 y (Nat.zero_le _) y2).1
  have b := (x3 y (Nat.zero_le _) (by omega)).1
  by_cases hx : x < stop
  · have c := (x3 x (Nat.zero_le _) x2).1
    have d := (y3 x (Nat.zero_le _) (by omega)).1
    have e1 := (y3 y (Nat.zero_le _) y2).2 (Nat.le_refl _)
    have e2 := (x3 x (Nat.zero_le _) x2).2 (Nat.le_refl _)
    have := (x3 y (Nat.zero_le _) (by omega)).2
    have := (y3 x (Nat.zero_le _) (by omega)).1
    omega
  · have e1 := (x3 stop (Nat.zero_le _) hs).2 (by omega)
    have := (y3 stop (Nat.zero_le _) (Nat.le_refl _)).2
    have := (y3 stop (Nat.zero_le _) (Nat.le_refl _)).1 e1
    omega

theorem bwdMis_max (r g : ByteArray) (st len lo k : Nat) (hk : 1 ≤ k) (hlo : lo ≤ r.size) :
    bwdMis r g st len lo r.size k = max (bwdMis r g (st + len) 0 0 r.size k) lo := by
  obtain ⟨y1, y2, y3⟩ := bwdMis_spec r g st len lo _ r.size k rfl hlo hk
  obtain ⟨-, x2, x3⟩ := bwdMis_spec r g (st + len) 0 0 _ r.size k rfl (Nat.zero_le _) hk
  simp only [Nat.add_zero] at x3
  generalize bwdMis r g st len lo r.size k = y at *
  generalize bwdMis r g (st + len) 0 0 r.size k = x at *
  by_cases hx : lo ≤ x
  · have c := (x3 x (Nat.zero_le _) x2).2 (Nat.le_refl _)
    have d := (y3 x hx x2).1 c
    have e := (y3 y y1 y2).2 (Nat.le_refl _)
    have f := (x3 y (Nat.zero_le _) y2).1 e
    omega
  · have c := (x3 lo (Nat.zero_le _) hlo).2 (by omega)
    have d := (y3 lo (Nat.le_refl _) hlo).1 c
    omega

/-- `gappedPen2` with the profiles of the start diagonal (`f1`, `f2`) and the end
diagonal (`e1`, `e2`) passed in. -/
def gappedPen2P (r g : ByteArray) (st len lim : Nat) (f1 f2 e1 e2 : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := min f1 (n - skip)
  let E1 := max e1 skip
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := min f2 (n - skip)
  let E2 := max e2 skip
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else lim + 1

theorem gappedPen2P_eq (r g : ByteArray) (st len lim : Nat) :
    gappedPen2P r g st len lim (fwdProf r g st).1 (fwdProf r g st).2.1 (bwdProf r g (st + len)).1
      (bwdProf r g (st + len)).2.1 = gappedPen2 r g st len lim := by
  unfold gappedPen2P gappedPen2 fwdProf bwdProf
  simp only []
  generalize hsk : (if len < r.size then (if len > r.size then len - r.size else r.size - len) else 0) = skip
  have hs : skip ≤ r.size := by rw [← hsk]; split <;> (try split) <;> omega
  rw [fwdMis_min r g st _ 1 (Nat.le_refl _) (Nat.sub_le _ _), fwdMis_min r g st _ 2 (by decide) (Nat.sub_le _ _),
    bwdMis_max r g st len skip 1 (Nat.le_refl _) hs, bwdMis_max r g st len skip 2 (by decide) hs]

/-- `twoGapB` with `A` and `B` passed in. -/
def twoGapBP (R G : ByteArray) (st len A B : Nat) : Bool :=
  if len = R.size + 2 then twoGapAt R G st len 1 1 A B
  else if len + 2 = R.size then twoGapAt R G st len 0 0 A B
  else if len = R.size then twoGapAt R G st len 1 0 A B || twoGapAt R G st len 0 1 A B
  else false

theorem twoGapBP_eq (R G : ByteArray) (st len : Nat) :
    twoGapBP R G st len (fwdProf R G st).1 (bwdProf R G (st + len)).1 = twoGapB R G st len := by
  unfold twoGapBP twoGapB fwdProf
  have := bwdMis_max R G st len 0 1 (Nat.le_refl _) (Nat.zero_le _)
  simp only [Nat.max_zero] at this
  simp only [bwdProf, ← this]

/-- `filt16` with `A`, `B` and the third mismatches `f3`, `e3` passed in. -/
def filt16P (R G : ByteArray) (st len A B f3 e3 : Nat) : Bool :=
  let n := R.size
  let s := skipOf n len
  (len == n && hamming R G st 4 0 n 0 == 4) ||
  (len != n && decide (gapLen n len ≤ 5) && decide (max e3 s - s ≤ min f3 (n - s))) ||
  ((len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0))

theorem filt16P_eq (R G : ByteArray) (st len : Nat) :
    filt16P R G st len (fwdProf R G st).1 (bwdProf R G (st + len)).1 (fwdProf R G st).2.2
      (bwdProf R G (st + len)).2.2 = filt16 R G st len := by
  have hs : skipOf R.size len ≤ R.size := by unfold skipOf; split <;> omega
  have h0 := bwdMis_max R G st len 0 1 (Nat.le_refl _) (Nat.zero_le _)
  simp only [Nat.max_zero] at h0
  unfold filt16P filt16 fwdProf bwdProf
  simp only []
  rw [fwdMis_min R G st _ 3 (by decide) (Nat.sub_le _ _), bwdMis_max R G st len _ 3 (by decide) hs, h0]

end MapSpec.Fast
