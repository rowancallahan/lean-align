import AlignmentWfaView

/-! Pointwise wavefront recurrences with exactly the same stored bands.
The view algebra determines bounds only; each output entry uses direct
absolute-diagonal lookups. -/
namespace AlignmentSpec

theorem decodeR_injective : Function.Injective decodeR := by
  intro a b h
  cases a <;> cases b <;> simp_all [decodeR]

theorem rget_zipR (f g : RFront) (t : Nat) :
    rget (zipR f g) t = betterR (rget f t) (rget g t) := by
  apply decodeR_injective
  rw [decodeR_rget, rtob_zipR, decodeR_betterR, decodeR_rget, decodeR_rget]
  have h := congrArg (fun l => l[t]?) (bden_zipB (t + 1) (rtob f) (rtob g))
  simp only [List.getElem?_zipWith, bget_den (t + 1) t _ (by omega)] at h
  exact Option.some.inj h

theorem rget_mapR (g : Nat → Nat → Nat) (hz : ∀ t, g t 0 = 0)
    (f : RFront) (t : Nat) : rget (mapR g f) t = g t (rget f t) := by
  by_cases ht : t < f.lo
  · simp [rget, mapR, ht, hz]
  · have he : f.lo + (t - f.lo) = t := by omega
    simp only [rget, mapR, ht, if_false, Array.getElem?_mapIdx, he]
    cases f.body[t - f.lo]? <;> simp [hz]

theorem rget_shiftUpR (f : RFront) (t : Nat) :
    rget (shiftUpR f) t = if t = 0 then 0 else rget f (t - 1) := by
  cases t with
  | zero => simp [rget, shiftUpR]
  | succ t =>
    simp only [rget, shiftUpR, Nat.add_lt_add_iff_right, Nat.add_sub_add_right,
      Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]

theorem rget_shiftDownR (len : Nat) (f : RFront) (t : Nat) :
    rget (shiftDownR len f) t = if t + 1 < len then rget f (t + 1) else 0 := by
  cases f with
  | mk lo body =>
    cases lo with
    | zero =>
      simp only [shiftDownR, rget, Nat.not_lt_zero, if_false, Nat.sub_zero,
        Array.getElem?_extract]
      by_cases ht : t + 1 < len
      · simp only [ht, if_true]
        by_cases hb : t + 1 < body.size
        · rw [if_pos (by omega)]
          congr 2; omega
        · rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]
      · rw [if_neg ht, if_neg (by omega)]
        rfl
    | succ p =>
      simp only [shiftDownR]
      split
      · rename_i hb
        simp only [rget]
        by_cases ht : t + 1 < len
        · simp [ht, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
        · rw [if_neg ht]
          by_cases hp : t < p
          · simp [hp]
          · rw [if_neg hp, Array.getElem?_eq_none (by omega)]; rfl
      · simp only [rget, Array.getElem?_extract, Nat.zero_add, Nat.sub_zero]
        by_cases ht : t + 1 < len <;> by_cases hp : t < p
        · simp [ht, hp, show t + 1 < p + 1 from by omega]
        · simp only [ht, hp, if_true, if_false,
            show ¬t + 1 < p + 1 from by omega, Nat.add_sub_add_right]
          by_cases hb : t - p < body.size
          · rw [if_pos (by omega)]
          · rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]
        · simp [ht, hp]
        · simp only [ht, hp, if_false]
          rw [if_neg (by omega)]; rfl

@[macro_inline] def packPoint (v : VFront) (g : Nat → Nat) : RFront :=
  ⟨v.lo, arrayBuild (fun i : Fin v.body.size => g (v.lo + i.val))⟩

theorem packPoint_eq (v : VFront) (g : Nat → Nat)
    (h : ∀ t, g t = rget (packV v) t) : packPoint v g = packV v := by
  unfold packPoint packV
  congr 1
  apply Array.ext
  · simp [arrayBuild_eq]
  · intro i h1 h2
    have hi : i < v.body.size := by simpa using h2
    simp only [arrayBuild_eq, Array.getElem_ofFn, materialize_get]
    rw [h]
    simp only [rget, packV, Nat.not_lt.mpr (Nat.le_add_right v.lo i), if_false,
      Nat.add_sub_cancel_left]
    rw [Array.getElem?_eq_getElem h2]
    simp

@[inline] def pointX (m n : Nat) (xe xo : RFront) (t : Nat) : Nat :=
  if t = 0 then 0 else
    betterR (pushXR m n (t - 1) (rget xe (t - 1)))
      (pushXR m n (t - 1) (rget xo (t - 1)))

@[inline] def pointY (m n len : Nat) (ye yo : RFront) (t : Nat) : Nat :=
  if t + 1 < len then
    betterR (pushYR m n (t + 1) (rget ye (t + 1)))
      (pushYR m n (t + 1) (rget yo (t + 1))) else 0

@[inline] def pointM (m n : Nat) (xa ya : Array Char)
    (dm xf yf : RFront) (t : Nat) : Nat :=
  extR m xa ya t (betterR (betterR (pushDR m n t (rget dm t)) (rget xf t)) (rget yf t))

@[macro_inline] def pointXView (m n : Nat) (xe xo : RFront) : VFront :=
  zipV (shiftUpV (mapV (pushXR m n) (viewR xe)))
    (shiftUpV (mapV (pushXR m n) (viewR xo)))

@[macro_inline] def pointYView (m n len : Nat) (ye yo : RFront) : VFront :=
  zipV (shiftDownV len (mapV (pushYR m n) (viewR ye)))
    (shiftDownV len (mapV (pushYR m n) (viewR yo)))

@[macro_inline] def pointMView (m n : Nat) (xa ya : Array Char)
    (dm xf yf : RFront) : VFront :=
  mapV (extR m xa ya)
    (zipV (zipV (mapV (pushDR m n) (viewR dm)) (viewR xf)) (viewR yf))

theorem pointX_eq (m n : Nat) (xe xo : RFront) (t : Nat) :
    pointX m n xe xo t = rget (packV (pointXView m n xe xo)) t := by
  simp only [pointXView, packV_zipV, packV_shiftUpV, packV_mapV, packV_viewR,
    rget_zipR, rget_shiftUpR, rget_mapR (pushXR m n) (fun _ => rfl)]
  by_cases h : t = 0 <;> simp [pointX, h, betterR]

theorem pointY_eq (m n len : Nat) (ye yo : RFront) (t : Nat) :
    pointY m n len ye yo t = rget (packV (pointYView m n len ye yo)) t := by
  simp only [pointYView, packV_zipV, packV_shiftDownV, packV_mapV, packV_viewR,
    rget_zipR, rget_shiftDownR, rget_mapR (pushYR m n) (fun _ => rfl)]
  by_cases h : t + 1 < len <;> simp [pointY, h, betterR]

theorem pointM_eq (m n : Nat) (xa ya : Array Char) (dm xf yf : RFront) (t : Nat) :
    pointM m n xa ya dm xf yf t = rget (packV (pointMView m n xa ya dm xf yf)) t := by
  simp only [pointMView, packV_mapV, packV_zipV, packV_viewR,
    rget_mapR (extR m xa ya) (fun _ => rfl), rget_zipR,
    rget_mapR (pushDR m n) (fun _ => rfl), pointM]

theorem packPointX_eq (m n : Nat) (xe xo : RFront) :
    packPoint (pointXView m n xe xo) (pointX m n xe xo) = packV (pointXView m n xe xo) :=
  packPoint_eq _ _ (pointX_eq m n xe xo)

theorem packPointY_eq (m n len : Nat) (ye yo : RFront) :
    packPoint (pointYView m n len ye yo) (pointY m n len ye yo) =
      packV (pointYView m n len ye yo) := packPoint_eq _ _ (pointY_eq m n len ye yo)

theorem packPointM_eq (m n : Nat) (xa ya : Array Char) (dm xf yf : RFront) :
    packPoint (pointMView m n xa ya dm xf yf) (pointM m n xa ya dm xf yf) =
      packV (pointMView m n xa ya dm xf yf) := packPoint_eq _ _ (pointM_eq m n xa ya dm xf yf)

def nextLevelP (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) : RLevel :=
  let xe := frontAtR hist pe (·.xf)
  let xo := frontAtR hist po (·.mf)
  let ye := frontAtR hist pe (·.yf)
  let yo := frontAtR hist po (·.mf)
  let dm := frontAtR hist px (·.mf)
  let xf := packPoint (pointXView m n xe xo) (pointX m n xe xo)
  let yf := packPoint (pointYView m n len ye yo) (pointY m n len ye yo)
  ⟨packPoint (pointMView m n xa ya dm xf yf) (pointM m n xa ya dm xf yf), xf, yf⟩

theorem nextLevelP_eq (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) :
    nextLevelP m n xa ya len pe po px hist = nextLevelR m n xa ya len pe po px hist := by
  simp only [nextLevelP, packPointX_eq, packPointY_eq, packPointM_eq]
  simp only [pointXView, pointYView, pointMView, packV_mapV, packV_zipV,
    packV_shiftUpV, packV_shiftDownV, packV_viewR, nextLevelR]

end AlignmentSpec
#print axioms AlignmentSpec.nextLevelP_eq
