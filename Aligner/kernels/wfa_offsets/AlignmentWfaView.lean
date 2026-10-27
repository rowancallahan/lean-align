import AlignmentWfaOffR

/-! Deferred array expressions. Only final wavefront arrays are materialized.
Every combinator commutes with `materialize`, so fusion is exact equality. -/
namespace AlignmentSpec


structure NView where
  size : Nat
  get : Nat → Nat

@[specialize] def arrayBuildGo {n : Nat} (f : Fin n → Nat) (acc : Array Nat) :
    (i : Nat) → i ≤ n → Array Nat
  | i + 1, h =>
    have w : n - i - 1 < n := by omega
    arrayBuildGo f (acc.push (f ⟨n - i - 1, w⟩)) i (by omega)
  | 0, _ => acc

theorem ofFn_consC {n : Nat} (f : Fin (n + 1) → Nat) :
    Array.ofFn f = #[f ⟨0, by omega⟩] ++ Array.ofFn (fun i : Fin n => f ⟨i.val + 1, by omega⟩) := by
  apply Array.ext
  · simp [Nat.add_comm]
  · intro i h1 h2
    cases i with
    | zero => simp
    | succ i => simp [Array.getElem_append]

theorem arrayBuildGo_eq {n : Nat} (f : Fin n → Nat) (i : Nat) :
    ∀ acc (h : i ≤ n), arrayBuildGo f acc i h = acc ++
      Array.ofFn (fun j : Fin i => f ⟨n - i + j.val, by omega⟩) := by
  induction i with
  | zero =>
    intro acc h
    have hz : Array.ofFn (fun j : Fin 0 => f ⟨n - 0 + j.val, by omega⟩) = #[] := by
      apply Array.ext
      · simp
      · intro j hj; simp at hj
    rw [arrayBuildGo, hz, Array.append_empty]
  | succ i ih =>
    intro acc h
    rw [arrayBuildGo, ih, ofFn_consC]
    have hi : n - (i + 1) = n - i - 1 := by omega
    simp only [Nat.add_zero, hi, ← Array.append_assoc, Array.push_eq_append]
    congr 1
    congr 1
    funext j
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

@[macro_inline] def arrayBuild {n : Nat} (f : Fin n → Nat) : Array Nat :=
  arrayBuildGo f (Array.emptyWithCapacity n) n (by omega)

theorem arrayBuild_eq {n : Nat} (f : Fin n → Nat) : arrayBuild f = Array.ofFn f := by
  rw [arrayBuild, arrayBuildGo_eq]
  simp

@[macro_inline] def materialize (v : NView) : Array Nat :=
  arrayBuild (fun i : Fin v.size => v.get i.val)

@[macro_inline] def arrayView (a : Array Nat) : NView :=
  ⟨a.size, fun i => a[i]?.getD 0⟩

@[macro_inline] def mapView (g : Nat → Nat → Nat) (a : NView) : NView :=
  ⟨a.size, fun i => g i (a.get i)⟩

@[macro_inline] def repView (n a : Nat) : NView := ⟨n, fun _ => a⟩

@[macro_inline] def appendView (a b : NView) : NView :=
  ⟨a.size + b.size, fun i => if i < a.size then a.get i else b.get (i - a.size)⟩

@[macro_inline] def extractView (a : NView) (start stop : Nat) : NView :=
  ⟨min stop a.size - start, fun i => a.get (start + i)⟩

@[macro_inline] def zipView (a b : NView) : NView :=
  ⟨min a.size b.size, fun i => betterR (a.get i) (b.get i)⟩

@[simp] theorem materialize_size (v : NView) : (materialize v).size = v.size := by
  simp [materialize, arrayBuild_eq]

@[simp] theorem materialize_get (v : NView) (i : Nat) (h : i < (materialize v).size) :
    (materialize v)[i] = v.get i := by simp [materialize, arrayBuild_eq]

theorem materialize_arrayView (a : Array Nat) : materialize (arrayView a) = a := by
  apply Array.ext
  · simp [arrayView]
  · intro i h1 h2
    simp [arrayView, Array.getElem?_eq_getElem h2]

theorem materialize_mapView (g : Nat → Nat → Nat) (a : NView) :
    materialize (mapView g a) = (materialize a).mapIdx g := by
  apply Array.ext
  · simp [mapView]
  · intro i h1 h2; simp [mapView]

theorem materialize_repView (n a : Nat) :
    materialize (repView n a) = Array.replicate n a := by
  apply Array.ext
  · simp [repView]
  · intro i h1 h2; simp [repView]

theorem materialize_appendView (a b : NView) :
    materialize (appendView a b) = materialize a ++ materialize b := by
  apply Array.ext
  · simp [appendView]
  · intro i h1 h2
    simp only [materialize_get, appendView]
    split
    · rename_i h
      rw [Array.getElem_append_left (by simpa using h), materialize_get]
    · rename_i h
      rw [Array.getElem_append_right (by simpa using Nat.le_of_not_lt h), materialize_get,
        materialize_size]

theorem materialize_extractView (a : NView) (start stop : Nat) :
    materialize (extractView a start stop) = (materialize a).extract start stop := by
  apply Array.ext
  · simp [extractView]
  · intro i h1 h2; simp [extractView]

theorem materialize_zipView (a b : NView) :
    materialize (zipView a b) = Array.zipWith betterR (materialize a) (materialize b) := by
  apply Array.ext
  · simp [zipView]
  · intro i h1 h2; simp [zipView]

@[macro_inline] def zipExtView (a b : NView) : NView :=
  ⟨max a.size b.size, fun i => betterR
    (if i < a.size then a.get i else 0)
    (if i < b.size then b.get i else 0)⟩

theorem materialize_zipExtView (a b : NView) :
    materialize (zipExtView a b) = azipExtR (materialize a) (materialize b) := by
  unfold azipExtR
  simp only [materialize_size]
  split
  · rename_i hab
    apply Array.ext
    · simp [zipExtView, Nat.max_eq_right hab, Nat.min_eq_left hab]; omega
    · intro i h1 h2
      have hi : i < b.size := by simpa [zipExtView, Nat.max_eq_right hab] using h1
      by_cases ha : i < a.size
      · simp [zipExtView, Array.getElem_append, Nat.min_eq_left hab, ha, hi]
      · have hai : a.size ≤ i := by omega
        simp [zipExtView, Array.getElem_append, Nat.min_eq_left hab, ha, hi,
          Nat.add_sub_of_le hai, betterR]
        omega
  · rename_i hab
    have hba : b.size ≤ a.size := by omega
    apply Array.ext
    · simp [zipExtView, Nat.max_eq_left hba, Nat.min_eq_right hba]; omega
    · intro i h1 h2
      have hi : i < a.size := by simpa [zipExtView, Nat.max_eq_left hba] using h1
      by_cases hb : i < b.size
      · simp [zipExtView, Array.getElem_append, Nat.min_eq_right hba, hb, hi]
      · have hbi : b.size ≤ i := by omega
        simp [zipExtView, Array.getElem_append, Nat.min_eq_right hba, hb, hi,
          Nat.add_sub_of_le hbi, betterR]

structure VFront where
  lo : Nat
  body : NView

@[macro_inline] def packV (f : VFront) : RFront := ⟨f.lo, materialize f.body⟩
@[macro_inline] def viewR (f : RFront) : VFront := ⟨f.lo, arrayView f.body⟩
@[macro_inline] def mapV (g : Nat → Nat → Nat) (f : VFront) : VFront :=
  ⟨f.lo, mapView (fun i a => g (f.lo + i) a) f.body⟩
def zipVOld (f g : VFront) : VFront :=
  if f.body.size = 0 then g
  else if g.body.size = 0 then f
  else
    let lo := min f.lo g.lo
    ⟨lo, zipExtView (appendView (repView (f.lo - lo) 0) f.body)
      (appendView (repView (g.lo - lo) 0) g.body)⟩
@[macro_inline] def shiftUpV (f : VFront) : VFront := ⟨f.lo + 1, f.body⟩
def shiftDownVOld (len : Nat) (f : VFront) : VFront :=
  match f.lo with
  | p + 1 =>
    if f.body.size ≤ len - (p + 1) then ⟨p, f.body⟩
    else ⟨p, extractView f.body 0 (len - (p + 1))⟩
  | 0 => ⟨0, extractView f.body 1 (1 + (len - 1))⟩

@[macro_inline] def zipV (f g : VFront) : VFront :=
  let lo := min f.lo g.lo
  let both := zipExtView (appendView (repView (f.lo - lo) 0) f.body)
    (appendView (repView (g.lo - lo) 0) g.body)
  ⟨(if f.body.size = 0 then g.lo else if g.body.size = 0 then f.lo else lo),
   ⟨(if f.body.size = 0 then g.body.size else if g.body.size = 0 then f.body.size else both.size),
    fun i => if f.body.size = 0 then g.body.get i
      else if g.body.size = 0 then f.body.get i else both.get i⟩⟩

theorem zipV_eqOld (f g : VFront) : zipV f g = zipVOld f g := by
  by_cases hf : f.body.size = 0 <;> by_cases hg : g.body.size = 0 <;>
    simp [zipV, zipVOld, hf, hg]
  cases g with
  | mk lo body => cases body; simp_all

@[macro_inline] def shiftDownV (len : Nat) (f : VFront) : VFront :=
  ⟨f.lo - 1,
    ⟨(if f.lo = 0 then min (1 + (len - 1)) f.body.size - 1
      else if f.body.size ≤ len - f.lo then f.body.size
      else min (len - f.lo) f.body.size),
     fun i => f.body.get (if f.lo = 0 then 1 + i else i)⟩⟩

theorem shiftDownV_eqOld (len : Nat) (f : VFront) :
    shiftDownV len f = shiftDownVOld len f := by
  cases f with
  | mk lo body =>
    cases lo with
    | zero => simp [shiftDownV, shiftDownVOld, extractView]
    | succ p =>
      by_cases h : body.size ≤ len - (p + 1) <;>
        simp [shiftDownV, shiftDownVOld, extractView, h]

@[simp] theorem packV_viewR (f : RFront) : packV (viewR f) = f := by
  simp [packV, viewR, materialize_arrayView]
theorem packV_mapV (g : Nat → Nat → Nat) (f : VFront) :
    packV (mapV g f) = mapR g (packV f) := by
  simp only [packV, mapV, mapR, materialize_mapView]
theorem packV_zipV (f g : VFront) :
    packV (zipV f g) = zipR (packV f) (packV g) := by
  simp only [zipV_eqOld, zipVOld, zipR, packV, Array.isEmpty, materialize_size, decide_eq_true_eq]
  split
  · rfl
  · split
    · rfl
    · simp only [materialize_zipExtView, materialize_appendView, materialize_repView]
theorem packV_shiftUpV (f : VFront) : packV (shiftUpV f) = shiftUpR (packV f) := rfl
theorem packV_shiftDownV (len : Nat) (f : VFront) :
    packV (shiftDownV len f) = shiftDownR len (packV f) := by
  cases f with
  | mk lo body =>
    cases lo with
    | zero => simp [shiftDownV_eqOld, packV, shiftDownVOld, shiftDownR, materialize_extractView]
    | succ p =>
      simp only [shiftDownV_eqOld, shiftDownVOld, shiftDownR, packV, materialize_size]
      split
      · rfl
      · simp only [materialize_extractView]

def nextLevelV (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) : RLevel :=
  let xf := packV (zipV
    (shiftUpV (mapV (pushXR m n) (viewR (frontAtR hist pe (·.xf)))))
    (shiftUpV (mapV (pushXR m n) (viewR (frontAtR hist po (·.mf))))))
  let yf := packV (zipV
    (shiftDownV len (mapV (pushYR m n) (viewR (frontAtR hist pe (·.yf)))))
    (shiftDownV len (mapV (pushYR m n) (viewR (frontAtR hist po (·.mf))))))
  let base := zipV (zipV (mapV (pushDR m n) (viewR (frontAtR hist px (·.mf))))
    (viewR xf)) (viewR yf)
  ⟨packV (mapV (extR m xa ya) base), xf, yf⟩

theorem nextLevelV_eq (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) :
    nextLevelV m n xa ya len pe po px hist = nextLevelR m n xa ya len pe po px hist := by
  simp only [nextLevelV, packV_zipV, packV_shiftUpV, packV_shiftDownV,
    packV_mapV, packV_viewR, nextLevelR]

end AlignmentSpec
#print axioms AlignmentSpec.nextLevelV_eq
