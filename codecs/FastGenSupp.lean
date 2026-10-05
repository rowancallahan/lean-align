import FastGenWordFilt

/-!
# Seed support of all diagonals in one sweep (`suppCntC`)

`suppA acc D r` (the anchor arrays of `acc` with an anchor within `r` of diagonal `D`)
is a binary search per array and diagonal.  For the sorted diagonals `ds` of a read,
`suppCnt` gets all of them at once: one pass per array, a pointer moving forward as
`D` grows.  `suppCntC` checks (in one pass) that the arrays increase and `ds` does
not decrease, else falls back to `suppA` per diagonal, so in all cases

    (suppCntC acc r ds).getD t 0 = suppA acc (ds.getD t 0) r      (t < ds.length; suppCntC_get)

`stageKSS` is `stageKSV` reading the support from such counts while the filter's
radius is still `r0` (`stageKSS_eq`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- First index `≥ i` whose anchor's diagonal is `≥ lo` (`f`: fuel). -/
def advP (a : Array Nat) (lo : Nat) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if i < a.size ∧ a[i]! / 16 < lo then advP a lo f (i + 1) else i

/-- Add, for each `D` of `ds` (counts from index `k`), whether `a` has an anchor within `r`. -/
def sweepA (a : Array Nat) (r : Nat) : List Nat → Nat → Nat → Array Nat → Array Nat
  | [], _, _, cnt => cnt
  | D :: ds, k, i, cnt =>
    let i := advP a (D - r) (a.size - i) i
    let cnt := if i < a.size ∧ a[i]! / 16 ≤ D + r then cnt.modify k (· + 1) else cnt
    sweepA a r ds (k + 1) i cnt

/-- The supports of `ds` (sorted arrays, sorted `ds`). -/
def suppCnt (acc : List (Array Nat)) (r : Nat) (ds : List Nat) : Array Nat :=
  acc.foldl (fun cnt a => sweepA a r ds 0 0 cnt) (Array.replicate ds.length 0)

/-- `a` increases from index `i` on (`f`: fuel). -/
def incA (a : Array Nat) : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i => if i + 1 < a.size then decide (a[i]! < a[i + 1]!) && incA a f (i + 1) else true

/-- `ds` does not decrease. -/
def sortedL : List Nat → Bool
  | a :: b :: t => decide (a ≤ b) && sortedL (b :: t)
  | _ => true

/-- `suppCnt` when its conditions hold, else the supports one by one. -/
def suppCntC (acc : List (Array Nat)) (r : Nat) (ds : List Nat) : Array Nat :=
  if sortedL ds && acc.all (fun a => incA a a.size 0) then suppCnt acc r ds
  else (ds.map fun D => suppA acc D r).toArray

/-- `kfiltV` with the support `s` of `D` given. -/
@[inline] def kfiltVF {Gt : Type} [GRead Gt] [GPk Gt] (K : RP) (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D s : Nat) : Bool :=
  let Q := min lim b.pen
  let r := 2 * gapBound sc0 (-(Q : Int))
  let n := R.size
  let fJ := acc.length - s
  let sb := sbound Q
  if fJ ≤ sb then
    match GPk.pk G with
    | some P =>
      if wordWin K n r D P then
        let a := P.o + (D - n - r)
        let o := a % 32
        let gs := loadW P.w (a / 32) ((o + 2 * r + n) / 32 + 2) (Array.emptyWithCapacity 12)
        unlookV K gs R G o Ls r D sb us fJ &&
          decide (n / pl ≤ sb + fineV K gs o n r (n / pl) 0 ((n + 31) / 32) 0)
      else kfilt R G acc us Ls lim b D
    | none => kfilt R G acc us Ls lim b D
  else false

/-- `stageKSV` over `ds` (from index `k` of the counts `cnt`, supports at radius `r0`). -/
@[specialize] def stageKSS {Gt : Type} [GRead Gt] [GPk Gt] (body : Nat → Best → Best) (K : RP) (R : ByteArray)
    (G : Gt) (acc : List (Array Nat)) (us : List Nat) (Ls lim r0 : Nat) (cnt : Array Nat) :
    List Nat → Nat → Best → Best
  | [], _, b => b
  | D :: ds, k, b =>
    let r := 2 * gapBound sc0 (-((min lim b.pen : Nat) : Int))
    let s := if r = r0 then cnt.getD k 0 else suppA acc D r
    let b := if kfiltVF K R G acc us Ls lim b D s then body D b else b
    stageKSS body K R G acc us Ls lim r0 cnt ds (k + 1) b

/-! ## Proofs -/

theorem kfiltVF_supp {Gt : Type} [GRead Gt] [GPk Gt] (K : RP) (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) :
    kfiltVF K R G acc us Ls lim b D (suppA acc D (2 * gapBound sc0 (-((min lim b.pen : Nat) : Int)))) =
      kfiltV K R G acc us Ls lim b D := rfl

section
variable (a : Array Nat) (hs : a.toList.Pairwise (· < ·))
include hs

theorem advP_spec (lo : Nat) : ∀ f i, f = a.size - i → i ≤ a.size → (∀ k, k < i → a[k]! / 16 < lo) →
    i ≤ advP a lo f i ∧ advP a lo f i ≤ a.size ∧ (∀ k, k < advP a lo f i → a[k]! / 16 < lo) ∧
      (advP a lo f i < a.size → lo ≤ a[advP a lo f i]! / 16) := by
  intro f
  induction f with
  | zero => intro i hf hi h; simp only [advP]; exact ⟨Nat.le_refl _, hi, h, fun h2 => by omega⟩
  | succ f ih =>
    intro i hf hi h
    simp only [advP]
    split
    · next hc =>
      have := ih (i + 1) (by omega) (by omega) (fun k hk => by
        by_cases e : k = i
        · subst e; exact hc.2
        · exact h k (by omega))
      exact ⟨by omega, this.2.1, this.2.2⟩
    · next hc => exact ⟨Nat.le_refl _, hi, h, fun h2 => by omega⟩

/-- The sweep's test at `D` is `anyNear`. -/
theorem flag_eq (lo hi i : Nat) (hi1 : i ≤ a.size) (h1 : ∀ k, k < i → a[k]! / 16 < lo)
    (h2 : i < a.size → lo ≤ a[i]! / 16) :
    decide (i < a.size ∧ a[i]! / 16 ≤ hi) = anyNear a lo hi := by
  apply Bool.eq_iff_iff.mpr
  rw [anyNear_spec a hs, decide_eq_true_iff]
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨a[i], Array.getElem_mem_toList h3, by rw [← getElem!_pos a i h3]; exact h2 h3,
      by rw [← getElem!_pos a i h3]; exact h4⟩
  · rintro ⟨e, he, hl, hh⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    simp only [Array.length_toList] at hk
    simp only [Array.getElem_toList] at hl hh
    have hki : i ≤ k := by
      apply Classical.byContradiction; intro hn
      have := h1 k (by omega); rw [getElem!_pos a k hk] at this; omega
    refine ⟨by omega, ?_⟩
    have := mono_get a hs i k hki hk
    rw [getElem!_pos a k hk] at this; omega

end

theorem getD_modify (cnt : Array Nat) (k t : Nat) :
    (cnt.modify k (· + 1)).getD t 0 = cnt.getD t 0 + if t = k ∧ k < cnt.size then 1 else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : k = t
  · subst h1
    by_cases h2 : k < cnt.size
    · simp [h2, Array.getElem?_eq_getElem h2]
    · simp [h2, Array.getElem?_eq_none (by omega : cnt.size ≤ k)]
  · simp [h1, Ne.symm h1]

/-- The flag of `a` at `D`. -/
def fl (a : Array Nat) (r D : Nat) : Nat := if anyNear a (D - r) (D + r) then 1 else 0

theorem sweepA_spec (a : Array Nat) (hs : a.toList.Pairwise (· < ·)) (r : Nat) :
    ∀ (ds : List Nat) (k i : Nat) (cnt : Array Nat), ds.Pairwise (· ≤ ·) → i ≤ a.size →
      (∀ D ∈ ds, ∀ k', k' < i → a[k']! / 16 < D - r) → k + ds.length ≤ cnt.size →
      (sweepA a r ds k i cnt).size = cnt.size ∧
      ∀ t, (sweepA a r ds k i cnt).getD t 0 =
        cnt.getD t 0 + if k ≤ t ∧ t < k + ds.length then fl a r (ds.getD (t - k) 0) else 0 := by
  intro ds
  induction ds with
  | nil => intro k i cnt _ _ _ _; simp [sweepA]; intro t h1 h2; omega
  | cons D ds ih =>
    intro k i cnt hsrt hi hinv hsz
    simp only [sweepA]
    have hrest := List.pairwise_cons.1 hsrt
    obtain ⟨h0, h1, h2, h3⟩ := advP_spec a hs (D - r) (a.size - i) i rfl hi (hinv D (List.mem_cons_self ..))
    generalize advP a (D - r) (a.size - i) i = j at h0 h1 h2 h3
    have hfl := flag_eq a hs (D - r) (D + r) j h1 h2 h3
    generalize hc : (if j < a.size ∧ a[j]! / 16 ≤ D + r then cnt.modify k (· + 1) else cnt) = cnt'
    have hc' : cnt'.size = cnt.size ∧ ∀ t, cnt'.getD t 0 = cnt.getD t 0 + if t = k then fl a r D else 0 := by
      rw [← hc]
      unfold fl
      rw [← hfl]
      by_cases hh : j < a.size ∧ a[j]! / 16 ≤ D + r
      · rw [if_pos hh, decide_eq_true hh]
        refine ⟨by simp, fun t => ?_⟩
        rw [getD_modify]
        have hk : k < cnt.size := by simp at hsz; omega
        by_cases e : t = k
        · rw [if_pos ⟨e, hk⟩, if_pos e]; rfl
        · rw [if_neg (fun h => e h.1), if_neg e]
      · rw [if_neg hh, decide_eq_false hh]; simp
    have := ih (k + 1) j cnt' hrest.2 h1 (fun D' hD' k' hk' => by
      have := h2 k' hk'; have := hrest.1 D' hD'; omega) (by simp at hsz; omega)
    refine ⟨this.1.trans hc'.1, fun t => ?_⟩
    rw [this.2 t, hc'.2 t]
    by_cases e : t = k
    · subst e
      simp; intro h; omega
    · by_cases h4 : k + 1 ≤ t ∧ t < k + 1 + ds.length
      · rw [if_pos h4, if_neg e, if_pos (by simp; omega),
          show t - k = (t - (k + 1)) + 1 by omega, List.getD_cons_succ, Nat.add_zero]
      · rw [if_neg h4, if_neg e, if_neg (by simp; omega)]

theorem suppA_cons (a : Array Nat) (acc : List (Array Nat)) (D r : Nat) :
    suppA (a :: acc) D r = fl a r D + suppA acc D r := by
  unfold suppA fl
  by_cases h : anyNear a (D - r) (D + r) = true <;> simp [h] <;> omega

theorem suppCnt_spec (r : Nat) (ds : List Nat) (hds : ds.Pairwise (· ≤ ·)) :
    ∀ (acc : List (Array Nat)) (cnt : Array Nat), (∀ a ∈ acc, a.toList.Pairwise (· < ·)) → ds.length ≤ cnt.size →
      (acc.foldl (fun cnt a => sweepA a r ds 0 0 cnt) cnt).size = cnt.size ∧
      ∀ t, t < ds.length → (acc.foldl (fun cnt a => sweepA a r ds 0 0 cnt) cnt).getD t 0 =
        cnt.getD t 0 + suppA acc (ds.getD t 0) r := by
  intro acc
  induction acc with
  | nil => intro cnt _ _; simp [suppA]
  | cons a acc ih =>
    intro cnt hs hsz
    simp only [List.foldl_cons]
    have h1 := sweepA_spec a (hs a (List.mem_cons_self ..)) r ds 0 0 cnt hds (Nat.zero_le _)
      (fun _ _ k' hk' => by omega) (by omega)
    have h2 := ih (sweepA a r ds 0 0 cnt) (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha')) (by omega)
    refine ⟨h2.1.trans h1.1, fun t ht => ?_⟩
    rw [h2.2 t ht, h1.2 t, if_pos ⟨Nat.zero_le _, by omega⟩, suppA_cons, Nat.sub_zero]
    omega

theorem incA_spec (a : Array Nat) : ∀ f i, incA a f i = true → a.size ≤ i + f + 1 →
    ∀ x y, i ≤ x → x < y → y < a.size → a[x]! < a[y]! := by
  intro f
  induction f with
  | zero => intro i _ hf x y h1 h2 h3; omega
  | succ f ih =>
    intro i h hf x y h1 h2 h3
    simp only [incA] at h
    split at h
    · next hi =>
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases e : x = i
      · subst e
        by_cases e2 : y = x + 1
        · subst e2; exact h.1
        · exact Nat.lt_trans h.1 (ih (x + 1) h.2 (by omega) (x + 1) y (Nat.le_refl _) (by omega) h3)
      · exact ih (i + 1) h.2 (by omega) x y (by omega) h2 h3
    · omega

theorem incA_pw (a : Array Nat) (h : incA a a.size 0 = true) : a.toList.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro x y hx hy hxy
  simp only [Array.length_toList] at hx hy
  have := incA_spec a a.size 0 h (by omega) x y (Nat.zero_le _) hxy hy
  simp only [Array.getElem_toList]
  rwa [getElem!_pos a x hx, getElem!_pos a y hy] at this

theorem sortedL_pw : ∀ ds : List Nat, sortedL ds = true → ds.Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: t, h => by
    simp only [sortedL, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := sortedL_pw (b :: t) h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.le_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

/-- **The swept supports are `suppA`.** -/
theorem suppCntC_get (acc : List (Array Nat)) (r : Nat) (ds : List Nat) (t : Nat) (ht : t < ds.length) :
    (suppCntC acc r ds).getD t 0 = suppA acc (ds.getD t 0) r := by
  unfold suppCntC
  split
  · next h =>
    rw [Bool.and_eq_true, List.all_eq_true] at h
    have := suppCnt_spec r ds (sortedL_pw ds h.1) acc (Array.replicate ds.length 0)
      (fun a ha => incA_pw a (h.2 a ha)) (by simp)
    unfold suppCnt
    rw [this.2 t ht]
    simp [Array.getD_eq_getD_getElem?, ht]
  · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem ht, Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD]

theorem stageKSS_eq {Gt : Type} [GRead Gt] [GPk Gt] (body : Nat → Best → Best) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim r0 : Nat) (cnt : Array Nat) :
    ∀ (ds : List Nat) (k : Nat) (b : Best),
      (∀ t, t < ds.length → cnt.getD (k + t) 0 = suppA acc (ds.getD t 0) r0) →
      stageKSS body (packRP R) R G acc us Ls lim r0 cnt ds k b = stageKSV body (packRP R) R G acc us Ls lim ds b := by
  intro ds
  induction ds with
  | nil => intro k b _; rfl
  | cons D ds ih =>
    intro k b h
    simp only [stageKSS, stageKSV, List.foldl_cons]
    have hs : (if 2 * gapBound sc0 (-((min lim b.pen : Nat) : Int)) = r0 then cnt.getD k 0
        else suppA acc D (2 * gapBound sc0 (-((min lim b.pen : Nat) : Int)))) =
        suppA acc D (2 * gapBound sc0 (-((min lim b.pen : Nat) : Int))) := by
      split
      · next e => rw [e]; have := h 0 (by simp); simpa using this
      · rfl
    rw [hs, kfiltVF_supp]
    rw [ih (k + 1) _ (fun t ht => by
      have := h (t + 1) (by simp; omega)
      rw [show k + (t + 1) = k + 1 + t by omega, List.getD_cons_succ] at this
      exact this)]
    rfl

/-- **`stageKSV` with the swept supports.** -/
theorem stageKSS_cnt {Gt : Type} [GRead Gt] [GPk Gt] (body : Nat → Best → Best) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim r0 : Nat) (ds : List Nat) (b : Best) :
    stageKSS body (packRP R) R G acc us Ls lim r0 (suppCntC acc r0 ds) ds 0 b =
      stageKSV body (packRP R) R G acc us Ls lim ds b :=
  stageKSS_eq body R G acc us Ls lim r0 _ ds 0 b (fun t ht => by rw [Nat.zero_add]; exact suppCntC_get acc r0 ds t ht)

end MapSpec.Fast
