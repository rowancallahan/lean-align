import MapperFastIndex

/-!
Packed anchor lists `A·16 + mask`: merging, and the support lookup `supNear`.

* `lmerge` is the list form of `merge` (`merge_toList`); it keeps lists
  increasing in `A` and adds the masks of equal anchors (`lmerge_spec`).
* `single_spec`: one seed's anchors, through a certified index: increasing,
  each `A·16 + 2^j`, and mask `seedBit j A` per diagonal.
* `supScan_found`, `sorted_gap`: tools for `supNear` (`supNearM_spec` in
  `MapperFastLazy.lean`).
-/

namespace MapSpec.Fast

def lmerge : List Nat → List Nat → List Nat
  | [], ys => ys
  | a :: xs, [] => a :: xs
  | a :: xs, b :: ys =>
    if a / 16 < b / 16 then a :: lmerge xs (b :: ys)
    else if b / 16 < a / 16 then b :: lmerge (a :: xs) ys
    else (a + b % 16) :: lmerge xs ys
termination_by xs ys => xs.length + ys.length

theorem drop_cons_arr (x : Array Nat) (i : Nat) (h : i < x.size) :
    x.toList.drop i = x[i] :: x.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), Array.getElem_toList]

theorem drop_nil_arr (x : Array Nat) (i : Nat) (h : x.size ≤ i) : x.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa using h)

theorem merge_toList (x y : Array Nat) :
    ∀ d i j acc, (x.size - i) + (y.size - j) = d →
      (merge x y i j acc).toList = acc.toList ++ lmerge (x.toList.drop i) (y.toList.drop j) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro i j acc hd
  unfold merge
  by_cases hi : i < x.size
  · rw [dif_pos hi]
    by_cases hj : j < y.size
    · rw [dif_pos hj]
      simp only []
      rw [drop_cons_arr x i hi, drop_cons_arr y j hj, lmerge.eq_3]
      split
      · rw [ih _ (by omega) (i + 1) j _ rfl, Array.toList_push, List.append_assoc, drop_cons_arr y j hj]; rfl
      · split
        · rw [ih _ (by omega) i (j + 1) _ rfl, Array.toList_push, List.append_assoc, drop_cons_arr x i hi]; rfl
        · rw [ih _ (by omega) (i + 1) (j + 1) _ rfl, Array.toList_push, List.append_assoc]; rfl
    · rw [dif_neg hj, ih _ (by omega) (i + 1) j _ rfl, Array.toList_push, List.append_assoc,
        drop_nil_arr y j (by omega), drop_cons_arr x i hi]
      cases x.toList.drop (i + 1) <;> simp [lmerge]
  · rw [dif_neg hi, drop_nil_arr x i (by omega)]
    by_cases hj : j < y.size
    · rw [dif_pos hj, ih _ (by omega) i (j + 1) _ rfl, Array.toList_push, List.append_assoc,
        drop_nil_arr x i (by omega), drop_cons_arr y j hj]
      simp [lmerge]
    · rw [dif_neg hj, drop_nil_arr y j (by omega)]; simp [lmerge]

/-- Mask of anchor `A` in a packed list (sum over its entries with that `A`). -/
def mv : List Nat → Nat → Nat
  | [], _ => 0
  | e :: l, A => (if e / 16 = A then e % 16 else 0) + mv l A

def SortedA (l : List Nat) : Prop := l.Pairwise (fun a b => a / 16 < b / 16)

theorem mv_zero (l : List Nat) (A : Nat) (h : ∀ e ∈ l, e / 16 ≠ A) : mv l A = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [mv, if_neg (h e List.mem_cons_self), Nat.zero_add]
    exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem mv_of_mem (l : List Nat) (hs : SortedA l) (e : Nat) (he : e ∈ l) : mv l (e / 16) = e % 16 := by
  induction l with
  | nil => simp at he
  | cons a l ih =>
    unfold SortedA at hs
    rw [List.pairwise_cons] at hs
    simp only [mv]
    rcases List.mem_cons.mp he with rfl | he'
    · rw [if_pos rfl, mv_zero l _ (fun e' he' => by have := hs.1 e' he'; omega)]; simp
    · rw [ih hs.2 he', if_neg (by have := hs.1 e he'; omega)]; simp

theorem lmerge_keys (xs ys : List Nat) : ∀ e ∈ lmerge xs ys, ∃ z ∈ xs ++ ys, z / 16 ≤ e / 16 := by
  induction xs, ys using lmerge.induct with
  | case1 ys => intro e he; exact ⟨e, by simpa [lmerge] using he, Nat.le_refl _⟩
  | case2 a xs => intro e he; exact ⟨e, by simpa [lmerge] using he, Nat.le_refl _⟩
  | case3 a xs b ys h ih =>
    intro e he
    rw [lmerge, if_pos h] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨e, by simp, Nat.le_refl _⟩
    · obtain ⟨z, hz, hz'⟩ := ih e he; exact ⟨z, by simp at hz ⊢; grind, hz'⟩
  | case4 a xs b ys h h' ih =>
    intro e he
    rw [lmerge, if_neg h, if_pos h'] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨e, by simp, Nat.le_refl _⟩
    · obtain ⟨z, hz, hz'⟩ := ih e he; exact ⟨z, by simp at hz ⊢; grind, hz'⟩
  | case5 a xs b ys h h' ih =>
    intro e he
    rw [lmerge, if_neg h, if_neg h'] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨a, by simp, by omega⟩
    · obtain ⟨z, hz, hz'⟩ := ih e he; exact ⟨z, by simp at hz ⊢; grind, hz'⟩

/-- Equal anchors of the two lists have masks that fit together. -/
def Fits (xs ys : List Nat) : Prop := ∀ a ∈ xs, ∀ b ∈ ys, a / 16 = b / 16 → a % 16 + b % 16 < 16

theorem lmerge_spec (xs ys : List Nat) (hx : SortedA xs) (hy : SortedA ys) (hf : Fits xs ys) :
    SortedA (lmerge xs ys) ∧ ∀ A, mv (lmerge xs ys) A = mv xs A + mv ys A := by
  induction xs, ys using lmerge.induct with
  | case1 ys => simp [lmerge, mv, hy]
  | case2 a xs => simp [lmerge, mv, hx]
  | case3 a xs b ys h ih =>
    unfold SortedA at hx hy
    have hx' := List.pairwise_cons.mp hx
    obtain ⟨h1, h2⟩ := ih hx'.2 hy (fun a' ha b' hb => hf a' (List.mem_cons_of_mem _ ha) b' hb)
    rw [lmerge, if_pos h]
    refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, h1⟩, fun A => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := lmerge_keys _ _ e he
      rcases List.mem_append.mp hz with hz | hz
      · have := hx'.1 z hz; omega
      · rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · have := (List.pairwise_cons.mp hy).1 z hz; omega
    · simp only [mv]; rw [h2]; simp only [mv]; omega
  | case4 a xs b ys h h' ih =>
    unfold SortedA at hx hy
    have hy' := List.pairwise_cons.mp hy
    obtain ⟨h1, h2⟩ := ih hx hy'.2 (fun a' ha b' hb => hf a' ha b' (List.mem_cons_of_mem _ hb))
    rw [lmerge, if_neg h, if_pos h']
    refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, h1⟩, fun A => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := lmerge_keys _ _ e he
      rcases List.mem_append.mp hz with hz | hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · have := (List.pairwise_cons.mp hx).1 z hz; omega
      · have := hy'.1 z hz; omega
    · simp only [mv]; rw [h2]; simp only [mv]; omega
  | case5 a xs b ys h h' ih =>
    unfold SortedA at hx hy
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    obtain ⟨h1, h2⟩ := ih hx'.2 hy'.2
      (fun a' ha b' hb => hf a' (List.mem_cons_of_mem _ ha) b' (List.mem_cons_of_mem _ hb))
    have hab := hf a List.mem_cons_self b List.mem_cons_self (by omega)
    have hk : (a + b % 16) / 16 = a / 16 := by omega
    rw [lmerge, if_neg h, if_neg h']
    refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, h1⟩, fun A => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := lmerge_keys _ _ e he
      rw [hk]
      rcases List.mem_append.mp hz with hz | hz
      · have := hx'.1 z hz; omega
      · have := hy'.1 z hz; omega
    · simp only [mv]; rw [h2, hk]
      by_cases hA : a / 16 = A
      · rw [if_pos hA, if_pos hA, if_pos (by omega)]; omega
      · rw [if_neg hA, if_neg hA, if_neg (by omega)]; omega

theorem lmerge_pos (xs ys : List Nat) (hx : ∀ e ∈ xs, 0 < e % 16) (hy : ∀ e ∈ ys, 0 < e % 16)
    (hf : Fits xs ys) : ∀ e ∈ lmerge xs ys, 0 < e % 16 := by
  induction xs, ys using lmerge.induct with
  | case1 ys => simpa [lmerge] using hy
  | case2 a xs => simpa [lmerge] using hx
  | case3 a xs b ys h ih =>
    rw [lmerge, if_pos h]
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hx e List.mem_cons_self
    · exact ih (fun e' h' => hx e' (List.mem_cons_of_mem _ h')) hy
        (fun a' ha b' hb => hf a' (List.mem_cons_of_mem _ ha) b' hb) e he
  | case4 a xs b ys h h' ih =>
    rw [lmerge, if_neg h, if_pos h']
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hy e List.mem_cons_self
    · exact ih hx (fun e' h'' => hy e' (List.mem_cons_of_mem _ h''))
        (fun a' ha b' hb => hf a' ha b' (List.mem_cons_of_mem _ hb)) e he
  | case5 a xs b ys h h' ih =>
    rw [lmerge, if_neg h, if_neg h']
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · have := hx a List.mem_cons_self
      have hab := hf a List.mem_cons_self b List.mem_cons_self (by omega)
      omega
    · exact ih (fun e' h'' => hx e' (List.mem_cons_of_mem _ h'')) (fun e' h'' => hy e' (List.mem_cons_of_mem _ h''))
        (fun a' ha b' hb => hf a' (List.mem_cons_of_mem _ ha) b' (List.mem_cons_of_mem _ hb)) e he

/-! ## The anchors of a read -/

instance (G : ByteArray) (p : Nat) (R : ByteArray) (s : Nat) : Decidable (MatchAt G p R s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Bit `j` of the mask of diagonal `A`: seed `j` occurs at `A − (BIAS − j·q)`. -/
def seedBit (G R : ByteArray) (j A : Nat) : Nat :=
  if BIAS - j * q ≤ A ∧ MatchAt G (A - (BIAS - j * q)) R (j * q) then 2 ^ j else 0

/-- The seeds that occur on (biased) diagonal `A`. -/
def maskAt (G R : ByteArray) (A : Nat) : Nat :=
  seedBit G R 0 A + seedBit G R 1 A + seedBit G R 2 A + seedBit G R 3 A

theorem maskAt_lt (G R : ByteArray) (A : Nat) : maskAt G R A < 16 := by
  unfold maskAt seedBit
  split <;> split <;> split <;> split <;> simp

theorem single_spec (ix : HIdx) (G R : ByteArray) (j : Nat) (hj : 2 ^ j < 16) (hjq : j * q ≤ BIAS)
    (hchk : checkIdx ix G = true) :
    SortedA (lookupSeed ix G R j).toList ∧ (∀ e ∈ (lookupSeed ix G R j).toList, e % 16 = 2 ^ j) ∧
      ∀ A, mv (lookupSeed ix G R j).toList A = seedBit G R j A := by
  obtain ⟨hp, hm⟩ := lookupSeed_spec ix G R j hchk
  have hres : ∀ e ∈ (lookupSeed ix G R j).toList, e % 16 = 2 ^ j ∧ ∃ p, MatchAt G p R (j * q) ∧
      e / 16 = p + (BIAS - j * q) := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := (hm e).1 he
    unfold anchorOf
    generalize 2 ^ j = w at *
    exact ⟨by omega, p, hp, by omega⟩
  refine ⟨List.Pairwise.imp_of_mem (fun ha hb hab => by
      have := (hres _ ha).1; have := (hres _ hb).1; omega) hp, fun e he => (hres e he).1, fun A => ?_⟩
  unfold seedBit
  split
  · next h =>
    have hmem : anchorOf j (A - (BIAS - j * q)) ∈ (lookupSeed ix G R j).toList := (hm _).2 ⟨_, h.2, rfl⟩
    have := mv_of_mem _ (List.Pairwise.imp_of_mem (fun ha hb hab => by
      have := (hres _ ha).1; have := (hres _ hb).1; omega) hp) _ hmem
    unfold anchorOf at this
    generalize 2 ^ j = w at *
    rw [show ((A - (BIAS - j * q) + (BIAS - j * q)) * 16 + w) / 16 = A by omega] at this
    rw [this]; omega
  · next h =>
    apply mv_zero
    intro e he he'
    obtain ⟨-, p, hp', hp''⟩ := hres e he
    apply h
    refine ⟨by omega, ?_⟩
    rw [show A - (BIAS - j * q) = p by omega]; exact hp'

theorem merge_list (x y : Array Nat) : (merge x y 0 0 #[]).toList = lmerge x.toList y.toList := by
  rw [merge_toList x y _ 0 0 #[] rfl]; simp

/-! ## `supNear` -/

theorem supScan_found (as : Array Nat) (A v stop : Nat) :
    ∀ d k, stop - k = d → (∃ k', k ≤ k' ∧ k' < stop ∧ as[k']! / 16 = A) →
      (∀ k', k ≤ k' → k' < stop → as[k']! / 16 = A → pop4 (as[k']! % 16) = v) → supScan as A k stop = v := by
  intro d
  induction d with
  | zero => intro k hd ⟨k', h1, h2, _⟩; omega
  | succ d ih =>
    intro k hd hex hv
    unfold supScan
    rw [if_pos (by omega)]
    split
    · next h => exact hv k (Nat.le_refl _) (by omega) (by simpa using h)
    · next h =>
      obtain ⟨k', h1, h2, h3⟩ := hex
      have : k' ≠ k := by intro e; subst e; simp_all
      exact ih (k + 1) (by omega) ⟨k', by omega, h2, h3⟩ (fun k'' a b c => hv k'' (by omega) b c)

theorem supScan_none (as : Array Nat) (A stop : Nat) :
    ∀ d k, stop - k = d → (∀ k', k ≤ k' → k' < stop → as[k']! / 16 ≠ A) → supScan as A k stop = 0 := by
  intro d
  induction d with
  | zero => intro k hd _; unfold supScan; rw [if_neg (by omega)]
  | succ d ih =>
    intro k hd hn
    unfold supScan
    rw [if_pos (by omega), if_neg (by simpa using hn k (Nat.le_refl _) (by omega))]
    exact ih (k + 1) (by omega) (fun k' a b => hn k' (by omega) b)

theorem sorted_gap (as : Array Nat) (hs : SortedA as.toList) :
    ∀ d k, k + d < as.size → as[k]! / 16 + d ≤ as[k + d]! / 16 := by
  have adj : ∀ k, k + 1 < as.size → as[k]! / 16 < as[k + 1]! / 16 := by
    intro k hk
    have := List.pairwise_iff_getElem.mp hs k (k + 1) (by simp; omega) (by simp; omega) (by omega)
    simp only [Array.getElem_toList] at this
    rw [getElem!_pos as k (by omega), getElem!_pos as (k + 1) hk]; exact this
  intro d
  induction d with
  | zero => intro k _; simp
  | succ d ih =>
    intro k hk
    have := ih k (by omega)
    have := adj (k + d) (by omega)
    rw [show k + (d + 1) = k + d + 1 by omega]; omega

end MapSpec.Fast

