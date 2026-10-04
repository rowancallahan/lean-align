import MapperFastLoop

/-!
Lazy seed lookups (`mapChrom2`, the prototype's `mapCore`): the anchors after
some of the seeds were looked up, and the loop invariant.

* `AnchorsM m as`: `as` is increasing in the diagonal and holds exactly
  `A·16 + m A` for the diagonals with `m A ≠ 0`; after looking up the seeds of
  the bit set `J`, `m = maskJ G R J` (`merge_step`).
* `supAt` counts the seeds clean on a diagonal: the looked-up ones from the
  masks, the others in the genome (`supAt_spec`).
* A hit none of whose clean seeds was looked up costs at least `4·|J|`
  (`same_lower_J`, `gap_lower`), which is the stopping rule.
-/

namespace MapSpec.Fast

open MapSpec

/-! ## Anchor arrays for a partial set of seeds -/

structure AnchorsM (m : Nat → Nat) (as : Array Nat) : Prop where
  lt : ∀ A, m A < 16
  sorted : SortedA as.toList
  mem : ∀ e ∈ as.toList, e % 16 = m (e / 16) ∧ 0 < e % 16
  complete : ∀ A, m A ≠ 0 → A * 16 + m A ∈ as.toList

/-- Bit `j` of `J`. -/
abbrev bit (J j : Nat) : Nat := J / 2 ^ j % 2

/-- The seeds of `J` that occur on diagonal `A`. -/
def maskJ (G R : ByteArray) (J A : Nat) : Nat :=
  (if bit J 0 = 1 then seedBit G R 0 A else 0) + (if bit J 1 = 1 then seedBit G R 1 A else 0) +
    (if bit J 2 = 1 then seedBit G R 2 A else 0) + (if bit J 3 = 1 then seedBit G R 3 A else 0)

theorem seedBit_cases (G R : ByteArray) (j A : Nat) : seedBit G R j A = 0 ∨ seedBit G R j A = 2 ^ j := by
  unfold seedBit; split <;> simp

theorem maskJ_lt (G R : ByteArray) (J A : Nat) : maskJ G R J A < 16 := by
  unfold maskJ
  rcases seedBit_cases G R 0 A with h0 | h0 <;> rcases seedBit_cases G R 1 A with h1 | h1 <;>
    rcases seedBit_cases G R 2 A with h2 | h2 <;> rcases seedBit_cases G R 3 A with h3 | h3 <;>
    simp only [h0, h1, h2, h3] <;> split <;> split <;> split <;> split <;> decide

theorem maskJ_full (G R : ByteArray) (A : Nat) : maskJ G R 15 A = maskAt G R A := by
  unfold maskJ maskAt; simp

theorem anchorsM_init (G R : ByteArray) : AnchorsM (maskJ G R 0) #[] :=
  ⟨maskJ_lt G R 0, by simp [SortedA], by simp, fun A h => by simp [maskJ] at h⟩

theorem mv_anchors (m : Nat → Nat) (as : Array Nat) (h : AnchorsM m as) (A : Nat) : mv as.toList A = m A := by
  by_cases hex : ∃ e ∈ as.toList, e / 16 = A
  · obtain ⟨e, he, rfl⟩ := hex
    rw [mv_of_mem _ h.sorted e he, (h.mem e he).1]
  · rw [mv_zero _ _ (fun e he h' => hex ⟨e, he, h'⟩)]
    by_cases hA : m A = 0
    · exact hA.symm
    · exact absurd ⟨_, h.complete A hA, by have := h.lt A; omega⟩ hex

theorem anchorsM_of (m : Nat → Nat) (l : Array Nat) (hlt : ∀ A, m A < 16) (hs : SortedA l.toList)
    (hpos : ∀ e ∈ l.toList, 0 < e % 16) (hmv : ∀ A, mv l.toList A = m A) : AnchorsM m l := by
  refine ⟨hlt, hs, fun e he => ⟨?_, hpos e he⟩, fun A hA => ?_⟩
  · rw [← hmv, mv_of_mem _ hs e he]
  · by_cases hex : ∃ e ∈ l.toList, e / 16 = A
    · obtain ⟨e, he, heA⟩ := hex
      have := mv_of_mem _ hs e he
      rw [hmv, heA] at this
      rw [show A * 16 + m A = e by omega]; exact he
    · exfalso; apply hA
      rw [← hmv]; exact mv_zero _ _ (fun e he h => hex ⟨e, he, h⟩)

theorem bit_add_all : ∀ J, J < 16 → ∀ j, j < 4 → ∀ i, i < 4 → bit J j = 0 →
    bit (J + 2 ^ j) i = if i = j then 1 else bit J i := by decide

theorem bit_add (J j i : Nat) (hj : j < 4) (hi : i < 4) (hJ : J < 16) (h0 : bit J j = 0) :
    bit (J + 2 ^ j) i = if i = j then 1 else bit J i := bit_add_all J hJ j hj i hi h0

theorem maskJ_add (G R : ByteArray) (J j A : Nat) (hj : j < 4) (hJ : J < 16) (h0 : bit J j = 0) :
    maskJ G R (J + 2 ^ j) A = maskJ G R J A + seedBit G R j A := by
  have e := fun i (hi : i < 4) => bit_add J j i hj hi hJ h0
  unfold maskJ
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [h0]; simp only [if_true, if_false, show (1 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
      show (3 : Nat) ≠ 0 by omega, show (0 : Nat) ≠ 1 by omega]; omega
  · rw [h0]; simp only [if_true, if_false, show (0 : Nat) ≠ 1 by omega, show (2 : Nat) ≠ 1 by omega,
      show (3 : Nat) ≠ 1 by omega]; omega
  · rw [h0]; simp only [if_true, if_false, show (0 : Nat) ≠ 2 by omega, show (1 : Nat) ≠ 2 by omega,
      show (3 : Nat) ≠ 2 by omega, show (0 : Nat) ≠ 1 by omega]; omega
  · rw [h0]; simp only [if_true, if_false, show (0 : Nat) ≠ 3 by omega, show (1 : Nat) ≠ 3 by omega,
      show (2 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 1 by omega]; omega

/-- **Adding a seed.**  Merging seed `j`'s anchors into the anchors of `J`. -/
theorem merge_step (ix : HIdx) (G R : ByteArray) (hchk : checkIdx ix G = true) (J j : Nat) (as : Array Nat)
    (h : AnchorsM (maskJ G R J) as) (hj : j < 4) (hJ : J < 16) (h0 : bit J j = 0) :
    AnchorsM (maskJ G R (J + 2 ^ j)) (merge as (lookupSeed ix G R j) 0 0 #[]) := by
  obtain ⟨s1, r1, m1⟩ := single_spec ix G R j (by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
    (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide) hchk
  have hm : ∀ A, maskJ G R (J + 2 ^ j) A = maskJ G R J A + seedBit G R j A :=
    fun A => maskJ_add G R J j A hj hJ h0
  have hf : Fits as.toList (lookupSeed ix G R j).toList := by
    intro a ha b hb hab
    rw [(h.mem a ha).1, r1 b hb, hab]
    have := maskJ_lt G R (J + 2 ^ j) (b / 16)
    rw [hm] at this
    have := m1 (b / 16)
    rw [mv_of_mem _ s1 b hb, r1 b hb] at this
    omega
  obtain ⟨hs, hmv⟩ := lmerge_spec _ _ h.sorted s1 hf
  have hpos := lmerge_pos _ _ (fun e he => (h.mem e he).2) (fun e he => by rw [r1 e he]; exact Nat.pow_pos (by omega)) hf
  rw [← merge_list] at hs hpos
  apply anchorsM_of _ _ (maskJ_lt G R _) hs hpos
  intro A
  rw [merge_list] at *
  rw [hmv, mv_anchors _ _ h, m1, hm]

/-! ## New anchors -/

def lnew : List Nat → List Nat → List Nat
  | _, [] => []
  | [], b :: ys => b :: lnew [] ys
  | a :: xs, b :: ys =>
    if a / 16 < b / 16 then lnew xs (b :: ys)
    else if (a / 16 == b / 16) = true then lnew xs ys
    else b :: lnew (a :: xs) ys
termination_by xs ys => xs.length + ys.length

theorem newOnly_toList (x y : Array Nat) :
    ∀ d i j acc, (x.size - i) + (y.size - j) = d →
      (newOnly x y i j acc).toList = acc.toList ++ lnew (x.toList.drop i) (y.toList.drop j) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro i j acc hd
  unfold newOnly
  by_cases hj : j < y.size
  · rw [dif_pos hj, drop_cons_arr y j hj]
    by_cases hi : i < x.size
    · rw [dif_pos hi, drop_cons_arr x i hi, lnew]
      split
      · rw [ih _ (by omega) (i + 1) j _ rfl, drop_cons_arr y j hj]
      · split
        · rw [ih _ (by omega) (i + 1) (j + 1) _ rfl]
        · rw [ih _ (by omega) i (j + 1) _ rfl, Array.toList_push, List.append_assoc, drop_cons_arr x i hi]; rfl
    · rw [dif_neg hi, drop_nil_arr x i (by omega), ih _ (by omega) i (j + 1) _ rfl, Array.toList_push,
        List.append_assoc, drop_nil_arr x i (by omega)]
      simp [lnew]
  · rw [dif_neg hj, drop_nil_arr y j (by omega)]
    cases x.toList.drop i <;> simp [lnew]

theorem lnew_sub (xs ys : List Nat) : ∀ e ∈ lnew xs ys, e ∈ ys := by
  induction xs, ys using lnew.induct with
  | case1 xs => simp [lnew]
  | case2 b ys ih => intro e he; rw [lnew] at he; rcases List.mem_cons.mp he with rfl | he
                     · simp
                     · exact List.mem_cons_of_mem _ (ih e he)
  | case3 a xs b ys h ih => intro e he; rw [lnew, if_pos h] at he; exact ih e he
  | case4 a xs b ys h h' ih => intro e he; rw [lnew, if_neg h, if_pos h'] at he; exact List.mem_cons_of_mem _ (ih e he)
  | case5 a xs b ys h h' ih =>
    intro e he; rw [lnew, if_neg h, if_neg h'] at he
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · exact List.mem_cons_of_mem _ (ih e he)

theorem lnew_complete (xs ys : List Nat) : ∀ e ∈ ys, (∀ a ∈ xs, a / 16 ≠ e / 16) → e ∈ lnew xs ys := by
  induction xs, ys using lnew.induct with
  | case1 xs => simp
  | case2 b ys ih =>
    intro e he _; rw [lnew]
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · exact List.mem_cons_of_mem _ (ih e he (by simp))
  | case3 a xs b ys h ih =>
    intro e he hn; rw [lnew, if_pos h]; exact ih e he (fun a' ha' => hn a' (List.mem_cons_of_mem _ ha'))
  | case4 a xs b ys h h' ih =>
    intro e he hn; rw [lnew, if_neg h, if_pos h']
    rcases List.mem_cons.mp he with rfl | he
    · exact absurd (by simpa using h') (hn a List.mem_cons_self)
    · exact ih e he (fun a' ha' => hn a' (List.mem_cons_of_mem _ ha'))
  | case5 a xs b ys h h' ih =>
    intro e he hn; rw [lnew, if_neg h, if_neg h']
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · exact List.mem_cons_of_mem _ (ih e he hn)

theorem newOnly_spec (x y : Array Nat) :
    (∀ e ∈ (newOnly x y 0 0 #[]).toList, e ∈ y.toList) ∧
    (∀ e ∈ y.toList, (∀ a ∈ x.toList, a / 16 ≠ e / 16) → e ∈ (newOnly x y 0 0 #[]).toList) := by
  rw [newOnly_toList x y _ 0 0 #[] rfl]
  simp only [List.drop_zero, show (#[] : Array Nat).toList = [] from rfl, List.nil_append]
  exact ⟨lnew_sub _ _, lnew_complete _ _⟩

/-! ## Supports -/

theorem supNearM_spec (m : Nat → Nat) (as : Array Nat) (h : AnchorsM m as) (i A : Nat) (hi : i < as.size)
    (h1 : A ≤ as[i]! / 16 + 3) (h2 : as[i]! / 16 ≤ A + 3) : supNear as i A = pop4 (m A) := by
  unfold supNear
  by_cases hA : m A = 0
  · rw [hA, supScan_none as A _ _ _ rfl]
    · rfl
    intro k' _ hk' he
    have hm := h.mem as[k']! (by rw [getElem!_pos as k' (by omega)]; exact Array.getElem_mem_toList _)
    rw [he, hA] at hm; omega
  · have hmem := h.complete A hA
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hmem
    simp only [Array.length_toList] at hk
    simp only [Array.getElem_toList] at hke
    have hkA : as[k]! / 16 = A := by
      rw [getElem!_pos as k hk, hke]; have := h.lt A; omega
    have hclose : i - min i 3 ≤ k ∧ k < min as.size (i + 4) := by
      by_cases hki : i ≤ k
      · have := sorted_gap as h.sorted (k - i) i (by omega)
        rw [show i + (k - i) = k by omega] at this
        omega
      · have := sorted_gap as h.sorted (i - k) k (by omega)
        rw [show k + (i - k) = i by omega] at this
        omega
    apply supScan_found as A _ _ _ _ rfl ⟨k, hclose.1, hclose.2, hkA⟩
    intro k' _ hk' he
    have hm := h.mem as[k']! (by rw [getElem!_pos as k' (by omega)]; exact Array.getElem_mem_toList _)
    rw [he] at hm; rw [hm.1]

theorem seedOn_spec (G R : ByteArray) (looked j A : Nat) (hj : j < 4) :
    seedOn G R looked j A = if bit looked j = 0 ∧ seedBit G R j A ≠ 0 then 1 else 0 := by
  unfold seedOn
  have hjq : j * q ≤ BIAS := by simp [q, BIAS]; omega
  have hsb := seedBit_ne G R j A
  have hshift : looked >>> j % 2 = bit looked j := by rw [Nat.shiftRight_eq_div_pow]
  by_cases hc : (looked >>> j % 2 == 0 && decide (BIAS ≤ A + j * q) && decide (A + j * q - BIAS + q ≤ G.size) &&
      eqRun G R (A + j * q - BIAS) (j * q) q) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hshift] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    rw [if_pos ⟨h1, hsb.2 ⟨by omega, by rw [show A - (BIAS - j * q) = A + j * q - BIAS by omega]; exact
      ⟨h3, (eqRun_spec G R q _ _).1 h4⟩⟩⟩]
  · rw [if_neg hc]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    obtain ⟨hd, hf, hm⟩ := hsb.1 h2
    rw [show A - (BIAS - j * q) = A + j * q - BIAS by omega] at hf hm
    apply hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hshift]
    exact ⟨⟨⟨h1, by omega⟩, hf⟩, (eqRun_spec G R q _ _).2 hm⟩

theorem term01 (G R : ByteArray) (J j A : Nat) :
    (if bit J j = 1 then seedBit G R j A else 0) = (if bit J j = 1 ∧ seedBit G R j A ≠ 0 then 1 else 0) * 2 ^ j := by
  rcases seedBit_cases G R j A with h | h <;> rw [h] <;> split <;> split <;> simp_all

theorem ite01' (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by split <;> omega

/-- **Support.**  `supAt` is the number of seeds clean on the diagonal. -/
theorem supAt_spec (G R : ByteArray) (J : Nat) (as : Array Nat) (h : AnchorsM (maskJ G R J) as) (i A : Nat)
    (hi : i < as.size) (h1 : A ≤ as[i]! / 16 + 3) (h2 : as[i]! / 16 ≤ A + 3) :
    supAt G R as J i A = pop4 (maskAt G R A) := by
  unfold supAt
  rw [supNearM_spec _ as h i A hi h1 h2, seedOn_spec G R J 0 A (by omega), seedOn_spec G R J 1 A (by omega),
    seedOn_spec G R J 2 A (by omega), seedOn_spec G R J 3 A (by omega), pop4_maskAt]
  unfold maskJ
  rw [term01, term01, term01, term01]
  have hb : ∀ x : Nat, x % 2 = 0 ∨ x % 2 = 1 := fun x => by omega
  simp only [bit, Nat.pow_zero, Nat.div_one, Nat.reducePow]
  by_cases e0 : seedBit G R 0 A = 0 <;> by_cases e1 : seedBit G R 1 A = 0 <;>
    by_cases e2 : seedBit G R 2 A = 0 <;> by_cases e3 : seedBit G R 3 A = 0 <;>
    rcases hb J with r0 | r0 <;> rcases hb (J / 2) with r1 | r1 <;>
    rcases hb (J / 4) with r2 | r2 <;> rcases hb (J / 8) with r3 | r3 <;>
    simp [e0, e1, e2, e3, r0, r1, r2, r3, pop4]

/-- The loop state after `K` lookups (seeds `J`). -/
structure LoopState (cw : Window → Nat) (R G : ByteArray) (c : Nat) (J K : Nat) (as : Array Nat) (b : Best) (S : Window → Prop) : Prop where
  inv : Inv cw S b
  anchors : AnchorsM (maskJ G R J) as
  hJ : J < 16
  card : pop4 J = K
  same : ∀ st, maskJ G R J (st + BIAS) ≠ 0 → S ⟨c, st, R.size⟩
  gap : 3 ≤ K → b.pen < 8 ∨ ∀ st len, len ≠ R.size → cw ⟨c, st, len⟩ ≤ 12 →
    (maskJ G R J (st + BIAS) ≠ 0 ∨ maskJ G R J (st + len + BIAS - R.size) ≠ 0) → S ⟨c, st, len⟩

theorem maskJ_zero (G R : ByteArray) (J A : Nat) (h : maskJ G R J A = 0) : ∀ j, j < 4 → bit J j = 1 → seedBit G R j A = 0 := by
  intro j hj hb
  unfold maskJ at h
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [hb, if_true] at h <;> omega

theorem anchorM_index (m : Nat → Nat) (as : Array Nat) (ha : AnchorsM m as) (A : Nat) (hA : m A ≠ 0) :
    ∃ i, i < as.size ∧ as[i]! / 16 = A := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (ha.complete A hA)
  simp only [Array.length_toList] at hi
  refine ⟨i, hi, ?_⟩
  rw [getElem!_pos as i hi, ← Array.getElem_toList (by simpa using hi), he]
  have := ha.lt A; omega

theorem pop4_full (J : Nat) (hJ : J < 16) (h : pop4 J = 4) : J = 15 := by
  have : ∀ J, J < 16 → pop4 J = 4 → J = 15 := by decide
  exact this J hJ h

theorem pop4_add : ∀ J, J < 16 → ∀ j, j < 4 → bit J j = 0 → pop4 (J + 2 ^ j) = pop4 J + 1 ∧ J + 2 ^ j < 16 := by
  decide

theorem bit_pow : ∀ j, j < 4 → ∀ i, i < 4 → bit (2 ^ j) i = 1 → i = j := by decide

theorem seedHashes_get (R : ByteArray) (j : Nat) (hj : j < 4) : (seedHashes R)[j]! = seedHash R j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem insKey_perm (key : Nat → Nat) (x : Nat) (l : List Nat) : (insKey key x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insKey]
  | cons y ys ih =>
    unfold insKey
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem seedOrder_spec (ix : HIdx) (hs : Array (Option UInt64)) :
    (seedOrder ix hs).Nodup ∧ (∀ j ∈ seedOrder ix hs, j < 4) ∧ (seedOrder ix hs).length = 4 := by
  unfold seedOrder
  simp only []
  generalize (fun j => if j = 0 then sizeH ix hs[0]! else if j = 1 then sizeH ix hs[1]! else
    if j = 2 then sizeH ix hs[2]! else sizeH ix hs[3]!) = key
  have hp : (insKey key 3 (insKey key 2 (insKey key 1 [0]))).Perm [3, 2, 1, 0] :=
    (insKey_perm key 3 _).trans (((insKey_perm key 2 _).trans ((insKey_perm key 1 _).cons 2)).cons 3)
  refine ⟨hp.nodup_iff.mpr (by decide), fun j hj => ?_, by rw [hp.length_eq]; rfl⟩
  have := hp.mem_iff.mp hj
  simp at this; omega

/-! ## The steps keep the invariant -/

section chrom

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (R G : ByteArray) (c : Nat)
  (hcw : ∀ st len, cw ⟨c, st, len⟩ = penB R G st len) (hn : 100 ≤ R.size)

include hc13 hcw hn

/-- Same-length window of an anchor whose mask bits are clean seeds. -/
theorem sameStep2_inv (e : Nat) (hsound : ∀ j, j < 4 → bit (e % 16) j = 1 → seedBit G R j (e / 16) ≠ 0)
    (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    Inv cw (fun w => S w ∨ (BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩)) (sameStep2 R G c b e) := by
  unfold sameStep2
  simp only []
  by_cases hcond : (decide (BIAS ≤ e / 16) && decide (e / 16 - BIAS + R.size ≤ G.size) && !(b.pen == 0 && b.amb)) = true
  · rw [if_pos hcond]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq] at hcond
    obtain ⟨⟨hA, hfit⟩, -⟩ := hcond
    have hst : e / 16 - BIAS + BIAS = e / 16 := by omega
    have cl : ∀ j, j < 4 → bit (e % 16) j = 1 → hc R G (e / 16 - BIAS) (j * q) q = 0 := by
      intro j hj hb
      have := hsound j hj hb
      rw [← hst] at this
      exact (seedBit_start G R (e / 16 - BIAS) j hj (by simp [q]; omega)).1 this
    have c0 := cl 0 (by omega); have c1 := cl 1 (by omega); have c2 := cl 2 (by omega); have c3 := cl 3 (by omega)
    simp only [bit, q, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul, Nat.zero_mul] at c0 c1 c2 c3
    rw [hamSeeds_spec R G _ _ _ (by simp [q]; omega) c0 c1 c2 c3]
    have hcwv : cw ⟨c, e / 16 - BIAS, R.size⟩ = penSame R G (e / 16 - BIAS) := by
      rw [hcw]; unfold penB; rw [if_pos hfit, if_pos rfl]
    have hle := h.le13
    unfold penSame at hcwv
    generalize preB R G (e / 16 - BIAS) R.size = H at *
    have hcw' : (H ≤ 3 ∧ cw ⟨c, e / 16 - BIAS, R.size⟩ = 4 * H) ∨
        (3 < H ∧ cw ⟨c, e / 16 - BIAS, R.size⟩ = 13) := by
      rw [hcwv]; split
      · left; omega
      · right; omega
    have hcap : cap = 12 := rfl
    by_cases h4 : 4 * min H (min 3 (b.pen / 4) + 1) ≤ cap
    · rw [if_pos h4]
      apply inv_congr cw _ _ _ (inv_add cw hc13 S b h c _ _ _ (by omega))
      intro w; simp only [hA, true_and]
    · rw [if_neg h4]
      apply inv_skip' cw hc13 S (fun w => w = ⟨c, e / 16 - BIAS, R.size⟩) b h
      · intro w hw; subst hw; unfold Dom; right; left; omega
      · intro w; simp only [hA, true_and]
  · rw [if_neg hcond]
    apply inv_skip' cw hc13 S (fun w => BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩) b h
    · rintro w ⟨hA, rfl⟩
      unfold Dom
      by_cases hfit : e / 16 - BIAS + R.size ≤ G.size
      · have hab : b.pen = 0 ∧ b.amb = true := by
          apply Classical.byContradiction
          intro hn'
          apply hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
            beq_eq_false_iff_ne, ne_eq]
          refine ⟨⟨hA, hfit⟩, ?_⟩
          by_cases hp : b.pen = 0
          · right; cases ha : b.amb
            · rfl
            · exact absurd ⟨hp, ha⟩ hn'
          · left; exact hp
        by_cases h0 : cw ⟨c, e / 16 - BIAS, R.size⟩ = 0
        · right; right; exact ⟨by omega, Or.inl hab.2⟩
        · left; omega
      · right; left; rw [hcw]; unfold penB; rw [if_neg hfit]
    · intro w; rfl

theorem gapL2_inv (J : Nat) (as : Array Nat) (ha : AnchorsM (maskJ G R J) as) (i : Nat) (hi : i < as.size)
    (L : Nat) (hL1 : 1 ≤ L) (hL3 : L ≤ 3) (cs : Nat) (hcs : cs = pop4 (maskAt G R (as[i]! / 16)))
    (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    Inv cw (fun w => S w ∨ GapL c R.size as i L w) (gapL2 R G c as J i (as[i]! / 16) cs L b) := by
  generalize hA : as[i]! / 16 = A at *
  have hsp : supAt G R as J i (A + L) = pop4 (maskAt G R (A + L)) :=
    supAt_spec G R J as ha i (A + L) hi (by omega) (by omega)
  have hsm : A ≥ L → supAt G R as J i (A - L) = pop4 (maskAt G R (A - L)) := fun hAL =>
    supAt_spec G R J as ha i (A - L) hi (by omega) (by omega)
  have gl : ∀ len, (len = R.size + L ∨ len + L = R.size) → len ≠ R.size ∧ gapLen R.size len ≤ 3 := by
    intro len hl; unfold gapLen; constructor <;> (try split) <;> omega
  unfold gapL2
  simp only []
  subst hcs
  have w1 := gapW_inv cw hc13 R G c hcw hn S b h (A - BIAS) (R.size + L)
    (pop4 (maskAt G R A) + supAt G R as J i (A + L)) (decide (BIAS ≤ A))
    (gl _ (Or.inl rfl)).1 (gl _ (Or.inl rfl)).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ A (A + L) _ hfit (gl _ (Or.inl rfl)).1
        (gl _ (Or.inl rfl)).2 hp (by omega) (by omega) (by rw [hsp]))
  have w2 := gapW_inv cw hc13 R G c hcw hn _ _ w1 (A - BIAS) (R.size - L)
    (pop4 (maskAt G R A) + supAt G R as J i (A - L)) (decide (BIAS ≤ A))
    (gl _ (Or.inr (by omega))).1 (gl _ (Or.inr (by omega))).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ A (A - L) _ hfit (gl _ (Or.inr (by omega))).1
        (gl _ (Or.inr (by omega))).2 hp (by omega) (by omega) (by rw [hsm (by simp [BIAS] at hok; omega)]))
  have w3 := gapW_inv cw hc13 R G c hcw hn _ _ w2 (A - L - BIAS) (R.size + L)
    (pop4 (maskAt G R A) + supAt G R as J i (A - L)) (decide (BIAS + L ≤ A))
    (gl _ (Or.inl rfl)).1 (gl _ (Or.inl rfl)).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ (A - L) A _ hfit (gl _ (Or.inl rfl)).1
        (gl _ (Or.inl rfl)).2 hp (by omega) (by omega) (by rw [hsm (by omega), Nat.add_comm]))
  have w4 := gapW_inv cw hc13 R G c hcw hn _ _ w3 (A + L - BIAS) (R.size - L)
    (pop4 (maskAt G R A) + supAt G R as J i (A + L)) (decide (BIAS ≤ A + L))
    (gl _ (Or.inr (by omega))).1 (gl _ (Or.inr (by omega))).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ (A + L) A _ hfit (gl _ (Or.inr (by omega))).1
        (gl _ (Or.inr (by omega))).2 hp (by omega) (by simp [BIAS] at hok ⊢; omega) (by rw [hsp, Nat.add_comm]))
  apply inv_congr cw _ _ _ w4
  intro w
  unfold GapL
  rw [hA]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem gapAll2_inv (J : Nat) (as : Array Nat) (ha : AnchorsM (maskJ G R J) as) :
    ∀ k i S b, i + k ≤ as.size → Inv cw S b →
      Inv cw (fun w => S w ∨ ∃ i', i ≤ i' ∧ i' < i + k ∧ ∃ L, 1 ≤ L ∧ L ≤ 3 ∧ GapL c R.size as i' L w)
        (gapAll2 R G c as J k i b) := by
  intro k
  induction k with
  | zero => intro i S b _ h; exact inv_congr cw _ _ _ h (fun w => by simp; omega)
  | succ k ih =>
    intro i S b hk h
    unfold gapAll2
    simp only []
    have hcs : supAt G R as J i (as[i]! / 16) = pop4 (maskAt G R (as[i]! / 16)) :=
      supAt_spec G R J as ha i _ (by omega) (by omega) (by omega)
    have g1 := gapL2_inv cw hc13 R G c hcw hn J as ha i (by omega) 1 (by omega) (by omega) _ hcs S b h
    have g2 := gapL2_inv cw hc13 R G c hcw hn J as ha i (by omega) 2 (by omega) (by omega) _ hcs _ _ g1
    have g3 := gapL2_inv cw hc13 R G c hcw hn J as ha i (by omega) 3 (by omega) (by omega) _ hcs _ _ g2
    have := ih (i + 1) _ _ (by omega) g3
    apply inv_congr cw _ _ _ this
    intro w
    constructor
    · rintro ((((h0 | h1) | h2) | h3) | ⟨i', h1', h2', L, hL⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨i, by omega, by omega, 1, by omega, by omega, h1⟩
      · exact Or.inr ⟨i, by omega, by omega, 2, by omega, by omega, h2⟩
      · exact Or.inr ⟨i, by omega, by omega, 3, by omega, by omega, h3⟩
      · exact Or.inr ⟨i', by omega, by omega, L, hL⟩
    · rintro (h0 | ⟨i', h1', h2', L, hL1, hL3, hg⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h0)))
      · by_cases hi : i' = i
        · subst hi
          rcases (show L = 1 ∨ L = 2 ∨ L = 3 by omega) with rfl | rfl | rfl
          · exact Or.inl (Or.inl (Or.inl (Or.inr hg)))
          · exact Or.inl (Or.inl (Or.inr hg))
          · exact Or.inl (Or.inr hg)
        · exact Or.inr ⟨i', by omega, by omega, L, hL1, hL3, hg⟩

/-- A one-gap window with a looked-up clean seed is one of the windows of an anchor. -/
theorem gap_coverM (J : Nat) (as : Array Nat) (ha : AnchorsM (maskJ G R J) as) (st len : Nat)
    (hne : len ≠ R.size) (h : cw ⟨c, st, len⟩ ≤ 12)
    (hm : maskJ G R J (st + BIAS) ≠ 0 ∨ maskJ G R J (st + len + BIAS - R.size) ≠ 0) :
    ∃ i, i < as.size ∧ ∃ L, 1 ≤ L ∧ L ≤ 3 ∧ GapL c R.size as i L ⟨c, st, len⟩ := by
  rw [hcw] at h
  unfold penB at h
  split at h
  · next hfit =>
    split at h
    · next hL =>
      have hL1 : 1 ≤ gapLen R.size len := by unfold gapLen; split <;> omega
      have hgl : (len = R.size + gapLen R.size len) ∨ (len + gapLen R.size len = R.size) := by
        unfold gapLen; split <;> omega
      generalize gapLen R.size len = L at *
      rcases hm with h1 | h2
      · obtain ⟨i, hi, hA⟩ := anchorM_index _ as ha _ h1
        refine ⟨i, hi, L, hL1, hL, ?_⟩
        unfold GapL; rw [hA]; simp only [BIAS] at *
        rcases hgl with e | e
        · left; refine ⟨by omega, ?_⟩; simp; omega
        · right; left; refine ⟨by omega, ?_⟩; simp; omega
      · obtain ⟨i, hi, hA⟩ := anchorM_index _ as ha _ h2
        refine ⟨i, hi, L, hL1, hL, ?_⟩
        unfold GapL; rw [hA]; simp only [BIAS] at *
        rcases hgl with e | e
        · right; right; left; refine ⟨by omega, ?_⟩; simp; omega
        · right; right; right; refine ⟨by omega, ?_⟩; simp; constructor <;> omega
    · omega
  · omega

/-- **Stopping.**  With the best below `4K`, or all seeds looked up, every hit was
looked at or cannot change the result. -/
theorem finish (J K : Nat) (as : Array Nat) (b : Best) (S : Window → Prop) (hs : LoopState cw R G c J K as b S)
    (hstop : b.pen < 4 * K ∨ J = 15) :
    ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧ ∀ st len, cw ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩ := by
  have hK : K ≤ 4 := by rw [← hs.card]; unfold pop4; omega
  have hJK : J = 15 → K = 4 := by intro e; rw [← hs.card, e]; rfl
  refine ⟨_, inv_skip cw hc13 S (fun w => w.chr = c ∧ cw w ≤ 12 ∧ ¬ S w) b hs.inv ?_, fun w hw => Or.inl hw,
    fun st len hw => ?_⟩
  · rintro ⟨c', st, len⟩ ⟨hc', hhit, hnS⟩
    simp only at hc'
    subst c'
    have hle := hs.inv.le13
    unfold Dom
    by_cases hlen : len = R.size
    · subst hlen
      have hpb := hhit
      rw [hcw] at hpb
      unfold penB at hpb
      split at hpb
      · next hfit =>
        rw [if_pos rfl] at hpb
        by_cases hm : maskJ G R J (st + BIAS) = 0
        · have hl := same_lower_J R G st hn hfit J (maskJ_zero G R J _ hm)
          rcases hstop with hp | hJ15
          · left; rw [hcw]; unfold penB; rw [if_pos hfit, if_pos rfl]; unfold penSame at hpb ⊢
            rw [hs.card] at hl; split <;> split at hpb <;> omega
          · subst hJ15; rw [maskJ_full] at hm
            exact absurd hm (same_hit_mask R G st hn hfit hpb)
        · exact absurd (hs.same st hm) hnS
      · omega
    · have h8 := penB_gap_ge R G st len hlen
      rw [← hcw] at h8
      have hpb := hhit
      rw [hcw] at hpb
      unfold penB at hpb
      split at hpb
      · next hfit =>
        split at hpb
        · next hL =>
          by_cases hm : maskJ G R J (st + BIAS) = 0 ∧ maskJ G R J (st + len + BIAS - R.size) = 0
          · rcases hstop with hp | hJ15
            · have := gap_lower R G st len hn hfit hlen hL hpb J (fun j hj hb =>
                ⟨maskJ_zero G R J _ hm.1 j hj hb, maskJ_zero G R J _ hm.2 j hj hb⟩)
              left; rw [hcw]; unfold penB; rw [if_pos hfit, if_neg hlen, if_pos hL]; rw [hs.card] at this; omega
            · subst hJ15; rw [maskJ_full, maskJ_full] at hm
              have := gap_support R G st len hn hfit hlen hL hpb
              rw [hm.1, hm.2] at this; simp [pop4] at this; split at this <;> omega
          · have hm' : maskJ G R J (st + BIAS) ≠ 0 ∨ maskJ G R J (st + len + BIAS - R.size) ≠ 0 := by
              by_cases h1 : maskJ G R J (st + BIAS) = 0
              · exact Or.inr (fun h2 => hm ⟨h1, h2⟩)
              · exact Or.inl h1
            by_cases h3 : 3 ≤ K
            · rcases hs.gap h3 with hp | hcov
              · left; omega
              · exact absurd (hcov st len hlen hhit hm') hnS
            · rcases hstop with hp | hJ15
              · left; omega
              · omega
        · omega
      · omega
  · by_cases hS : S ⟨c, st, len⟩
    · exact Or.inl hS
    · exact Or.inr ⟨rfl, hw, hS⟩

theorem lookupH_eq (ix : HIdx) (j : Nat) (hj : j < 4) :
    lookupH ix G R j (seedHashes R)[j]! = lookupSeed ix G R j := by
  rw [seedHashes_get R j hj]; rfl

/-- **The lazy loop.** -/
theorem lazyLoop_inv (ix : HIdx) (hchk : checkIdx ix G = true) :
    ∀ (ord : List Nat) (J : Nat) (as : Array Nat) (b : Best) (S : Window → Prop),
      LoopState cw R G c J (pop4 J) as b S → ord.Nodup → (∀ j ∈ ord, j < 4 ∧ bit J j = 0) →
      pop4 J + ord.length = 4 →
      ∃ S', Inv cw S' (lazyLoop R G c ix (seedHashes R) ord (pop4 J) as J b) ∧ (∀ w, S w → S' w) ∧
        ∀ st len, cw ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩ := by
  intro ord
  induction ord with
  | nil =>
    intro J as b S hs _ _ hlen
    simp only [List.length_nil, Nat.add_zero] at hlen
    exact finish cw hc13 R G c hcw hn J _ as b S hs (Or.inr (pop4_full J hs.hJ hlen))
  | cons j rest ih =>
    intro J as b S hs hnd hord hlen
    obtain ⟨hj4, hj0⟩ := hord j List.mem_cons_self
    obtain ⟨hpop, hJ'⟩ := pop4_add J hs.hJ j hj4 hj0
    unfold lazyLoop
    simp only []
    rw [lookupH_eq cw hc13 R G c hcw hn ix j hj4, Nat.one_shiftLeft]
    -- the new anchors
    obtain ⟨s1, r1, m1⟩ := single_spec ix G R j (by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
      (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide) hchk
    have ha' := merge_step ix G R hchk J j as hs.anchors hj4 hs.hJ hj0
    obtain ⟨nsub, ncomp⟩ := newOnly_spec as (lookupSeed ix G R j)
    -- same-length windows of the new anchors
    have hsound : ∀ e ∈ (newOnly as (lookupSeed ix G R j) 0 0 #[]).toList,
        ∀ j', j' < 4 → bit (e % 16) j' = 1 → seedBit G R j' (e / 16) ≠ 0 := by
      intro e he j' hj' hb
      have hel := nsub e he
      rw [r1 e hel] at hb
      have := bit_pow j hj4 j' hj' hb
      subst this
      have := m1 (e / 16)
      rw [mv_of_mem _ s1 e hel, r1 e hel] at this
      rw [← this]; exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))
    have f1 := foldl_inv cw (sameStep2 R G c) (fun e w => BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩)
      (fun e => e ∈ (newOnly as (lookupSeed ix G R j) 0 0 #[]).toList)
      (fun e he S b h => sameStep2_inv cw hc13 R G c hcw hn e (hsound e he) S b h)
      (newOnly as (lookupSeed ix G R j) 0 0 #[]).toList S b (fun e he => he) hs.inv
    rw [Array.foldl_toList] at f1
    generalize (newOnly as (lookupSeed ix G R j) 0 0 #[]).foldl (sameStep2 R G c) b = b1 at f1
    generalize hS1 : (fun w => S w ∨ ∃ e ∈ (newOnly as (lookupSeed ix G R j) 0 0 #[]).toList,
      BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩) = S1 at f1
    have hSS1 : ∀ w, S w → S1 w := by intro w hw; rw [← hS1]; exact Or.inl hw
    have same1 : ∀ st, maskJ G R (J + 2 ^ j) (st + BIAS) ≠ 0 → S1 ⟨c, st, R.size⟩ := by
      intro st hm
      rw [maskJ_add G R J j _ hj4 hs.hJ hj0] at hm
      by_cases h0 : maskJ G R J (st + BIAS) = 0
      · have hsb : seedBit G R j (st + BIAS) ≠ 0 := by omega
        -- the anchor is new
        have hmem : (st + BIAS) * 16 + 2 ^ j ∈ (lookupSeed ix G R j).toList := by
          have hlj : AnchorsM (fun A => seedBit G R j A) (lookupSeed ix G R j) :=
            anchorsM_of _ _ (fun A => by
              rcases seedBit_cases G R j A with h | h <;> rw [h] <;>
              rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
              s1 (fun e he => by rw [r1 e he]; exact Nat.pow_pos (by omega)) m1
          have := hlj.complete _ hsb
          rcases seedBit_cases G R j (st + BIAS) with h | h
          · exact absurd h hsb
          · rwa [h] at this
        have hk : ((st + BIAS) * 16 + 2 ^ j) / 16 = st + BIAS := by
          have : 2 ^ j < 16 := by
            rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
          generalize 2 ^ j = w at this ⊢
          omega
        have hnew := ncomp _ hmem (fun a ha hk' => by
          have := hs.anchors.mem a ha
          rw [hk'] at this
          rw [hk] at this; omega)
        rw [← hS1]
        exact Or.inr ⟨_, hnew, by rw [hk]; omega, by rw [hk]; simp⟩
      · exact hSS1 _ (hs.same st h0)
    -- one-gap windows
    have stage : ∃ S2, Inv cw S2 (if 2 ≤ pop4 J && 8 ≤ b1.pen then
          gapAll2 R G c (merge as (lookupSeed ix G R j) 0 0 #[]) (J + 2 ^ j)
            (merge as (lookupSeed ix G R j) 0 0 #[]).size 0 b1 else b1) ∧
        (∀ w, S1 w → S2 w) ∧
        (3 ≤ pop4 J + 1 → (if 2 ≤ pop4 J && 8 ≤ b1.pen then
          gapAll2 R G c (merge as (lookupSeed ix G R j) 0 0 #[]) (J + 2 ^ j)
            (merge as (lookupSeed ix G R j) 0 0 #[]).size 0 b1 else b1).pen < 8 ∨
          ∀ st len, len ≠ R.size → cw ⟨c, st, len⟩ ≤ 12 →
            (maskJ G R (J + 2 ^ j) (st + BIAS) ≠ 0 ∨ maskJ G R (J + 2 ^ j) (st + len + BIAS - R.size) ≠ 0) →
            S2 ⟨c, st, len⟩) := by
      by_cases hrun : (decide (2 ≤ pop4 J) && decide (8 ≤ b1.pen)) = true
      · rw [if_pos hrun]
        have g := gapAll2_inv cw hc13 R G c hcw hn (J + 2 ^ j) _ ha'
          (merge as (lookupSeed ix G R j) 0 0 #[]).size 0 S1 b1 (by omega) f1
        refine ⟨_, g, fun w hw => Or.inl hw, fun _ => Or.inr fun st len hl hw hm => ?_⟩
        obtain ⟨i, hi, L, hL1, hL3, hg⟩ := gap_coverM cw hc13 R G c hcw hn _ _ ha' st len hl hw hm
        exact Or.inr ⟨i, by omega, by omega, L, hL1, hL3, hg⟩
      · rw [if_neg hrun]
        refine ⟨S1, f1, fun w hw => hw, fun h3 => Or.inl ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hrun
        have := hrun (by omega); omega
    obtain ⟨S2, h2, hS12, hgap2⟩ := stage
    generalize (if 2 ≤ pop4 J && 8 ≤ b1.pen then
          gapAll2 R G c (merge as (lookupSeed ix G R j) 0 0 #[]) (J + 2 ^ j)
            (merge as (lookupSeed ix G R j) 0 0 #[]).size 0 b1 else b1) = b2 at h2 hgap2
    have hst : LoopState cw R G c (J + 2 ^ j) (pop4 J + 1) (merge as (lookupSeed ix G R j) 0 0 #[]) b2 S2 :=
      ⟨h2, ha', hJ', hpop, fun st hm => hS12 _ (same1 st hm), hgap2⟩
    split
    · obtain ⟨S', h', hS', hc'⟩ := finish cw hc13 R G c hcw hn _ _ _ _ _ hst (Or.inl (by omega))
      exact ⟨S', h', fun w hw => hS' w (hS12 w (hSS1 w hw)), hc'⟩
    · rw [← hpop]
      have hnd' := (List.nodup_cons.mp hnd)
      obtain ⟨S', h', hS', hc'⟩ := ih (J + 2 ^ j) _ b2 S2 (by rw [hpop]; exact hst) hnd'.2
        (fun j' hj' => by
          obtain ⟨a1, a2⟩ := hord j' (List.mem_cons_of_mem _ hj')
          refine ⟨a1, ?_⟩
          rw [bit_add J j j' hj4 a1 hs.hJ hj0, if_neg (fun e : j' = j => hnd'.1 (e ▸ hj'))]; exact a2)
        (by simp at hlen; omega)
      exact ⟨S', h', fun w hw => hS' w (hS12 w (hSS1 w hw)), hc'⟩

/-- **One chromosome.**  `mapChrom2` keeps the invariant and looks at every hit of chromosome `c`. -/
theorem mapChrom2_inv (ix : HIdx) (hchk : checkIdx ix G = true) (S : Window → Prop) (b : Best)
    (h : Inv cw S b) : ∃ S', Inv cw S' (mapChrom2 R G c ix b) ∧ (∀ w, S w → S' w) ∧
      (∀ st len, cw ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩) := by
  unfold mapChrom2
  obtain ⟨hnd, hlt, hl⟩ := seedOrder_spec ix (seedHashes R)
  have := lazyLoop_inv cw hc13 R G c hcw hn ix hchk (seedOrder ix (seedHashes R)) 0 #[] b S
    ⟨h, anchorsM_init G R, by omega, rfl, fun st hm => by simp [maskJ] at hm, fun h3 => by simp [pop4] at h3⟩
    hnd (fun j hj => ⟨hlt j hj, by simp [bit]⟩) (by rw [hl]; rfl)
  exact this

end chrom

/-- **All chromosomes.**  `mapChroms` ends with the invariant over a set containing every hit. -/
theorem mapChroms_inv (R : ByteArray) (gbs : Array ByteArray) (idxs : Array HIdx) (hn : 100 ≤ R.size)
    (hchk : ∀ c, c < gbs.size → checkIdx idxs[c]! gbs[c]! = true) :
    ∃ S, Inv (cwG R gbs) S (mapChroms R gbs idxs) ∧ ∀ w, cwG R gbs w ≤ 12 → S w := by
  have step : ∀ (l : List Nat) S b, (∀ c ∈ l, c < gbs.size) → Inv (cwG R gbs) S b →
      ∃ S', Inv (cwG R gbs) S' (l.foldl (fun b c => mapChrom2 R gbs[c]! c idxs[c]! b) b) ∧
        (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ st len, cwG R gbs ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩ := by
    intro l
    induction l with
    | nil => intro S b _ h; exact ⟨S, h, fun w hw => hw, fun c hc => by simp at hc⟩
    | cons c l ih =>
      intro S b hl h
      have hc : c < gbs.size := hl c List.mem_cons_self
      obtain ⟨S1, h1, s1, c1⟩ := mapChrom2_inv (cwG R gbs) (cwG_le R gbs) R gbs[c]! c
        (fun st len => by unfold cwG; simp [hc]) hn idxs[c]! (hchk c hc) S b h
      obtain ⟨S2, h2, s2, c2⟩ := ih S1 _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) h1
      refine ⟨S2, h2, fun w hw => s2 w (s1 w hw), fun c' hc' st len hw => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact s2 _ (c1 st len hw)
      · exact c2 c' hc' st len hw
  obtain ⟨S, h, -, hcov⟩ := step (List.range gbs.size) (fun _ => False) {} (fun c hc => List.mem_range.mp hc)
    (inv_init _ (cwG_le R gbs))
  refine ⟨S, h, fun ⟨c, st, len⟩ hw => ?_⟩
  by_cases hc : c < gbs.size
  · exact hcov c (List.mem_range.mpr hc) st len hw
  · unfold cwG at hw; simp [hc] at hw

end MapSpec.Fast

#print axioms MapSpec.Fast.mapChroms_inv
