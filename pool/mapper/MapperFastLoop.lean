import MapperFastBest
import MapperFastSupport

/-!
The loops of `mapChrom` keep `Inv`, and together look at every hit of the
chromosome (`mapChrom_inv`); over all chromosomes, `mapChroms` looks at every
hit of the genome (`mapChroms_inv`).
-/

namespace MapSpec.Fast

open MapSpec

theorem inv_congr (cw : Window → Nat) (S S' : Window → Prop) (b : Best) (h : Inv cw S b)
    (e : ∀ w, S w ↔ S' w) : Inv cw S' b := by
  have : S = S' := funext fun w => propext (e w)
  subst this; exact h

theorem inv_skip' (cw : Window → Nat) (hc : ∀ w, cw w ≤ 13) (S X : Window → Prop) (b : Best)
    (h : Inv cw S b) (hX : ∀ w, X w → Dom cw b w) (S' : Window → Prop) (e : ∀ w, S' w ↔ S w ∨ X w) :
    Inv cw S' b :=
  inv_congr cw _ _ b (inv_skip cw hc S X b h hX) (fun w => (e w).symm)

theorem foldl_inv {α : Type} (cw : Window → Nat) (f : Best → α → Best) (X : α → Window → Prop)
    (P : α → Prop) (hstep : ∀ a, P a → ∀ S b, Inv cw S b → Inv cw (fun w => S w ∨ X a w) (f b a)) :
    ∀ (l : List α) S b, (∀ a ∈ l, P a) → Inv cw S b →
      Inv cw (fun w => S w ∨ ∃ a ∈ l, X a w) (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro S b _ h; exact inv_congr cw _ _ b h (fun w => by simp)
  | cons a l ih =>
    intro S b hP h
    have := ih _ _ (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')) (hstep a (hP a List.mem_cons_self) S b h)
    exact inv_congr cw _ _ _ this (fun w => by
      simp only [List.mem_cons, exists_eq_or_imp]; exact or_assoc)

theorem pop4_pos (G R : ByteArray) (d : Nat) (h : maskAt G R d ≠ 0) : 1 ≤ pop4 (maskAt G R d) := by
  rw [pop4_maskAt]
  unfold maskAt at h
  split <;> split <;> split <;> split <;> simp_all

theorem pop4_le (m : Nat) : pop4 m ≤ 4 := by unfold pop4; omega

section chrom

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (R G : ByteArray) (c : Nat)
  (hcw : ∀ st len, cw ⟨c, st, len⟩ = penB R G st len) (hn : 100 ≤ R.size)

include hc13 hcw hn

/-! ## Same-length windows -/

theorem sameStep_inv (as : Array Nat) (ha : AnchorsOK G R as) (sup : Nat) (e : Nat) (he : e ∈ as.toList)
    (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    Inv cw (fun w => S w ∨ (pop4 (e % 16) = sup ∧ BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩))
      (sameStep R G c sup b e) := by
  have hm := (ha.mem e he).1
  unfold sameStep
  simp only []
  by_cases hcond : (pop4 (e % 16) == sup && decide (BIAS ≤ e / 16) && decide (e / 16 - BIAS + R.size ≤ G.size)) = true
  · rw [if_pos hcond]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨hsup, hA⟩, hfit⟩ := hcond
    have hst : e / 16 - BIAS + BIAS = e / 16 := by omega
    obtain ⟨c0, c1, c2, c3⟩ := same_clean R G (e / 16 - BIAS) hn hfit
    rw [hst, ← hm] at c0 c1 c2 c3
    rw [hamSeeds_spec R G _ _ _ (by simp [q]; omega) c0 c1 c2 c3]
    have hcwv : cw ⟨c, e / 16 - BIAS, R.size⟩ = penSame R G (e / 16 - BIAS) := by
      rw [hcw]; unfold penB; rw [if_pos hfit, if_pos rfl]
    have hle := h.le13
    unfold penSame at hcwv
    generalize preB R G (e / 16 - BIAS) R.size = H at *
    have hcw' : (H ≤ 3 ∧ cw ⟨c, e / 16 - BIAS, R.size⟩ = 4 * H) ∨ (3 < H ∧ cw ⟨c, e / 16 - BIAS, R.size⟩ = 13) := by
      rw [hcwv]; split
      · left; omega
      · right; omega
    have hcap : cap = 12 := rfl
    by_cases h4 : 4 * min H (min 3 (b.pen / 4) + 1) ≤ cap
    · rw [if_pos h4]
      apply inv_congr cw _ _ _ (inv_add cw hc13 S b h c _ _ _ (by omega))
      intro w; simp only [hsup, hA, true_and]
    · rw [if_neg h4]
      apply inv_skip' cw hc13 S (fun w => w = ⟨c, e / 16 - BIAS, R.size⟩) b h
      · intro w hw; subst hw; unfold Dom; right; left; omega
      · intro w; simp only [hsup, hA, true_and]
  · rw [if_neg hcond]
    apply inv_skip' cw hc13 S (fun w => pop4 (e % 16) = sup ∧ BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩) b h
    · rintro w ⟨hsup, hA, rfl⟩
      unfold Dom; right; left
      rw [hcw]; unfold penB
      rw [if_neg]
      intro hfit; apply hcond
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact ⟨⟨hsup, hA⟩, hfit⟩
    · intro w; rfl

/-- The windows pass `k` looks at. -/
def SameK (c : Nat) (n : Nat) (as : Array Nat) (k : Nat) (w : Window) : Prop :=
  ∃ e ∈ as.toList, pop4 (e % 16) = 4 - k ∧ BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, n⟩

theorem samePass_inv (as : Array Nat) (ha : AnchorsOK G R as) (k : Nat) (hk : k ≤ 4)
    (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    Inv cw (fun w => S w ∨ SameK c R.size as k w) (samePass R G c as k b) := by
  unfold samePass
  split
  · rw [← Array.foldl_toList]
    have := foldl_inv cw (sameStep R G c (4 - k))
      (fun e w => pop4 (e % 16) = 4 - k ∧ BIAS ≤ e / 16 ∧ w = ⟨c, e / 16 - BIAS, R.size⟩)
      (fun e => e ∈ as.toList)
      (fun e he S b h => sameStep_inv cw hc13 R G c hcw hn as ha (4 - k) e he S b h) as.toList S b
      (fun e he => he) h
    exact inv_congr cw _ _ _ this (fun w => by unfold SameK; rfl)
  · next hcond =>
    have hc' : ¬ 4 * k ≤ b.pen ∨ (b.pen = 0 ∧ b.amb = true) := by
      by_cases h1 : 4 * k ≤ b.pen
      · right
        cases ha' : b.amb <;> by_cases h0 : b.pen = 0 <;> simp_all
      · left; exact h1
    apply inv_skip' cw hc13 S (SameK c R.size as k) b h
    · rintro w ⟨e, he, hsup, hA, rfl⟩
      have hm := (ha.mem e he).1
      unfold Dom
      rw [hcw]
      unfold penB
      split
      · next hfit =>
        rw [if_pos rfl]
        have hl := same_lower R G (e / 16 - BIAS) hn hfit
        rw [show e / 16 - BIAS + BIAS = e / 16 by omega, ← hm, hsup] at hl
        unfold penSame
        split
        · rcases hc' with h1 | ⟨h1, h2⟩
          · left; omega
          · by_cases h0 : preB R G (e / 16 - BIAS) R.size = 0
            · right; right; rw [h0, h1]; exact ⟨rfl, Or.inl h2⟩
            · left; omega
        · right; left; rfl
      · right; left; rfl
    · intro w; rfl

/-! ## One-gap windows -/

theorem gapW_inv (S : Window → Prop) (b : Best) (h : Inv cw S b) (st len s : Nat) (ok : Bool)
    (hne : len ≠ R.size) (hL : gapLen R.size len ≤ 3)
    (hs : ok = true → st + len ≤ G.size → penGap R G st len ≤ 12 →
      (if penGap R G st len ≤ 9 then 3 else 2) ≤ s) :
    Inv cw (fun w => S w ∨ (ok = true ∧ w = ⟨c, st, len⟩)) (gapW R G c st len s ok b) := by
  have hcwv : cw ⟨c, st, len⟩ = if st + len ≤ G.size then penGap R G st len else 13 := by
    rw [hcw]; unfold penB; simp [hne, hL]
  have hle := h.le13
  have hcap : cap = 12 := rfl
  have hpg : penGap R G st len ≤ 13 := by unfold penGap; split <;> omega
  unfold gapW
  by_cases hcond : (decide (need b ≤ s) && ok && decide (st + len ≤ G.size)) = true
  · rw [if_pos hcond]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨hneed, hok⟩, hfit⟩ := hcond
    rw [if_pos hfit] at hcwv
    unfold addGap
    rw [gappedPen2_spec R G st len _ hne (by omega)]
    apply inv_congr cw _ _ _ (inv_add cw hc13 S b h c st len _ (by
      rw [hcwv]; split <;> omega))
    intro w; simp [hok]
  · rw [if_neg hcond]
    apply inv_skip' cw hc13 S (fun w => ok = true ∧ w = ⟨c, st, len⟩) b h
    · rintro w ⟨hok, rfl⟩
      unfold Dom
      rw [hcwv]
      split
      · next hfit =>
        have hneed : ¬ need b ≤ s := by
          intro hn'; apply hcond; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hn', hok⟩, hfit⟩
        unfold need at hneed
        by_cases h1 : b.pen < penGap R G st len
        · left; exact h1
        · by_cases h2 : penGap R G st len = 13
          · right; left; exact h2
          · exfalso
            have := hs hok hfit (by omega)
            simp only [hcap] at hneed
            split at this <;> split at hneed <;> omega
      · right; left; rfl
    · intro w; rfl

/-- The windows `gapL` looks at for anchor `i` and gap length `L`. -/
def GapL (c n : Nat) (as : Array Nat) (i L : Nat) (w : Window) : Prop :=
  (BIAS ≤ as[i]! / 16 ∧ w = ⟨c, as[i]! / 16 - BIAS, n + L⟩) ∨
  (BIAS ≤ as[i]! / 16 ∧ w = ⟨c, as[i]! / 16 - BIAS, n - L⟩) ∨
  (BIAS + L ≤ as[i]! / 16 ∧ w = ⟨c, as[i]! / 16 - L - BIAS, n + L⟩) ∨
  (BIAS ≤ as[i]! / 16 + L ∧ w = ⟨c, as[i]! / 16 + L - BIAS, n - L⟩)

theorem gap_support' (st len d1 d2 s : Nat) (hfit : st + len ≤ G.size) (hne : len ≠ R.size)
    (h3 : gapLen R.size len ≤ 3) (hp : penGap R G st len ≤ 12)
    (e1 : st + BIAS = d1) (e2 : st + len + BIAS - R.size = d2)
    (hs : pop4 (maskAt G R d1) + pop4 (maskAt G R d2) = s) :
    (if penGap R G st len ≤ 9 then 3 else 2) ≤ s := by
  rw [← hs, ← e1, ← e2]; exact gap_support R G st len hn hfit hne h3 hp

theorem gapL_inv (as : Array Nat) (ha : AnchorsOK G R as) (i : Nat) (hi : i < as.size) (L : Nat)
    (hL1 : 1 ≤ L) (hL3 : L ≤ 3) (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    Inv cw (fun w => S w ∨ GapL c R.size as i L w)
      (gapL R G c as i (as[i]! / 16) (pop4 (as[i]! % 16)) L b) := by
  have hmem : as[i]! ∈ as.toList := by rw [getElem!_pos as i hi]; exact Array.getElem_mem_toList _
  have hcs := (ha.mem _ hmem).1
  generalize hA : as[i]! / 16 = A at *
  have hsp : supNear as i (A + L) = pop4 (maskAt G R (A + L)) :=
    supNear_spec G R as ha i (A + L) hi (by omega) (by omega)
  have hsm : A ≥ L → supNear as i (A - L) = pop4 (maskAt G R (A - L)) := fun hAL =>
    supNear_spec G R as ha i (A - L) hi (by omega) (by omega)
  have gl : ∀ len, (len = R.size + L ∨ len + L = R.size) → len ≠ R.size ∧ gapLen R.size len ≤ 3 := by
    intro len hl; unfold gapLen; constructor <;> (try split) <;> omega
  unfold gapL
  simp only []
  rw [hcs]
  have w1 := gapW_inv cw hc13 R G c hcw hn S b h (A - BIAS) (R.size + L) (pop4 (maskAt G R A) + supNear as i (A + L)) (decide (BIAS ≤ A))
    (gl _ (Or.inl rfl)).1 (gl _ (Or.inl rfl)).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ A (A + L) _ hfit (gl _ (Or.inl rfl)).1
        (gl _ (Or.inl rfl)).2 hp (by omega) (by omega) (by rw [hsp]))
  have w2 := gapW_inv cw hc13 R G c hcw hn _ _ w1 (A - BIAS) (R.size - L) (pop4 (maskAt G R A) + supNear as i (A - L)) (decide (BIAS ≤ A))
    (gl _ (Or.inr (by omega))).1 (gl _ (Or.inr (by omega))).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ A (A - L) _ hfit (gl _ (Or.inr (by omega))).1
        (gl _ (Or.inr (by omega))).2 hp (by omega) (by omega) (by rw [hsm (by simp [BIAS] at hok; omega)]))
  have w3 := gapW_inv cw hc13 R G c hcw hn _ _ w2 (A - L - BIAS) (R.size + L) (pop4 (maskAt G R A) + supNear as i (A - L)) (decide (BIAS + L ≤ A))
    (gl _ (Or.inl rfl)).1 (gl _ (Or.inl rfl)).2 (fun hok hfit hp => by
      simp only [decide_eq_true_eq] at hok
      exact gap_support' cw hc13 R G c hcw hn _ _ (A - L) A _ hfit (gl _ (Or.inl rfl)).1
        (gl _ (Or.inl rfl)).2 hp (by omega) (by omega) (by rw [hsm (by omega), Nat.add_comm]))
  have w4 := gapW_inv cw hc13 R G c hcw hn _ _ w3 (A + L - BIAS) (R.size - L) (pop4 (maskAt G R A) + supNear as i (A + L)) (decide (BIAS ≤ A + L))
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

theorem gapAll_inv (as : Array Nat) (ha : AnchorsOK G R as) :
    ∀ k i S b, i + k ≤ as.size → Inv cw S b →
      Inv cw (fun w => S w ∨ ∃ i', i ≤ i' ∧ i' < i + k ∧ ∃ L, 1 ≤ L ∧ L ≤ 3 ∧ GapL c R.size as i' L w)
        (gapAll R G c as k i b) := by
  intro k
  induction k with
  | zero => intro i S b _ h; exact inv_congr cw _ _ _ h (fun w => by simp; omega)
  | succ k ih =>
    intro i S b hk h
    unfold gapAll
    simp only []
    have g1 := gapL_inv cw hc13 R G c hcw hn as ha i (by omega) 1 (by omega) (by omega) S b h
    have g2 := gapL_inv cw hc13 R G c hcw hn as ha i (by omega) 2 (by omega) (by omega) _ _ g1
    have g3 := gapL_inv cw hc13 R G c hcw hn as ha i (by omega) 3 (by omega) (by omega) _ _ g2
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

/-! ## Every hit is looked at -/

theorem anchor_index (as : Array Nat) (ha : AnchorsOK G R as) (A : Nat) (hA : maskAt G R A ≠ 0) :
    ∃ i, i < as.size ∧ as[i]! / 16 = A := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (ha.complete A hA)
  simp only [Array.length_toList] at hi
  refine ⟨i, hi, ?_⟩
  rw [getElem!_pos as i hi, ← Array.getElem_toList (by simpa using hi), he]
  have := maskAt_lt G R A; omega

theorem same_cover (as : Array Nat) (ha : AnchorsOK G R as) (st : Nat) (h : cw ⟨c, st, R.size⟩ ≤ 12) :
    ∃ k, k ≤ 3 ∧ SameK c R.size as k ⟨c, st, R.size⟩ := by
  rw [hcw] at h
  unfold penB at h
  split at h
  · next hfit =>
    rw [if_pos rfl] at h
    have hm := same_hit_mask R G st hn hfit h
    have hmem := ha.complete _ hm
    have hp1 := pop4_pos G R _ hm
    have hp4 := pop4_le (maskAt G R (st + BIAS))
    have := maskAt_lt G R (st + BIAS)
    refine ⟨4 - pop4 (maskAt G R (st + BIAS)), by omega, _, hmem, ?_, by omega, ?_⟩
    · rw [show ((st + BIAS) * 16 + maskAt G R (st + BIAS)) % 16 = maskAt G R (st + BIAS) by omega]; omega
    · rw [show ((st + BIAS) * 16 + maskAt G R (st + BIAS)) / 16 = st + BIAS by omega]; simp
  · omega

theorem gap_cover (as : Array Nat) (ha : AnchorsOK G R as) (st len : Nat) (hne : len ≠ R.size)
    (h : cw ⟨c, st, len⟩ ≤ 12) : ∃ i, i < as.size ∧ ∃ L, 1 ≤ L ∧ L ≤ 3 ∧ GapL c R.size as i L ⟨c, st, len⟩ := by
  rw [hcw] at h
  unfold penB at h
  split at h
  · next hfit =>
    split at h
    · next hL =>
      have hs := gap_support R G st len hn hfit hne hL h
      have hL1 : 1 ≤ gapLen R.size len := by unfold gapLen; split <;> omega
      have hgl : (len = R.size + gapLen R.size len) ∨ (len + gapLen R.size len = R.size) := by
        unfold gapLen; split <;> omega
      generalize gapLen R.size len = L at *
      by_cases h1 : maskAt G R (st + BIAS) = 0
      · have h2 : maskAt G R (st + len + BIAS - R.size) ≠ 0 := by
          intro h2; rw [h1, h2] at hs; simp [pop4] at hs; split at hs <;> omega
        obtain ⟨i, hi, hA⟩ := anchor_index cw hc13 R G c hcw hn as ha _ h2
        refine ⟨i, hi, L, hL1, hL, ?_⟩
        unfold GapL; rw [hA]; simp only [BIAS] at *
        rcases hgl with e | e
        · right; right; left; refine ⟨by omega, ?_⟩; simp; omega
        · right; right; right; refine ⟨by omega, ?_⟩; simp; constructor <;> omega
      · obtain ⟨i, hi, hA⟩ := anchor_index cw hc13 R G c hcw hn as ha _ h1
        refine ⟨i, hi, L, hL1, hL, ?_⟩
        unfold GapL; rw [hA]; simp only [BIAS] at *
        rcases hgl with e | e
        · left; refine ⟨by omega, ?_⟩; simp; omega
        · right; left; refine ⟨by omega, ?_⟩; simp; omega
    · omega
  · omega

/-- **One chromosome.**  `mapChrom` keeps the invariant and looks at every hit of chromosome `c`. -/
theorem mapChrom_inv (ix : HIdx) (hchk : checkIdx ix G = true) (S : Window → Prop) (b : Best)
    (h : Inv cw S b) : ∃ S', Inv cw S' (mapChrom R G c ix b) ∧ (∀ w, S w → S' w) ∧
      (∀ st len, cw ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩) := by
  have ha := anchors_spec ix G R hchk
  unfold mapChrom
  simp only []
  generalize anchors ix G R = as at *
  have p0 := samePass_inv cw hc13 R G c hcw hn as ha 0 (by omega) S b h
  have p1 := samePass_inv cw hc13 R G c hcw hn as ha 1 (by omega) _ _ p0
  have p2 := samePass_inv cw hc13 R G c hcw hn as ha 2 (by omega) _ _ p1
  have p3 := samePass_inv cw hc13 R G c hcw hn as ha 3 (by omega) _ _ p2
  generalize samePass R G c as 3 (samePass R G c as 2 (samePass R G c as 1 (samePass R G c as 0 b))) = b4 at p3
  have hsame : ∀ st, cw ⟨c, st, R.size⟩ ≤ 12 →
      ((((S ⟨c, st, R.size⟩ ∨ SameK c R.size as 0 ⟨c, st, R.size⟩) ∨ SameK c R.size as 1 ⟨c, st, R.size⟩) ∨
        SameK c R.size as 2 ⟨c, st, R.size⟩) ∨ SameK c R.size as 3 ⟨c, st, R.size⟩) := by
    intro st hst
    obtain ⟨k, hk, hs⟩ := same_cover cw hc13 R G c hcw hn as ha st hst
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inl (Or.inr hs)
    · exact Or.inr hs
  split
  · have g := gapAll_inv cw hc13 R G c hcw hn as ha as.size 0 _ _ (by omega) p3
    refine ⟨_, g, fun w hw => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hw)))), fun st len hl => ?_⟩
    by_cases hlen : len = R.size
    · subst hlen; exact Or.inl (hsame st hl)
    · obtain ⟨i, hi, L, hL1, hL3, hg⟩ := gap_cover cw hc13 R G c hcw hn as ha st len hlen hl
      exact Or.inr ⟨i, by omega, by omega, L, hL1, hL3, hg⟩
  · next h8 =>
    have g := inv_skip cw hc13 _ (fun w => w.chr = c ∧ w.len ≠ R.size) b4 p3 (by
      rintro ⟨c', st, len⟩ ⟨rfl, hl⟩
      left
      have := penB_gap_ge R G st len hl
      rw [hcw]; omega)
    refine ⟨_, g, fun w hw => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hw)))), fun st len hl => ?_⟩
    by_cases hlen : len = R.size
    · subst hlen; exact Or.inl (hsame st hl)
    · exact Or.inr ⟨rfl, hlen⟩

end chrom

/-- True penalty of a window of the byte genome. -/
def cwG (R : ByteArray) (gbs : Array ByteArray) (w : Window) : Nat :=
  if w.chr < gbs.size then penB R gbs[w.chr]! w.start w.len else 13

theorem cwG_le (R : ByteArray) (gbs : Array ByteArray) (w : Window) : cwG R gbs w ≤ 13 := by
  unfold cwG; split
  · exact penB_le _ _ _ _
  · exact Nat.le_refl _

end MapSpec.Fast

