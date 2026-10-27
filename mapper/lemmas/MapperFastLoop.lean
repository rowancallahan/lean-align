import MapperFastBest
import MapperFastSupport

/-!
Generic facts for the loops of the fast mapper: invariant congruence,
skipping, folds, and one gapped window (`gapW_inv`); the true penalty `cwG`.
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

end chrom

/-- True penalty of a window of the byte genome. -/
def cwG (R : ByteArray) (gbs : Array ByteArray) (w : Window) : Nat :=
  if w.chr < gbs.size then penB R gbs[w.chr]! w.start w.len else 13

theorem cwG_le (R : ByteArray) (gbs : Array ByteArray) (w : Window) : cwG R gbs w ≤ 13 := by
  unfold cwG; split
  · exact penB_le _ _ _ _
  · exact Nat.le_refl _

end MapSpec.Fast

