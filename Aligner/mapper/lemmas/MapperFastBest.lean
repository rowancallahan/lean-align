import MapperFastAlgo
import MapSpec

/-!
The running best window (`Best`) and its invariant.

`cw w` is the true penalty of window `w` (13 = not a hit).  `Inv cw S b`: `b`
records the least penalty over the windows of `S` that were looked at, a
window with that penalty, and whether another window of `S` ties it.
Adding a window with its penalty (or with any value above the current best
when its penalty is too) keeps the invariant (`inv_add`); so does dropping
windows that cannot beat or tie the best (`inv_skip`).  When `S` contains every
hit, `result b` is the unique best hit (`result_spec`).
-/

namespace MapSpec.Fast

open MapSpec

/-- The window `b` holds. -/
def Best.win (b : Best) : Window := ⟨b.chr, b.st, b.len⟩

structure Inv (cw : Window → Nat) (S : Window → Prop) (b : Best) : Prop where
  le13 : b.pen ≤ 13
  min : ∀ w, S w → b.pen ≤ cw w
  hit : b.pen ≤ 12 → cw b.win = b.pen
  amb : b.pen ≤ 12 → (b.amb = true ↔ ∃ w, S w ∧ w ≠ b.win ∧ cw w = b.pen)

theorem inv_init (cw : Window → Nat) (hc : ∀ w, cw w ≤ 13) : Inv cw (fun _ => False) {} := by
  refine ⟨by decide, fun w h => h.elim, fun h => by simp [cap] at h, fun h => by simp [cap] at h⟩

/-- Windows that cannot change the result. -/
def Dom (cw : Window → Nat) (b : Best) (w : Window) : Prop :=
  b.pen < cw w ∨ cw w = 13 ∨ (cw w = b.pen ∧ (b.amb = true ∨ w = b.win))

theorem inv_skip (cw : Window → Nat) (hc : ∀ w, cw w ≤ 13) (S X : Window → Prop) (b : Best)
    (h : Inv cw S b) (hX : ∀ w, X w → Dom cw b w) : Inv cw (fun w => S w ∨ X w) b := by
  refine ⟨h.le13, fun w hw => ?_, h.hit, fun hp => ?_⟩
  · rcases hw with hw | hw
    · exact h.min w hw
    · have := hX w hw; have := h.le13; unfold Dom at *; omega
  · rw [h.amb hp]
    constructor
    · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, Or.inl hw, h1, h2⟩
    · rintro ⟨w, hw | hw, h1, h2⟩
      · exact ⟨w, hw, h1, h2⟩
      · rcases hX w hw with h3 | h3 | ⟨h3, h4 | h4⟩
        · omega
        · omega
        · exact (h.amb hp).mp h4
        · exact absurd h4 h1

theorem add_ne (b : Best) (c st len : Nat) :
    ((c != b.chr || st != b.st || len != b.len) = true) ↔ (⟨c, st, len⟩ : Window) ≠ b.win := by
  unfold Best.win
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Window.mk.injEq]
  constructor
  · rintro ((h | h) | h) ⟨h1, h2, h3⟩ <;> contradiction
  · intro h
    by_cases h1 : c = b.chr
    · by_cases h2 : st = b.st
      · exact Or.inr (fun h3 => h ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)

theorem inv_add (cw : Window → Nat) (hc : ∀ w, cw w ≤ 13) (S : Window → Prop) (b : Best)
    (h : Inv cw S b) (c st len r : Nat) (hr : r = cw ⟨c, st, len⟩ ∨ (b.pen < r ∧ b.pen < cw ⟨c, st, len⟩)) :
    Inv cw (fun w => S w ∨ w = ⟨c, st, len⟩) (b.add c st len r) := by
  have hcw := hc ⟨c, st, len⟩
  have hle := h.le13
  unfold Best.add
  by_cases h1 : r < b.pen
  · rw [if_pos h1]
    have hr' : r = cw ⟨c, st, len⟩ := by omega
    refine ⟨by dsimp only; omega, fun w hw => ?_, fun _ => by simp [Best.win, hr'], fun _ => ?_⟩
    · dsimp only
      rcases hw with hw | rfl
      · have := h.min w hw; omega
      · omega
    · simp only [Best.win]
      constructor
      · intro e; cases e
      · rintro ⟨w, hw | rfl, h2, h3⟩
        · have := h.min w hw; omega
        · exact absurd rfl h2
  · rw [if_neg h1]
    by_cases h2 : (r == b.pen && (c != b.chr || st != b.st || len != b.len)) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true, beq_iff_eq, add_ne] at h2
      have hr' : r = cw ⟨c, st, len⟩ := by omega
      refine ⟨by dsimp only; omega, fun w hw => ?_, fun hp => h.hit hp, fun hp => ?_⟩
      · dsimp only
        rcases hw with hw | rfl
        · exact h.min w hw
        · omega
      · dsimp only at hp ⊢
        exact ⟨fun _ => ⟨_, Or.inr rfl, h2.2, by omega⟩, fun _ => rfl⟩
    · rw [if_neg h2]
      have h2' : r = b.pen → (⟨c, st, len⟩ : Window) = b.win := by
        intro e
        apply Classical.byContradiction
        intro hne
        apply h2
        simp only [Bool.and_eq_true, beq_iff_eq, add_ne]
        exact ⟨e, hne⟩
      refine ⟨h.le13, fun w hw => ?_, h.hit, fun hp => ?_⟩
      · rcases hw with hw | rfl
        · exact h.min w hw
        · omega
      · rw [h.amb hp]
        constructor
        · rintro ⟨w, hw, h3, h4⟩; exact ⟨w, Or.inl hw, h3, h4⟩
        · rintro ⟨w, hw | rfl, h3, h4⟩
          · exact ⟨w, hw, h3, h4⟩
          · exfalso
            rcases hr with hr | hr
            · exact h3 (h2' (by omega))
            · omega

/-- **Result.**  When every hit was looked at, `result` is the unique best hit. -/
theorem result_spec (cw : Window → Nat) (S : Window → Prop) (b : Best) (h : Inv cw S b)
    (hall : ∀ w, cw w ≤ 12 → S w) (w : Window) (pen : Nat) :
    result b = some (w.chr, w.start, w.len, pen) ↔
      cw w = pen ∧ pen ≤ 12 ∧ ∀ w', cw w' ≤ 12 → w' ≠ w → pen < cw w' := by
  unfold result
  constructor
  · intro hr
    split at hr
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨e1, e2, e3, e4⟩ := hr
      have hw : b.win = w := by cases w; simp_all [Best.win]
      subst e4
      refine ⟨by rw [← hw]; exact h.hit hc.1, by simp [cap] at hc; omega, fun w' h1 h2 => ?_⟩
      have := h.min w' (hall w' h1)
      by_cases he : cw w' = b.pen
      · have := (h.amb (by simp [cap] at hc; omega)).mpr ⟨w', hall w' h1, by rw [hw]; exact h2, he⟩
        simp_all
      · omega
    · cases hr
  · rintro ⟨h1, h2, h3⟩
    have hmin := h.min w (hall w (by omega))
    have hp : b.pen ≤ 12 := by omega
    have hbw : b.win = w := by
      apply Classical.byContradiction
      intro hne
      have := h3 b.win (by rw [h.hit hp]; omega) hne
      rw [h.hit hp] at this; omega
    have hpen : b.pen = pen := by rw [← h1, ← hbw, h.hit hp]
    have hamb : b.amb = false := by
      cases ha : b.amb
      · rfl
      · obtain ⟨w', hw', hne, he⟩ := (h.amb hp).mp ha
        have := h3 w' (by omega) (by rw [← hbw]; exact hne)
        omega
    rw [if_pos (by simp [cap, hamb, hp])]
    rw [← hbw, hpen]; rfl

end MapSpec.Fast
