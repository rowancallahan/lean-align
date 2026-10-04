import MapperFastBest

/-!
`Best` and its invariant for any penalty cap `P` (`MapperFastBest` is `P = 12`).

`cw w` is the true penalty of window `w`, `P + 1` when `w` is not a hit.
`InvP P cw S b`: `b` holds the least penalty over the windows of `S`, a window
with that penalty, and whether another window of `S` ties it (`inv_addP`,
`inv_skipP`).  When `S` holds every hit, `resultP P b` is the unique best hit
(`resultP_spec`).
-/

namespace MapSpec.Fast

open MapSpec

/-- The empty best for cap `P`. -/
def initP (P : Nat) : Best := { pen := P + 1 }

def resultP (P : Nat) (b : Best) : Option (Nat × Nat × Nat × Nat) :=
  if b.pen ≤ P && !b.amb then some (b.chr, b.st, b.len, b.pen) else none

structure InvP (P : Nat) (cw : Window → Nat) (S : Window → Prop) (b : Best) : Prop where
  le : b.pen ≤ P + 1
  min : ∀ w, S w → b.pen ≤ cw w
  hit : b.pen ≤ P → cw b.win = b.pen
  amb : b.pen ≤ P → (b.amb = true ↔ ∃ w, S w ∧ w ≠ b.win ∧ cw w = b.pen)

section
variable (P : Nat) (cw : Window → Nat) (hc : ∀ w, cw w ≤ P + 1)

theorem inv_initP : InvP P cw (fun _ => False) (initP P) :=
  ⟨Nat.le_refl _, fun w h => h.elim, fun h => absurd h (by simp [initP]), fun h => absurd h (by simp [initP])⟩

/-- Windows that cannot change the result. -/
def DomP (b : Best) (w : Window) : Prop :=
  b.pen < cw w ∨ cw w = P + 1 ∨ (cw w = b.pen ∧ (b.amb = true ∨ w = b.win))

include hc

theorem inv_skipP (S X : Window → Prop) (b : Best)
    (h : InvP P cw S b) (hX : ∀ w, X w → DomP P cw b w) : InvP P cw (fun w => S w ∨ X w) b := by
  refine ⟨h.le, fun w hw => ?_, h.hit, fun hp => ?_⟩
  · rcases hw with hw | hw
    · exact h.min w hw
    · have := hX w hw; have := h.le; have := hc w; unfold DomP at *; omega
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

theorem inv_addP (S : Window → Prop) (b : Best)
    (h : InvP P cw S b) (c st len r : Nat) (hr : r = cw ⟨c, st, len⟩ ∨ (b.pen < r ∧ b.pen < cw ⟨c, st, len⟩)) :
    InvP P cw (fun w => S w ∨ w = ⟨c, st, len⟩) (b.add c st len r) := by
  have hcw := hc ⟨c, st, len⟩
  have hle := h.le
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
      refine ⟨h.le, fun w hw => ?_, h.hit, fun hp => ?_⟩
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

omit hc in
/-- **Result.**  When every hit was looked at, `resultP` is the unique best hit. -/
theorem resultP_spec (S : Window → Prop) (b : Best) (h : InvP P cw S b)
    (hall : ∀ w, cw w ≤ P → S w) (w : Window) (pen : Nat) :
    resultP P b = some (w.chr, w.start, w.len, pen) ↔
      cw w = pen ∧ pen ≤ P ∧ ∀ w', cw w' ≤ P → w' ≠ w → pen < cw w' := by
  unfold resultP
  constructor
  · intro hr
    split at hr
    · next hcnd =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcnd
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨e1, e2, e3, e4⟩ := hr
      have hw : b.win = w := by cases w; simp_all [Best.win]
      subst e4
      refine ⟨by rw [← hw]; exact h.hit hcnd.1, hcnd.1, fun w' h1 h2 => ?_⟩
      have := h.min w' (hall w' h1)
      by_cases he : cw w' = b.pen
      · have := (h.amb hcnd.1).mpr ⟨w', hall w' h1, by rw [hw]; exact h2, he⟩
        simp_all
      · omega
    · cases hr
  · rintro ⟨h1, h2, h3⟩
    have hmin := h.min w (hall w (by omega))
    have hp : b.pen ≤ P := by omega
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
    rw [if_pos (by simp [hamb, hp])]
    rw [← hbw, hpen]; rfl

end

end MapSpec.Fast
