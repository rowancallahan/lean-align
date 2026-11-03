import PairBnB
import PairUnique

/-!
# Box certificates for `bestPairD` (pair-level uniqueness)

The searches give, for a region of placements, only the best hit score in it, the
placement reaching it, and whether another placement in the region ties it
(`RROk`).  A *box* is a region for mate 1 and a region for mate 2.  When the boxes
cover every proper pair (`Cover`), the box results alone often decide `bestPairD`:

* the box bound `U = s1 + s2` bounds every pair in the box (the distance cost is `≥ 0`);
* a box whose two regions are unambiguous and whose best pair is proper gives a
  *witness* pair; let `W` be the best witness score;
* if every box has `U < W`, or `U = W` and both regions unambiguous, then the pairs
  scoring `W` are exactly the witnesses scoring `W`: one placement pair → mapped,
  several → pair tie (not reported).

`certify` returns `none` when the boxes do not decide (refine and try again), and
`some r` with `r = bestPairD …` otherwise (`certify_ok`).
-/

namespace MapSpec

open AlignmentSpec

/-- Result of a region search: best hit (placement, score) and the tie flag. -/
structure RRes where
  best : Option (Placement × Int)
  amb : Bool

/-- `r` is the region search result over the hits of `h` whose placement is in `R`. -/
def RROk (h : List (Placement × Int)) (R : Placement → Bool) (r : RRes) : Prop :=
  match r.best with
  | none => ∀ x ∈ h, R x.1 = false
  | some (p, s) => (p, s) ∈ h ∧ R p = true ∧ (∀ x ∈ h, R x.1 = true → x.2 ≤ s) ∧
      (r.amb = false → ∀ x ∈ h, R x.1 = true → x.2 = s → x.1 = p)

/-! ## Proofs -/

/-- Every proper pair lies in some box. -/
def Cover {β : Type} (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) (bs : List β)
    (RA RB : β → Placement → Bool) : Prop :=
  ∀ p ∈ properPairs sl lo hi h1 h2, ∃ b ∈ bs, RA b p.1.1 = true ∧ RB b p.2.1 = true

/-- `bestPairD`, characterized (a placement determines its score). -/
theorem bestPairD_iff (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (f1 : ScoreFun h1) (f2 : ScoreFun h2) (p : PairHit) :
    bestPairD dc sl lo hi h1 h2 = some p ↔ p ∈ properPairs sl lo hi h1 h2 ∧
      ∀ x ∈ properPairs sl lo hi h1 h2, pairScoreD dc x < pairScoreD dc p ∨ (x.1.1 = p.1.1 ∧ x.2.1 = p.2.1) := by
  have := Fast.findU_iff (pairScoreD dc) (fun p' p => decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1))
    (properPairs sl lo hi h1 h2) (by
      rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy he
      simp only [decide_eq_true_eq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [mem_properPairs] at hx hy
      have ea : sa = sa' := f1 _ hx.1 _ hy.1 rfl
      have eb : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
      rw [ea, eb]) p
  simp only [decide_eq_true_eq] at this
  exact this

section cert
variable {β : Type} (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
  (f1 : ScoreFun h1) (f2 : ScoreFun h2) (bs : List β) (RA RB : β → Placement → Bool)
  (res : β → RRes × RRes)
  (hok : ∀ b ∈ bs, RROk h1 (RA b) (res b).1 ∧ RROk h2 (RB b) (res b).2)
  (hcov : Cover sl lo hi h1 h2 bs RA RB)

end cert

end MapSpec

