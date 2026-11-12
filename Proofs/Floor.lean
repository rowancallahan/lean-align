import Proofs.Report

/-! # The report floor: pairs below `junkScore`, and proofs that no good proper pair exists

Spec's clause 1 asks every reported pair to score at least `insertSettings.junkScore`; an answer without a pair
needs `bestPossibleScore < requiredMapBound`. The pieces here:

* `score_of_report`: a printed pair's score is the sum of its two printed mate scores;
* `bound_of_noPair`: when no proper pair of hits within cap `c` (both mates) scores at least `−c`, every proper
  pair of the Specification scores at most `−(c + 1)` (a pair at `≥ −c` has both mates at `≥ −c`: scores ≤ 0). -/

namespace Spec.Floor

open Bridge

theorem score_of_report {genome : Genome} {m1 m2 : Read} {pair : PairAlignment genome m1 m2} {rep : PairReport}
    (h : pair.report = rep) : pair.score = rep.mate1.score + rep.mate2.score := by
  subst h; rfl

-- a printed pair's score
def repScore (rep : PairReport) : Int := rep.mate1.score + rep.mate2.score

theorem bound_of_noPair (insertSettings : InsertSettings) {genome : Genome} {m1 m2 : Read} (c : Nat)
    (h : ∀ w ∈ MapSpec.properPairs insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
        (MapSpec.hitsBoth MapSpec.sc0 (-(c : Int)) (oldGenome genome) m1)
        (MapSpec.hitsBoth MapSpec.sc0 (-(c : Int)) (oldGenome genome) m2), w.1.2 + w.2.2 < -(c : Int))
    (pair : PairAlignment genome m1 m2) (hp : pair.IsProper insertSettings.range insertSettings.dovetailSlack) :
    pair.score ≤ -((c : Int) + 1) := by
  -- an alignment gives a hit at its placement, at every threshold up to the hit's score (`answerOf_correct`)
  have hit_at : ∀ {read : Read} (alignment : GenomicAlignment genome read),
      ∃ s, alignment.score ≤ s ∧ s ≤ 0 ∧ ∀ T, T ≤ s →
        (oldPlacement alignment.placement, s) ∈ MapSpec.hitsBoth MapSpec.sc0 T (oldGenome genome) read := by
    intro read alignment
    obtain ⟨s, hs, hm⟩ := hit_of_alignment alignment alignment.score (Int.le_refl _)
    refine ⟨s, hs, MapSpec.hitsBoth_nonpos _ _ _ _ hm, fun T hT => ?_⟩
    rw [MapSpec.Fast.mem_hitsBoth_T] at hm ⊢
    exact ⟨hm.1, hm.2.1, hT⟩
  obtain ⟨s1, h1, n1, hm1⟩ := hit_at pair.first
  obtain ⟨s2, h2, n2, hm2⟩ := hit_at pair.second
  have hs : pair.score ≤ s1 + s2 := by unfold PairAlignment.score; omega
  by_cases hc : -(c : Int) ≤ s1 + s2
  · exfalso
    have a1 := hm1 (-(c : Int)) (by omega)
    have a2 := hm2 (-(c : Int)) (by omega)
    have hpp := (isProper_iff pair insertSettings.range insertSettings.dovetailSlack).mp hp
    have hw := h ((oldPlacement pair.first.placement, s1), (oldPlacement pair.second.placement, s2))
      (MapSpec.mem_properPairs.mpr ⟨a1, a2, hpp⟩)
    have e : ((oldPlacement pair.first.placement, s1), (oldPlacement pair.second.placement, s2)).1.2 +
        ((oldPlacement pair.first.placement, s1), (oldPlacement pair.second.placement, s2)).2.2 = s1 + s2 := rfl
    omega
  · omega

end Spec.Floor
