import TierOpt

/-! # Tiers: facts about the old router's tier specs used by `answerOf_correct` (B6)

Stated over the old spec only (`MapSpec`, `MapSpec.Fast`), so `Proofs/Bridge.lean` can import this
file. The translation steps (`hit_of_alignment`, `isProper_iff`) stay in Bridge.lean. -/

namespace Spec.Bridge

theorem pairScoreD_dcost0 (w : MapSpec.PairHit) : MapSpec.pairScoreD MapSpec.dcost0 w = w.1.2 + w.2.2 := by
  simp [MapSpec.pairScoreD, MapSpec.dcost0]

-- a cap at or above `g0` whose threshold is at or below the score `s` (scores are ≤ 0)
theorem cap_le {g0 : Nat} {s : Int} (hs : s ≤ 0) :
    g0 ≤ max g0 (-s).toNat ∧ -((max g0 (-s).toNat : Nat) : Int) ≤ s := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  have h := Nat.le_max_right g0 (-s).toNat
  have e : (((-s).toNat : Nat) : Int) = -s := Int.toNat_of_nonneg (by omega)
  have : (((-s).toNat : Nat) : Int) ≤ ((max g0 (-s).toNat : Nat) : Int) := by exact_mod_cast h
  omega

-- the unique best pair at caps that include `w` scores at least `w`
theorem le_of_pairSpecUT {usl lo hi : Nat} {T1 T2 : Int} {g : MapSpec.Genome} {m1 m2 : List Char}
    {x y : MapSpec.Placement × Int} (h : MapSpec.pairSpecUT MapSpec.sc0 MapSpec.dcost0 usl lo hi T1 T2 g m1 m2 = some (x, y))
    {w : MapSpec.PairHit} (hw : w ∈ MapSpec.properPairs usl lo hi (MapSpec.hitsBoth MapSpec.sc0 T1 g m1)
      (MapSpec.hitsBoth MapSpec.sc0 T2 g m2)) :
    w.1.2 + w.2.2 ≤ x.2 + y.2 := by
  unfold MapSpec.pairSpecUT at h
  rw [MapSpec.bestPairD_iff _ _ _ _ _ _ (MapSpec.hitsBoth_scoreFun _ _ _ _)
    (MapSpec.hitsBoth_scoreFun _ _ _ _)] at h
  obtain ⟨hxy, hall⟩ := h
  rcases hall w hw with hlt | ⟨e1, e2⟩
  · rw [pairScoreD_dcost0, pairScoreD_dcost0] at hlt; simp only at hlt; omega
  · rw [MapSpec.mem_properPairs] at hw hxy
    have := MapSpec.hitsBoth_scoreFun _ _ _ _ _ hw.1 _ hxy.1 e1
    have := MapSpec.hitsBoth_scoreFun _ _ _ _ _ hw.2.1 _ hxy.2.1 e2
    simp only at *; omega

-- a mate's unique best (at any cap) is its best hit at every threshold
theorem le_of_mapSpecBoth {T0 T : Int} {g : MapSpec.Genome} {m : List Char} {x p : MapSpec.Placement × Int}
    (h : MapSpec.mapSpecBoth MapSpec.sc0 T0 g m = some x) (hp : p ∈ MapSpec.hitsBoth MapSpec.sc0 T g m) :
    p.2 ≤ x.2 := by
  have hf := MapSpec.Fast.mateFloor_best h T p hp
  have hx := MapSpec.hitsBoth_nonpos _ _ _ _ (MapSpec.Fast.mapSpecBoth_mem h)
  have e : (((-x.2).toNat : Nat) : Int) = -x.2 := Int.toNat_of_nonneg (by omega)
  omega

end Spec.Bridge
