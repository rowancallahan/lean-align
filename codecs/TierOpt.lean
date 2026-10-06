import TierRouter

/-!
# Tier 2 pairs whose ceilings meet their floors: a best proper pair, proved

No new search: a corollary of `tierPair_sound` on what the router already reports.

A tier 2 pair has, per mate, a ceiling placement `plᵢ` (score `−pHᵢ`, a real spec hit at least that
good) and a proved floor `cdᵢ`; when the guarantee found no proper pair within `G0` (`pf = some G0`)
every proper pair scores below `−G0`, and by the gapless arithmetic above `−8` (scores are multiples
of 4 there) at most `−pfFloor G0`.  When the two ceiling placements form a proper pair and
`pH₁ + pH₂ ≤ max (cd₁ + cd₂) (pfFloor G0)`, that pair is a proper pair of the specification at its
exact scores, and no proper pair (at any caps) scores higher (`t2Opt_sound`).  It may tie with
another pair: this is "a best pair", not `pairSpecUT`'s unique one.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- The pair floor from "every proper pair scores below `−G0`" (scores above `−8` are multiples of 4). -/
def pfFloor (G0 : Nat) : Nat := if G0 < 4 then 4 else if G0 < 8 then 8 else G0 + 1

/-- The proved pair floor of a routed pair: the mates' floors, and the guarantee's pair floor. -/
def pairFloor (t : TierOut) : Nat :=
  max (t.m1.cd + t.m2.cd) (match t.pf with | some G0 => pfFloor G0 | none => 0)

/-- A tier 2 pair whose two ceiling placements form a proper pair with summed penalty at most the
pair floor: that pair. -/
def t2Opt (usl lo hi : Nat) (t : TierOut) : Option PairHit :=
  if t.tag = .t2 ∧ t.m1.pH + t.m2.pH ≤ pairFloor t then
    match t.m1.pl, t.m2.pl with
    | some x, some y => if properPairU usl lo hi x.1 y.1 then some (x, y) else none
    | _, _ => none
  else none

theorem pfFloor_le {s1 s2 : Int} {G0 : Nat} (h1 : s1 ≤ 0) (h2 : s2 ≤ 0)
    (m1 : -8 < s1 → ∃ k : Nat, s1 = -4 * (k : Int)) (m2 : -8 < s2 → ∃ k : Nat, s2 = -4 * (k : Int))
    (h : s1 + s2 < -(G0 : Int)) : s1 + s2 ≤ -(pfFloor G0 : Int) := by
  unfold pfFloor
  by_cases h8 : -8 < s1 + s2
  · obtain ⟨k1, e1⟩ := m1 (by omega)
    obtain ⟨k2, e2⟩ := m2 (by omega)
    subst e1 e2
    split
    · omega
    · split <;> omega
  · split
    · omega
    · split <;> omega

/-- **Every proper pair scores at most minus the pair floor** (any caps), from `FloorOk`. -/
theorem pairFloor_ok {usl lo hi : Nat} {g : Genome} {m1 m2 : List Char} {t : TierOut}
    (hF : FloorOk usl lo hi g m1 m2 t) (T1 T2 : Int) :
    ∀ w ∈ properPairs usl lo hi (hitsBoth sc0 T1 g m1) (hitsBoth sc0 T2 g m2),
      w.1.2 + w.2.2 ≤ -(pairFloor t : Int) := by
  intro w hw
  obtain ⟨⟨p1, s1⟩, ⟨p2, s2⟩⟩ := w
  rw [mem_properPairs] at hw
  obtain ⟨h1, h2, hp⟩ := hw
  have f1 := hF.1 T1 _ h1
  have f2 := hF.2.1 T2 _ h2
  have n1 := hitsBoth_nonpos _ _ _ _ h1
  have n2 := hitsBoth_nonpos _ _ _ _ h2
  have e1 := (mem_hitsBoth_T _ _ _ _ _).mp h1
  have e2 := (mem_hitsBoth_T _ _ _ _ _).mp h2
  simp only at f1 f2 n1 n2 ⊢
  unfold pairFloor
  cases hpf : t.pf with
  | none => simp only; omega
  | some G0 =>
    simp only
    have hlt : s1 + s2 < -(G0 : Int) := by
      have := hF.2.2 G0 hpf (max G0 (-s1).toNat) (max G0 (-s2).toNat) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        ((p1, s1), (p2, s2))
        (mem_properPairs.mpr ⟨(mem_hitsBoth_T _ _ _ _ _).mpr ⟨e1.1, e1.2.1, by omega⟩,
          (mem_hitsBoth_T _ _ _ _ _).mpr ⟨e2.1, e2.2.1, by omega⟩, hp⟩)
      unfold pairScoreD dcost0 at this
      simpa using this
    have := pfFloor_le n1 n2 (strandScore_mul4 g m1 p1.2 p1.1 s1 e1.2.1) (strandScore_mul4 g m2 p2.2 p2.1 s2 e2.2.1) hlt
    omega

/-- **A tier 2 pair whose ceilings meet the pair floor is a best proper pair**: `(x, y)` is a proper
pair of the specification at its exact scores, and no proper pair at any caps scores higher. -/
theorem t2Opt_sound {usl lo hi : Nat} {g : Genome} {m1 m2 : List Char} {O1 O2 : Option ByteArray} {t : TierOut}
    (hT : TierOk usl lo hi g m1 m2 O1 O2 t) {x y : Placement × Int} (h : t2Opt usl lo hi t = some (x, y)) :
    (x, y) ∈ properPairs usl lo hi (hitsBoth sc0 x.2 g m1) (hitsBoth sc0 y.2 g m2) ∧
      ∀ T1 T2 : Int, ∀ w ∈ properPairs usl lo hi (hitsBoth sc0 T1 g m1) (hitsBoth sc0 T2 g m2),
        pairScoreD dcost0 w ≤ pairScoreD dcost0 (x, y) := by
  unfold t2Opt at h
  split at h
  · rename_i hc
    obtain ⟨htag, hle⟩ := hc
    unfold TierOk at hT
    rw [htag] at hT
    obtain ⟨hF, ⟨k1, c1⟩, ⟨k2, c2⟩⟩ := hT
    split at h
    · rename_i x' y' hx hy
      split at h
      · rename_i hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ex, s1, hs1, hm1⟩ := (c1 k1).2.2 x' hx
        obtain ⟨ey, s2, hs2, hm2⟩ := (c2 k2).2.2 y' hy
        have hP := pairFloor_ok hF x'.2 y'.2 ((x'.1, s1), (y'.1, s2)) (mem_properPairs.mpr ⟨hm1, hm2, hp⟩)
        simp only at hP
        have e1 : s1 = x'.2 := by omega
        have e2 : s2 = y'.2 := by omega
        rw [e1] at hm1
        rw [e2] at hm2
        refine ⟨mem_properPairs.mpr ⟨hm1, hm2, hp⟩, fun T1 T2 w hw => ?_⟩
        have := pairFloor_ok hF T1 T2 w hw
        show w.1.2 + w.2.2 - ((0 : Nat) : Int) ≤ x'.2 + y'.2 - ((0 : Nat) : Int)
        omega
      · cases h
    · cases h
  · cases h

end MapSpec.Fast

#print axioms MapSpec.Fast.pairFloor_ok
#print axioms MapSpec.Fast.t2Opt_sound
