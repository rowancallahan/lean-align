import PairHitsKP
import PairBox

/-!
# Codec `pairUKP`: pair-level uniqueness (`pairSpecUT`), fast path + cap ladder

The proper-pair mode (Rowan, 2026-10-05):

* **Fast path.**  Each mate's genome search at its cap (`mapFastGBKP`).  Both unique
  bests `a`, `b`, a proper pair, distance cost `0` at their fragment: `(a, b)` is the
  answer (`fastU_ok`).
* **Ladder.**  Otherwise every hit within caps `0, 4, 8, …` (`hitsAtKP`), the mate
  with the cheaper lookups first (`costP`; when it has no hit, the other mate is not
  searched at that rung).  At the first rung with a proper pair `w` of score `W`, the
  hits that matter have penalty `≤ −W` (branch and bound, `pairSpecUT_bnb`): when the
  rung's caps cover that, `bestPairD` of the rung's lists is the answer; otherwise the
  lists at caps `min(P, −W)` are.  At the full caps, the lists at the caps are the answer.

    pairUKP … = pairSpecUT sc0 dc sl lo hi (−P1) (−P2) g m1 m2               (pairUKP_mz_eq)

The answer kinds (`UKind`): mapped, `pairTie` (proper pairs exist, no unique best),
none (no proper pair within the caps).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## List facts -/

theorem scoreFun_of_iff {l h : List (Placement × Int)} (e : ∀ x, x ∈ l ↔ x ∈ h) (hf : ScoreFun h) :
    ScoreFun l :=
  fun x hx y hy he => hf x ((e x).1 hx) y ((e y).1 hy) he

/-- `bestPairD` depends on the members of the hit lists only. -/
theorem bestPairD_congr (dc : Nat → Nat) (sl lo hi : Nat) {l1 l2 h1 h2 : List (Placement × Int)}
    (e1 : ∀ x, x ∈ l1 ↔ x ∈ h1) (e2 : ∀ x, x ∈ l2 ↔ x ∈ h2) (f1 : ScoreFun h1) (f2 : ScoreFun h2) :
    bestPairD dc sl lo hi l1 l2 = bestPairD dc sl lo hi h1 h2 := by
  have ep : ∀ p, p ∈ properPairs sl lo hi l1 l2 ↔ p ∈ properPairs sl lo hi h1 h2 := by
    intro p; rw [mem_properPairs, mem_properPairs, e1, e2]
  have key : ∀ p, bestPairD dc sl lo hi l1 l2 = some p ↔ bestPairD dc sl lo hi h1 h2 = some p := by
    intro p
    rw [bestPairD_iff dc sl lo hi l1 l2 (scoreFun_of_iff e1 f1) (scoreFun_of_iff e2 f2),
      bestPairD_iff dc sl lo hi h1 h2 f1 f2]
    simp only [ep]
  cases ha : bestPairD dc sl lo hi l1 l2 with
  | none =>
    cases hb : bestPairD dc sl lo hi h1 h2 with
    | none => rfl
    | some p => have := (key p).2 hb; rw [ha] at this; cases this
  | some p => exact ((key p).1 ha).symm

theorem bestPairD_nil_of (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (h : ∀ p, p ∉ properPairs sl lo hi h1 h2) : bestPairD dc sl lo hi h1 h2 = none := by
  unfold bestPairD
  rw [List.eq_nil_iff_forall_not_mem.mpr h]
  rfl

/-- **Caps from a proper pair.**  Given a proper pair `w` (at the caps `P1, P2`) with
score `W`, any caps `c ≤ P` with `c = P` or `−c ≤ W` give the same answer. -/
theorem pairSpecUT_caps (dc : Nat → Nat) (sl lo hi P1 P2 c1 c2 : Nat) (g : Genome) (m1 m2 : List Char)
    (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2))
    (h1 : c1 ≤ P1) (h2 : c2 ≤ P2)
    (k1 : P1 ≤ c1 ∨ -(c1 : Int) ≤ pairScoreD dc w) (k2 : P2 ≤ c2 ∨ -(c2 : Int) ≤ pairScoreD dc w) :
    pairSpecUT sc0 dc sl lo hi (-(c1 : Int)) (-(c2 : Int)) g m1 m2 =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  obtain ⟨hw1, hw2, hwp⟩ := mem_properPairs.mp hw
  have n1 := hitsBoth_nonpos _ _ _ _ hw1
  have n2 := hitsBoth_nonpos _ _ _ _ hw2
  have hd : (0 : Int) ≤ (dc (fragLen w.1.1 w.2.1) : Int) := Int.natCast_nonneg _
  have s1 : pairScoreD dc w ≤ w.1.2 := by unfold pairScoreD; omega
  have s2 : pairScoreD dc w ≤ w.2.2 := by unfold pairScoreD; omega
  have lift : ∀ (P c : Nat) (m : List Char) (x : Placement × Int), c ≤ P →
      (P ≤ c ∨ -(c : Int) ≤ pairScoreD dc w) → x ∈ hitsBoth sc0 (-(P : Int)) g m →
      pairScoreD dc w ≤ x.2 → x ∈ hitsBoth sc0 (-(c : Int)) g m := by
    intro P c m x hc k hx hs
    rcases k with k | k
    · have : c = P := by omega
      subst this; exact hx
    · apply hitsBoth_mono (T' := max (-(P : Int)) (pairScoreD dc w)) (by omega)
      rw [← hitsBoth_filter]
      exact List.mem_filter.mpr ⟨hx, by simpa using hs⟩
  have hwc : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(c1 : Int)) g m1) (hitsBoth sc0 (-(c2 : Int)) g m2) :=
    mem_properPairs.mpr ⟨lift P1 c1 m1 w.1 h1 k1 hw1 s1, lift P2 c2 m2 w.2 h2 k2 hw2 s2, hwp⟩
  rw [pairSpecUT_bnb dc sl lo hi _ _ g m1 m2 w hwc, pairSpecUT_bnb dc sl lo hi _ _ g m1 m2 w hw]
  have e : ∀ (P c : Nat), c ≤ P → (P ≤ c ∨ -(c : Int) ≤ pairScoreD dc w) →
      max (-(c : Int)) (pairScoreD dc w) = max (-(P : Int)) (pairScoreD dc w) := by
    intro P c hc k
    rcases k with k | k
    · have : c = P := by omega
      rw [this]
    · rw [Int.max_eq_right k, Int.max_eq_right (by omega)]
  rw [e P1 c1 h1 k1, e P2 c2 h2 k2]

/-! ## The best proper pair of a list (by score) -/

@[inline] def topStep (dc : Nat → Nat) (a b : PairHit) : PairHit :=
  if pairScoreD dc a < pairScoreD dc b then b else a

def topW (dc : Nat → Nat) : List PairHit → Option PairHit
  | [] => none
  | p :: ps => some (ps.foldl (topStep dc) p)

theorem foldl_top_mem (dc : Nat → Nat) : ∀ (ps : List PairHit) (a : PairHit), ps.foldl (topStep dc) a ∈ a :: ps
  | [], _ => List.mem_cons_self
  | b :: ps, a => by
    simp only [List.foldl_cons, topStep]
    split
    · exact List.mem_cons_of_mem _ (foldl_top_mem dc ps b)
    · rcases List.mem_cons.mp (foldl_top_mem dc ps a) with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem topW_mem (dc : Nat → Nat) (ps : List PairHit) (w : PairHit) (h : topW dc ps = some w) : w ∈ ps := by
  cases ps with
  | nil => cases h
  | cons p ps =>
    simp only [topW, Option.some.injEq] at h
    subst h; exact foldl_top_mem dc ps p

/-! ## The ladder over any exact hit lists -/

/-- The ladder: `hf b c` = the hits of mate 1 (`b = true`) or mate 2 at cap `c`; `a1`:
mate 1 is searched first at each rung. -/
def ladderU (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (a1 : Bool) : List Nat → Option PairHit
  | [] => bestPairD dc sl lo hi (hf true P1) (hf false P2)
  | c :: cs =>
    let c1 := min c P1
    let c2 := min c P2
    let hA := hf a1 (if a1 then c1 else c2)
    if hA.isEmpty then
      if (if a1 then P1 ≤ c1 else P2 ≤ c2) then none else ladderU dc sl lo hi P1 P2 hf a1 cs
    else
      let hB := hf (!a1) (if a1 then c2 else c1)
      let l1 := if a1 then hA else hB
      let l2 := if a1 then hB else hA
      if P1 ≤ c1 ∧ P2 ≤ c2 then bestPairD dc sl lo hi l1 l2
      else match topW dc (properPairs sl lo hi l1 l2) with
        | none => ladderU dc sl lo hi P1 P2 hf a1 cs
        | some w =>
          let e := (-(pairScoreD dc w)).toNat
          if (P1 ≤ c1 ∨ e ≤ c1) ∧ (P2 ≤ c2 ∨ e ≤ c2) then bestPairD dc sl lo hi l1 l2
          else bestPairD dc sl lo hi (hf true (min P1 e)) (hf false (min P2 e))

section ladder
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (g : Genome) (m1 m2 : List Char)
  (hf : Bool → Nat → List (Placement × Int))
  (hs1 : ∀ c, c ≤ P1 → ∀ x, x ∈ hf true c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m1)
  (hs2 : ∀ c, c ≤ P2 → ∀ x, x ∈ hf false c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m2)

include hs1 hs2

/-- One rung's lists at caps `c1 ≤ P1`, `c2 ≤ P2`: the three ways the ladder ends. -/
theorem rung_full (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) (f1 : P1 ≤ c1) (f2 : P2 ≤ c2) :
    bestPairD dc sl lo hi (hf true c1) (hf false c2) =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  have e1 : c1 = P1 := by omega
  have e2 : c2 = P2 := by omega
  subst e1 e2
  exact bestPairD_congr dc sl lo hi (hs1 _ h1) (hs2 _ h2) (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)

theorem rung_lift (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hf true c1) (hf false c2)) :
    w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2) := by
  obtain ⟨a, b, p⟩ := mem_properPairs.mp hw
  exact mem_properPairs.mpr ⟨hitsBoth_mono (by omega) ((hs1 c1 h1 _).1 a),
    hitsBoth_mono (by omega) ((hs2 c2 h2 _).1 b), p⟩

theorem rung_caps (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2))
    (k1 : P1 ≤ c1 ∨ -(c1 : Int) ≤ pairScoreD dc w) (k2 : P2 ≤ c2 ∨ -(c2 : Int) ≤ pairScoreD dc w) :
    bestPairD dc sl lo hi (hf true c1) (hf false c2) =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  rw [← pairSpecUT_caps dc sl lo hi P1 P2 c1 c2 g m1 m2 w hw h1 h2 k1 k2]
  exact bestPairD_congr dc sl lo hi (hs1 _ h1) (hs2 _ h2) (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)

theorem rung_none (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2)
    (h : (P1 ≤ c1 ∧ hf true c1 = []) ∨ (P2 ≤ c2 ∧ hf false c2 = [])) :
    pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 = none := by
  unfold pairSpecUT
  apply bestPairD_nil_of
  intro p hp
  obtain ⟨a, b, -⟩ := mem_properPairs.mp hp
  rcases h with ⟨f, e⟩ | ⟨f, e⟩
  · have : c1 = P1 := by omega
    subst this
    have := (hs1 c1 h1 _).2 a; rw [e] at this; cases this
  · have : c2 = P2 := by omega
    subst this
    have := (hs2 c2 h2 _).2 b; rw [e] at this; cases this

/-- After a proper pair `w` at the rung's caps: the rung's lists or the lists at
`min(P, −W)` (whichever the ladder takes) give the answer. -/
theorem rung_found (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hf true c1) (hf false c2)) :
    (if (P1 ≤ c1 ∨ (-(pairScoreD dc w)).toNat ≤ c1) ∧ (P2 ≤ c2 ∨ (-(pairScoreD dc w)).toNat ≤ c2) then
      bestPairD dc sl lo hi (hf true c1) (hf false c2)
    else bestPairD dc sl lo hi (hf true (min P1 (-(pairScoreD dc w)).toNat))
      (hf false (min P2 (-(pairScoreD dc w)).toNat))) =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  have hwP := rung_lift sl lo hi P1 P2 g m1 m2 hf hs1 hs2 c1 c2 h1 h2 w hw
  obtain ⟨a, b, -⟩ := mem_properPairs.mp hwP
  have n1 := hitsBoth_nonpos _ _ _ _ a
  have n2 := hitsBoth_nonpos _ _ _ _ b
  have hd : (0 : Int) ≤ (dc (fragLen w.1.1 w.2.1) : Int) := Int.natCast_nonneg _
  have hW : pairScoreD dc w ≤ 0 := by unfold pairScoreD; omega
  split
  · next hk =>
    exact rung_caps dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 c1 c2 h1 h2 w hwP
      (by rcases hk.1 with k | k
          · exact Or.inl k
          · right; omega)
      (by rcases hk.2 with k | k
          · exact Or.inl k
          · right; omega)
  · exact rung_caps dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 _ _ (Nat.min_le_left _ _) (Nat.min_le_left _ _) w hwP
      (by rcases Nat.le_total P1 (-(pairScoreD dc w)).toNat with k | k
          · left; rw [Nat.min_eq_left k]; exact Nat.le_refl _
          · right; rw [Nat.min_eq_right k]; omega)
      (by rcases Nat.le_total P2 (-(pairScoreD dc w)).toNat with k | k
          · left; rw [Nat.min_eq_left k]; exact Nat.le_refl _
          · right; rw [Nat.min_eq_right k]; omega)

set_option maxHeartbeats 1000000 in
/-- **The ladder is exact.** -/
theorem ladderU_eq (a1 : Bool) : ∀ cs : List Nat,
    ladderU dc sl lo hi P1 P2 hf a1 cs = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  intro cs
  induction cs with
  | nil =>
    have r := rung_full dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 P1 P2 (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _)
    exact r
  | cons c cs ih =>
    have h1 : min c P1 ≤ P1 := Nat.min_le_right _ _
    have h2 : min c P2 ≤ P2 := Nat.min_le_right _ _
    have found := rung_found dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 (min c P1) (min c P2) h1 h2
    have full := rung_full dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 (min c P1) (min c P2) h1 h2
    have nn := rung_none dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 (min c P1) (min c P2) h1 h2
    cases a1 with
    | true =>
      simp only [ladderU, if_true, Bool.not_true]
      split
      · next he =>
        split
        · next hf1 => exact (nn (Or.inl ⟨hf1, List.isEmpty_iff.mp he⟩)).symm
        · exact ih
      · split
        · next hk => exact full hk.1 hk.2
        · split
          · exact ih
          · next w hw => exact found w (topW_mem dc _ w hw)
    | false =>
      simp only [ladderU, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      split
      · next he =>
        split
        · next hf2 => exact (nn (Or.inr ⟨hf2, List.isEmpty_iff.mp he⟩)).symm
        · exact ih
      · split
        · next hk => exact full hk.1 hk.2
        · split
          · exact ih
          · next w hw => exact found w (topW_mem dc _ w hw)

end ladder

/-- `ladderU` with a flag: a proper pair was seen (for the answer kind `pairTie`). -/
def ladderUR (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (a1 : Bool) : List Nat → Option PairHit × Bool
  | [] =>
    (bestPairD dc sl lo hi (hf true P1) (hf false P2), !(properPairs sl lo hi (hf true P1) (hf false P2)).isEmpty)
  | c :: cs =>
    let c1 := min c P1
    let c2 := min c P2
    let hA := hf a1 (if a1 then c1 else c2)
    if hA.isEmpty then
      if (if a1 then P1 ≤ c1 else P2 ≤ c2) then (none, false) else ladderUR dc sl lo hi P1 P2 hf a1 cs
    else
      let hB := hf (!a1) (if a1 then c2 else c1)
      let l1 := if a1 then hA else hB
      let l2 := if a1 then hB else hA
      if P1 ≤ c1 ∧ P2 ≤ c2 then (bestPairD dc sl lo hi l1 l2, !(properPairs sl lo hi l1 l2).isEmpty)
      else match topW dc (properPairs sl lo hi l1 l2) with
        | none => ladderUR dc sl lo hi P1 P2 hf a1 cs
        | some w =>
          let e := (-(pairScoreD dc w)).toNat
          if (P1 ≤ c1 ∨ e ≤ c1) ∧ (P2 ≤ c2 ∨ e ≤ c2) then (bestPairD dc sl lo hi l1 l2, true)
          else (bestPairD dc sl lo hi (hf true (min P1 e)) (hf false (min P2 e)), true)

theorem ladderUR_fst (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (a1 : Bool) : ∀ cs, (ladderUR dc sl lo hi P1 P2 hf a1 cs).1 = ladderU dc sl lo hi P1 P2 hf a1 cs
  | [] => rfl
  | c :: cs => by
    have ih := ladderUR_fst dc sl lo hi P1 P2 hf a1 cs
    cases a1 <;>
    · simp only [ladderUR, ladderU, apply_ite Prod.fst, ih, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true]
      split
      · rfl
      · split
        · rfl
        · split
          · simp only [ih]
          · simp only [apply_ite Prod.fst]

/-- The flag: a proper pair within the full caps exists. -/
theorem ladderUR_snd (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (g : Genome) (m1 m2 : List Char)
    (hf : Bool → Nat → List (Placement × Int))
    (hs1 : ∀ c, c ≤ P1 → ∀ x, x ∈ hf true c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m1)
    (hs2 : ∀ c, c ≤ P2 → ∀ x, x ∈ hf false c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m2)
    (a1 : Bool) : ∀ cs, (ladderUR dc sl lo hi P1 P2 hf a1 cs).2 = true →
      ∃ w, w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2)
  | [] => by
    intro h
    simp only [ladderUR, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] at h
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨w, rung_lift sl lo hi P1 P2 g m1 m2 hf hs1 hs2 P1 P2 (Nat.le_refl _) (Nat.le_refl _) w hw⟩
  | c :: cs => by
    intro h
    have ih := ladderUR_snd dc sl lo hi P1 P2 g m1 m2 hf hs1 hs2 a1 cs
    have h1 : min c P1 ≤ P1 := Nat.min_le_right _ _
    have h2 : min c P2 ≤ P2 := Nat.min_le_right _ _
    have lift := rung_lift sl lo hi P1 P2 g m1 m2 hf hs1 hs2 (min c P1) (min c P2) h1 h2
    cases a1 with
    | true =>
      simp only [ladderUR, if_true, Bool.not_true] at h
      split at h
      · split at h
        · cases h
        · exact ih h
      · split at h
        · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] at h
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
          exact ⟨w, lift w hw⟩
        · split at h
          · exact ih h
          · next w hw => exact ⟨w, lift w (topW_mem dc _ w hw)⟩
    | false =>
      simp only [ladderUR, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h
      split at h
      · split at h
        · cases h
        · exact ih h
      · split at h
        · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] at h
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
          exact ⟨w, lift w hw⟩
        · split at h
          · exact ih h
          · next w hw => exact ⟨w, lift w (topW_mem dc _ w hw)⟩

/-! ## Fast path -/

/-- Both mates unique at their caps, a proper pair, no distance cost: that pair. -/
theorem fastU_ok (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (g : Genome) (m1 m2 : List Char)
    (a b : Placement × Int)
    (ha : mapSpecBoth sc0 (-(P1 : Int)) g m1 = some a) (hb : mapSpecBoth sc0 (-(P2 : Int)) g m2 = some b)
    (hp : properPairU sl lo hi a.1 b.1 = true) (hd : dc (fragLen a.1 b.1) = 0) :
    pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 = some (a, b) := by
  obtain ⟨⟨a1, a2⟩, a3⟩ := (mapSpecBoth_iffT _ g m1 a.1 a.2).1 ha
  obtain ⟨⟨b1, b2⟩, b3⟩ := (mapSpecBoth_iffT _ g m2 b.1 b.2).1 hb
  unfold pairSpecUT
  rw [bestPairD_iff dc sl lo hi _ _ (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)]
  refine ⟨mem_properPairs.mpr ⟨(mem_hitsBoth_T _ g m1 a.1 a.2).2 ⟨strandScore_allWindows g m1 _ _ _ a1, a1, a2⟩,
    (mem_hitsBoth_T _ g m2 b.1 b.2).2 ⟨strandScore_allWindows g m2 _ _ _ b1, b1, b2⟩, hp⟩, ?_⟩
  intro x hx
  obtain ⟨x1, x2, -⟩ := mem_properPairs.mp hx
  have y1 := (mem_hitsBoth_T _ g m1 x.1.1 x.1.2).1 x1
  have y2 := (mem_hitsBoth_T _ g m2 x.2.1 x.2.2).1 x2
  have z1 := a3 x.1.1 x.1.2 y1.2.1 y1.2.2
  have z2 := b3 x.2.1 x.2.2 y2.2.1 y2.2.2
  have hdx : (0 : Int) ≤ (dc (fragLen x.1.1 x.2.1) : Int) := Int.natCast_nonneg _
  have amem := (mem_hitsBoth_T _ g m1 a.1 a.2).2 ⟨strandScore_allWindows g m1 _ _ _ a1, a1, a2⟩
  have bmem := (mem_hitsBoth_T _ g m2 b.1 b.2).2 ⟨strandScore_allWindows g m2 _ _ _ b1, b1, b2⟩
  have le1 : x.1.2 ≤ a.2 := by
    rcases z1 with h | h
    · omega
    · exact Int.le_of_eq (hitsBoth_scoreFun _ _ _ _ x.1 x1 a amem h)
  have le2 : x.2.2 ≤ b.2 := by
    rcases z2 with h | h
    · omega
    · exact Int.le_of_eq (hitsBoth_scoreFun _ _ _ _ x.2 x2 b bmem h)
  have sab : pairScoreD dc (a, b) = a.2 + b.2 := by unfold pairScoreD; simp [hd]
  have sx : pairScoreD dc x ≤ x.1.2 + x.2.2 := by unfold pairScoreD; omega
  rw [sab]
  by_cases e1 : x.1.1 = a.1
  · by_cases e2 : x.2.1 = b.1
    · exact Or.inr ⟨e1, e2⟩
    · have := z2.resolve_right e2; left; omega
  · have := z1.resolve_right e1; left; omega

/-! ## Production: packed whole genome -/

/-- Hits of a read at cap `c`: `hitsAtKP`, or the specification for reads too short for
its seed bound. -/
def hitsKPF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) : List (Placement × Int) :=
  match hitsAtKP c ix G offs pgs R with
  | some l => l
  | none => hitsBoth sc0 (-(c : Int)) (decodeGenomeB (pgs.map Mz.unpack)) (decodeBytes R)

/-- Default rungs (`0, 4, 8, 12`, then the full caps). -/
def capsU : List Nat := [0, 4, 8, 12, 16]

/-- **Proper-pair mode**: the fast path, then the ladder (`a1`: mate 1 searched first);
with the flag "a proper pair was seen" (`pairTie` when the answer is `none`). -/
def pairUKPR {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat)
    (a1 : Bool) (ix : L) (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option PairHit × Bool :=
  let lad := fun (_ : Unit) =>
    ladderUR dc sl lo hi P1 P2 (fun b c => hitsKPF ix G offs pgs (if b then R1 else R2) c) a1 caps
  match mapFastGBKP P1 ix G offs pgs R1 with
  | some a =>
    match mapFastGBKP P2 ix G offs pgs R2 with
    | some b => if properPairU sl lo hi a.1 b.1 && dc (fragLen a.1 b.1) == 0 then (some (a, b), true) else lad ()
    | none => lad ()
  | none => lad ()

def pairUKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat)
    (a1 : Bool) (ix : L) (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option PairHit :=
  (pairUKPR dc sl lo hi P1 P2 caps a1 ix G offs pgs R1 R2).1

/-- Answer kind `pairTie`: proper pairs within the caps, none of them the unique best. -/
def PairTieOk (dc : Nat → Nat) (sl lo hi : Nat) (T1 T2 : Int) (g : Genome) (m1 m2 : List Char) : Prop :=
  pairSpecUT sc0 dc sl lo hi T1 T2 g m1 m2 = none ∧
    ∃ w, w ∈ properPairs sl lo hi (hitsBoth sc0 T1 g m1) (hitsBoth sc0 T2 g m2)

theorem hitsBoth_seqs (T : Int) (g g' : Genome) (read : List Char) (h : g.map (·.seq) = g'.map (·.seq)) :
    hitsBoth sc0 T g read = hitsBoth sc0 T g' read := by
  have hl : g.length = g'.length := by simpa using congrArg List.length h
  have hc : ∀ c : Nat, (g[c]?).map (fun x : Chromosome => x.seq) = (g'[c]?).map (fun x : Chromosome => x.seq) := by
    intro c; rw [← List.getElem?_map, ← List.getElem?_map, h]
  have hws : windowSeq g = windowSeq g' := by
    funext w
    unfold windowSeq
    have := hc w.chr
    cases h1 : g[w.chr]? <;> cases h2 : g'[w.chr]? <;> simp_all
  have haw : allWindows g = allWindows g' := by
    unfold allWindows
    rw [hl]
    congr 1
    funext c
    have := hc c
    cases h1 : g[c]? <;> cases h2 : g'[c]? <;> simp_all
  unfold hitsBoth windowScore
  rw [hws, haw]

theorem decode_seqs (gbs : Array ByteArray) (g : Genome) (hg : GenomeBytes gbs g) :
    (decodeGenomeB gbs).map (·.seq) = g.map (·.seq) := by
  obtain ⟨hsz, henc⟩ := hg
  unfold decodeGenomeB
  apply List.ext_getElem
  · simp [hsz]
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    exact decodeBytes_of_encodes _ _ (henc i (by simpa using h1) (by simpa using h2))

section top
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg hchk in
theorem hitsKPF_mem (R : ByteArray) (m : List Char) (hr : Encodes R m) (c : Nat) (hc : c ≤ 16)
    (x : Placement × Int) :
    x ∈ hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R c ↔
      x ∈ hitsBoth sc0 (-(c : Int)) g m := by
  unfold hitsKPF
  split
  · next l hl => exact mem_hitsAtKP_mz c hc g m ix G offs ns R hcut hg hr hchk l hl x
  · rw [decodeBytes_of_encodes R m hr, hitsBoth_seqs _ _ g m (decode_seqs _ g hg)]

include hcut hg hchk in
theorem mapFastGBKP_mz (P : Nat) (R : ByteArray) (m : List Char) (hr : Encodes R m) :
    mapFastGBKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = mapSpecBoth sc0 (-(P : Int)) g m := by
  rw [mapFastGBKP_eq, mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)]
  exact mapFastGB_eq_mapSpecBoth P g m _ R _ _ offs hg hr (catOk_cut G offs ns hcut) (lookOk_pk ix G hchk)

include hcut hg h1 h2 hchk in
/-- **Proper-pair mode, packed whole genome: the specification.** -/
theorem pairUKP_mz_eq (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16) :
    pairUKP dc sl lo hi P1 P2 caps a1 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  have lad := ladderU_eq dc sl lo hi P1 P2 g m1 m2
    (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c (by omega) x)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c (by omega) x) a1 caps
  have lad' : (ladderUR dc sl lo hi P1 P2
      (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
      a1 caps).1 = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
    rw [ladderUR_fst]; exact lad
  unfold pairUKP pairUKPR
  rw [mapFastGBKP_mz g ix G offs ns hcut hg hchk P1 R1 m1 h1, mapFastGBKP_mz g ix G offs ns hcut hg hchk P2 R2 m2 h2]
  split
  · next a ha =>
    split
    · next b hb =>
      split
      · next hk =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        exact (fastU_ok dc sl lo hi P1 P2 g m1 m2 a b ha hb hk.1 hk.2).symm
      · exact lad'
    · exact lad'
  · exact lad'

include hcut hg h1 h2 hchk in
/-- **The answer kind `pairTie` is exact.** -/
theorem pairUKPR_tie (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16)
    (h : pairUKPR dc sl lo hi P1 P2 caps a1 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      (none, true)) :
    PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  have e := pairUKP_mz_eq dc sl lo hi P1 P2 caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk hP1 hP2
  unfold pairUKP at e
  rw [h] at e
  refine ⟨e.symm, ?_⟩
  have snd := ladderUR_snd dc sl lo hi P1 P2 g m1 m2
    (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c (by omega) x)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c (by omega) x) a1 caps
  unfold pairUKPR at h
  rw [mapFastGBKP_mz g ix G offs ns hcut hg hchk P1 R1 m1 h1, mapFastGBKP_mz g ix G offs ns hcut hg hchk P2 R2 m2 h2] at h
  split at h
  · split at h
    · split at h
      · cases h
      · exact snd (by simpa using congrArg Prod.snd h)
    · exact snd (by simpa using congrArg Prod.snd h)
  · exact snd (by simpa using congrArg Prod.snd h)

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.ladderU_eq
#print axioms MapSpec.Fast.fastU_ok
#print axioms MapSpec.Fast.pairUKP_mz_eq
#print axioms MapSpec.Fast.pairUKPR_tie
