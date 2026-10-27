import MapperDefs
import AlignmentWavefront

/-!
Math behind the capped banded scorer (`codecs/BandScore.lean`).

* `sv`: the specification's optimal score of a read suffix against a genome
  segment, given the step before (score part of `bellmanAux`), and its
  recurrence.
* `Rel t c v`: a computed value `c` stands for the true value `v` at
  threshold `t` — equal when either is `≥ t`, both below `t` otherwise.
  `rel_max3`: the Gotoh update preserves it when every cost `a` satisfies
  `a + t_input ≤ t_output`.
* `sv_lt_thr`: a cell more than `B` diagonals off has its true value below its
  threshold, once `gapOpen + (B + 1) * gapExtend < T`.
-/

namespace MapSpec

open AlignmentSpec

/-! ## Optimal suffix score -/

def sv (sc : Scoring) (xs ys : List Char) (prev : Option Step) : Int :=
  (bellmanAux sc xs ys prev).2

theorem maxOn_snd (a b : List Step × Int) :
    (maxOn (fun item : List Step × Int => item.2) a b).2 = max a.2 b.2 := by
  rw [maxOn_eq_if]
  split <;> omega

theorem sv_nil_nil (sc : Scoring) (prev : Option Step) : sv sc [] [] prev = 0 := by
  simp [sv, bellmanAux]

theorem sv_nil_cons (sc : Scoring) (y : Char) (ys : List Char) (prev : Option Step) :
    sv sc [] (y :: ys) prev = gapXCost sc prev + sv sc [] ys (some .gapX) := by
  simp [sv, bellmanAux]

theorem sv_cons_nil (sc : Scoring) (x : Char) (xs : List Char) (prev : Option Step) :
    sv sc (x :: xs) [] prev = gapYCost sc prev + sv sc xs [] (some .gapY) := by
  simp [sv, bellmanAux]

theorem sv_cons_cons (sc : Scoring) (x : Char) (xs : List Char) (y : Char) (ys : List Char)
    (prev : Option Step) :
    sv sc (x :: xs) (y :: ys) prev =
      max (max (diagCost sc x y + sv sc xs ys none)
               (gapXCost sc prev + sv sc (x :: xs) ys (some .gapX)))
          (gapYCost sc prev + sv sc xs (y :: ys) (some .gapY)) := by
  simp only [sv, bellmanAux, maxOn_snd, bellmanAux_diag_eq_none]

/-- The optimal score is the score of a valid walk. -/
theorem sv_walk (sc : Scoring) (xs ys : List Char) (prev : Option Step) :
    ∃ p, IsMonotoneWalk p xs ys ∧ scoreWalk sc p xs ys prev = sv sc xs ys prev := by
  have h := bestAux_eq_bellmanAux sc xs ys prev
  rw [bestAux] at h
  have hmem := List.maxOn?_mem h
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
  refine ⟨p, isMonotoneWalk_of_mem_allPaths xs ys p hp, ?_⟩
  rw [sv, ← hpe]

/-- The window score is `sv` with no previous step. -/
theorem windowScore_eq_sv (sc : Scoring) (read : List Char) (g : Genome) (w : Window)
    (ys : List Char) (h : windowSeq g w = some ys) :
    windowScore sc read g w = some (sv sc read ys none) := by
  unfold windowScore
  rw [h]
  simp only
  rw [getBestAlignment_eq_bestAux, bestAux_eq_bellmanAux]
  rfl

/-! ## Thresholds and the band -/

/-- Threshold of a state: a gap state has not yet paid the open of its run. -/
def thr (sc : Scoring) (T : Int) : Option Step → Int
  | some .gapX => T - sc.gapOpen
  | some .gapY => T - sc.gapOpen
  | _ => T

/-- The band: a walk with more than `B` gap columns scores below `T`. -/
def BandOK (sc : Scoring) (T : Int) (B : Nat) : Prop :=
  sc.gapOpen + ((B : Int) + 1) * sc.gapExtend < T

/-- The smallest band for `sc` and `T` (3 for the default scoring). -/
def bandOf (sc : Scoring) (T : Int) : Nat :=
  ((sc.gapOpen - T) / (-sc.gapExtend)).toNat

theorem bandOf_ok (sc : Scoring) (hv : ValidScoring sc) (T : Int) :
    BandOK sc T (bandOf sc T) := by
  obtain ⟨-, -, -, he⟩ := hv
  unfold BandOK bandOf
  have hd : 0 < -sc.gapExtend := by omega
  have h1 := Int.lt_ediv_add_one_mul_self (sc.gapOpen - T) hd
  have h2 : ((sc.gapOpen - T) / -sc.gapExtend) ≤ (((sc.gapOpen - T) / -sc.gapExtend).toNat : Int) :=
    Int.self_le_toNat _
  have h3 : ((sc.gapOpen - T) / -sc.gapExtend + 1) * -sc.gapExtend ≤
      ((((sc.gapOpen - T) / -sc.gapExtend).toNat : Int) + 1) * -sc.gapExtend :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have h4 : ((((sc.gapOpen - T) / -sc.gapExtend).toNat : Int) + 1) * -sc.gapExtend =
      -(((((sc.gapOpen - T) / -sc.gapExtend).toNat : Int) + 1) * sc.gapExtend) := by
    rw [Int.mul_neg]
  omega

theorem bandOf_default : bandOf ⟨0, -4, -6, -2⟩ (-12) = 3 := by decide

/-- A valid walk with at least `G` gap columns scores at most
`G * gapExtend`, and at most `gapOpen + G * gapExtend` when it starts outside
a gap. -/
theorem score_le_of_gaps (sc : Scoring) (hv : ValidScoring sc) (p : List Step)
    (xs ys : List Char) (prev : Option Step) (hw : IsMonotoneWalk p xs ys) (G : Nat)
    (hG : 1 ≤ G) (hgaps : (G : Int) ≤ ((ys.length : Int) - xs.length).natAbs) :
    scoreWalk sc p xs ys prev ≤ (G : Int) * sc.gapExtend +
      (if prev = some .gapX ∨ prev = some .gapY then 0 else sc.gapOpen) := by
  obtain ⟨hM, hX, hO, hE⟩ := hv
  obtain ⟨hx, hy⟩ := hw
  rw [xConsumed_sum_eq_counts] at hx
  rw [yConsumed_sum_eq_counts] at hy
  obtain ⟨hmm, hgx, hgy⟩ := stats_eq_counts p xs ys prev
    ⟨by rw [xConsumed_sum_eq_counts]; exact hx, by rw [yConsumed_sum_eq_counts]; exact hy⟩
  rw [scoreWalk_eq_stats, statsScore]
  generalize hs : walkStats p xs ys prev = s at hmm hgx hgy
  have hGle : (G : Int) ≤ (s.gapXCount : Int) + s.gapYCount := by omega
  have h1 : sc.matchScore * (s.matchCount : Int) ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hM (by omega)
  have h2 : sc.mismatchScore * (s.mismatchCount : Int) ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  have h3 : sc.gapExtend * ((s.gapXCount : Int) + s.gapYCount) ≤ (G : Int) * sc.gapExtend := by
    rw [Int.mul_comm (G : Int)]
    exact Int.mul_le_mul_of_nonpos_left (by omega) hGle
  split
  · have h4 : sc.gapOpen * (s.runCount : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hO (by omega)
    omega
  · rename_i hprev
    have hruns : 1 ≤ s.runCount := by
      rcases Nat.eq_zero_or_pos s.runCount with h0 | h0
      · exfalso
        have hz := gaps_eq_zero_of_runs_zero p xs ys prev
          ⟨fun h => hprev (Or.inl h), fun h => hprev (Or.inr h)⟩ (by rw [hs]; exact h0)
        rw [hs] at hz
        omega
      · omega
    have h4 : sc.gapOpen * (s.runCount : Int) ≤ sc.gapOpen := by
      have := Int.mul_le_mul_of_nonpos_left hO (show (1 : Int) ≤ s.runCount by omega)
      simpa using this
    omega

/-- A cell more than `B` diagonals off is below its threshold. -/
theorem sv_lt_thr (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat)
    (hb : BandOK sc T B) (xs ys : List Char) (prev : Option Step)
    (hoff : (B : Int) + 1 ≤ ((ys.length : Int) - xs.length).natAbs) :
    sv sc xs ys prev < thr sc T prev := by
  obtain ⟨p, hw, hs⟩ := sv_walk sc xs ys prev
  have h := score_le_of_gaps sc hv p xs ys prev hw (B + 1) (by omega) (by push_cast; omega)
  rw [hs] at h
  unfold BandOK at hb
  push_cast at h
  cases prev with
  | none => simp [thr] at h ⊢; omega
  | some st => cases st <;> simp [thr] at h ⊢ <;> omega

/-! ## The relation between computed and true values -/

def Rel (t c v : Int) : Prop := (t ≤ v → c = v) ∧ (t ≤ c → c = v)

theorem Rel.refl (t v : Int) : Rel t v v := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Rel.below {t c v : Int} (h : Rel t c v) (hc : c < t) : v < t := by
  have := h.1; omega

theorem Rel.of_below {t c v : Int} (hc : c < t) (hv : v < t) : Rel t c v :=
  ⟨fun h => by omega, fun h => by omega⟩

theorem rel_add {t t1 a c1 v1 : Int} (h1 : Rel t1 c1 v1) (ha : a + t1 ≤ t) :
    Rel t (a + c1) (a + v1) := by
  obtain ⟨h1a, h1b⟩ := h1
  constructor
  · intro h; have := h1a (by omega); omega
  · intro h; have := h1b (by omega); omega

theorem rel_max3 {t t1 t2 t3 a1 a2 a3 c1 c2 c3 v1 v2 v3 : Int}
    (h1 : Rel t1 c1 v1) (h2 : Rel t2 c2 v2) (h3 : Rel t3 c3 v3)
    (ha1 : a1 + t1 ≤ t) (ha2 : a2 + t2 ≤ t) (ha3 : a3 + t3 ≤ t) :
    Rel t (max (max (a1 + c1) (a2 + c2)) (a3 + c3))
      (max (max (a1 + v1) (a2 + v2)) (a3 + v3)) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  constructor
  · intro h
    by_cases e1 : t1 ≤ c1 <;> by_cases f1 : t1 ≤ v1 <;>
    by_cases e2 : t2 ≤ c2 <;> by_cases f2 : t2 ≤ v2 <;>
    by_cases e3 : t3 ≤ c3 <;> by_cases f3 : t3 ≤ v3 <;>
    simp_all <;> omega
  · intro h
    by_cases e1 : t1 ≤ c1 <;> by_cases f1 : t1 ≤ v1 <;>
    by_cases e2 : t2 ≤ c2 <;> by_cases f2 : t2 ≤ v2 <;>
    by_cases e3 : t3 ≤ c3 <;> by_cases f3 : t3 ≤ v3 <;>
    simp_all <;> omega

end MapSpec
