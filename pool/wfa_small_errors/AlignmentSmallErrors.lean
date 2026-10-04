import AlignmentWfaArray

/-!
An exact shortcut for equal-length inputs with at most two substitutions.
Under unit substitution/extension penalties and nonpositive gap-open score,
any gapped equal-length walk costs at least two. A checked diagonal walk
costing at most two therefore attains the optimum. Other cases fall back
to the proved array WFA. This certificate is our own elementary proof.
-/
namespace AlignmentSpec

local instance : LawfulBEq Step where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> cases h <;> rfl
  rfl := by intro a; cases a <;> rfl

theorem gapless_eq_diags (p : List Step) (xs ys : List Char)
    (hv : IsMonotoneWalk p xs ys) (hx : p.count .gapX = 0)
    (hy : p.count .gapY = 0) : p = List.replicate xs.length .diag := by
  have hevery : ∀ s ∈ p, s = Step.diag := by
    intro s hs
    cases s with
    | diag => rfl
    | gapX => have := List.count_pos_iff.mpr hs; omega
    | gapY => have := List.count_pos_iff.mpr hs; omega
  have hp := List.eq_replicate_of_mem hevery
  have hn := hv.1
  rw [hp] at hn
  simp [xConsumed] at hn
  simpa [hn] using hp

theorem two_errors_optimal (sc : Scoring) (xs ys : List Char)
    (hm : sc.matchScore = 0) (hx : sc.mismatchScore = -1)
    (he : sc.gapExtend = -1) (ho : sc.gapOpen ≤ 0)
    (hlen : xs.length = ys.length)
    (hs : -2 ≤ walkScore sc xs ys (List.replicate xs.length .diag))
    (p : List Step) (hv : IsMonotoneWalk p xs ys) :
    walkScore sc xs ys p ≤ walkScore sc xs ys (List.replicate xs.length .diag) := by
  have hcons := hv
  simp only [IsMonotoneWalk, xConsumed_sum_eq_counts, yConsumed_sum_eq_counts] at hcons
  have hg : p.count .gapX = p.count .gapY := by omega
  by_cases hz : p.count .gapX = 0
  · rw [gapless_eq_diags p xs ys hv hz (by omega)]
    exact Int.le_refl _
  · have hcounts := stats_eq_counts p xs ys none hv
    have hrun : sc.gapOpen * ((walkStats p xs ys none).runCount : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg ho (by omega)
    have hsform := scoreWalk_eq_stats sc p xs ys none
    simp only [statsScore, hm, hx, he, Int.zero_mul, Int.neg_one_mul,
      hcounts.2.1, hcounts.2.2] at hsform
    unfold walkScore
    unfold walkScore at hs
    omega

/-- Stop at the third unit mismatch; allocate the diagonal walk only on success. -/
def diagCheckA (sc : Scoring) (xa ya : Array Char) : Nat → Nat → Int → Option Int
  | 0, i, acc => if acc < -2 then none else walkCheckA sc xa ya [] i i none acc
  | fuel+1, i, acc =>
    if acc < -2 then none else
      match xa[i]?, ya[i]? with
      | some x, some y => diagCheckA sc xa ya fuel (i+1) (acc + diagCost sc x y)
      | _, _ => none

theorem diagCheckA_sound (sc : Scoring) (xa ya : Array Char) (fuel : Nat) :
    ∀ i acc s prev, diagCheckA sc xa ya fuel i acc = some s →
      walkCheckA sc xa ya (List.replicate fuel .diag) i i prev acc = some s := by
  induction fuel with
  | zero =>
    intro i acc s prev h
    simp only [diagCheckA] at h
    split at h
    · simp at h
    · exact h
  | succ fuel ih =>
    intro i acc s prev h
    simp only [diagCheckA] at h
    split at h
    · simp at h
    · simp only [List.replicate_succ, walkCheckA]
      split at h
      · rename_i x y hx hy
        simp only [hx, hy]
        exact ih (i+1) (acc + diagCost sc x y) s (some .diag) h
      · rename_i hnone
        simp at h

def smallDiag (sc : Scoring) (xa ya : Array Char) : Option (List Step × Int) :=
  if sc.matchScore = 0 ∧ sc.mismatchScore = -1 ∧ sc.gapExtend = -1 ∧
      sc.gapOpen ≤ 0 ∧ xa.size = ya.size then
    let w := List.replicate xa.size Step.diag
    match diagCheckA sc xa ya xa.size 0 0 with
    | none => none
    | some s => if -2 ≤ s then some (w, s) else none
  else none

theorem smallDiag_spec (sc : Scoring) (xa ya : Array Char) (w : List Step) (s : Int)
    (h : smallDiag sc xa ya = some (w, s)) :
    IsMonotoneWalk w xa.toList ya.toList ∧ walkScore sc xa.toList ya.toList w = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold smallDiag at h
  split at h
  · rename_i hg
    obtain ⟨hm, hx, he, ho, hlen⟩ := hg
    dsimp only at h
    split at h
    · simp at h
    · rename_i score hc
      split at h
      · rename_i hs
        cases h
        have hc := diagCheckA_sound sc xa ya xa.size 0 0 s none hc
        rw [walkCheckA_eq] at hc
        simp only [List.drop_zero] at hc
        have hw := walkCheck_sound sc (List.replicate xa.size .diag) xa.toList ya.toList none 0 s hc
        have hscore : walkScore sc xa.toList ya.toList (List.replicate xa.size .diag) = s := by
          simpa [walkScore] using hw.2
        refine ⟨hw.1, hscore, ?_⟩
        obtain ⟨⟨bp, bs⟩, hb⟩ := getBestAlignment_returns_some sc xa.toList ya.toList
        have hbvalid := getBestAlignment_returns_a_valid_walk sc xa.toList ya.toList bp bs hb
        have hupper := two_errors_optimal sc xa.toList ya.toList hm hx he ho
          (by simpa using hlen) (by simpa [hscore] using hs) bp hbvalid.1
        have hlower := getBestAlignment_returns_a_maximum_score sc xa.toList ya.toList bp bs
          (List.replicate xa.size .diag) hb hw.1
        simp only [Array.length_toList, hscore, hbvalid.2] at hupper
        rw [hscore] at hlower
        have : s = bs := by omega
        simp [hb, this]
      · simp at h
  · simp at h

def wfaAlignH (sc : Scoring) (xa ya : Array Char) : Option (List Step × Int) :=
  match smallDiag sc xa ya with
  | some r => some r
  | none => wfaAlignCA sc xa ya

theorem wfaAlignH_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignH sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold wfaAlignH
  cases h : smallDiag sc xa ya with
  | none => exact wfaAlignCA_score sc xa ya
  | some r => exact (smallDiag_spec sc xa ya r.1 r.2 h).2.2

theorem wfaAlignH_sound (sc : Scoring) (xa ya : Array Char) (w : List Step) (s : Int)
    (h : wfaAlignH sc xa ya = some (w, s)) :
    IsMonotoneWalk w xa.toList ya.toList ∧ walkScore sc xa.toList ya.toList w = s := by
  unfold wfaAlignH at h
  cases hr : smallDiag sc xa ya with
  | none => rw [hr] at h; exact wfaAlignCA_sound sc xa ya w s h
  | some r =>
    rw [hr] at h
    cases h
    exact ⟨(smallDiag_spec sc xa ya w s hr).1, (smallDiag_spec sc xa ya w s hr).2.1⟩

theorem wfaAlignH_isSome (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignH sc xa ya).isSome := by
  unfold wfaAlignH
  cases smallDiag sc xa ya with
  | none => exact wfaAlignCA_isSome sc xa ya
  | some _ => rfl

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignH_score
#print axioms AlignmentSpec.wfaAlignH_sound
#print axioms AlignmentSpec.wfaAlignH_isSome
