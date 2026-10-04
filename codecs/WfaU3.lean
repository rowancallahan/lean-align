import AlignmentSpec              -- the specification (spec/, frozen)
import AlignmentWfaU32Kernel3     -- pool: supporting definitions and lemmas

/-!
# Codec `wfaAlignU3`

The algorithm, then the theorem against the specification, then its proof.
The parts the algorithm calls (`compactSmall`, `certifiedRunsU3`, `wfaAlignK`)
and the lemmas the proofs cite are in `pool/`.
-/

namespace AlignmentSpec.U32Proof

/-! ## The algorithm -/

/-- The kernel: exact shortcut, UInt32 fast path, proven fallback. -/
def wfaAlignU3 (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none =>
    match certifiedRunsU3 sc xa ya with
    | some r => some r
    | none => wfaAlignK sc xa ya

/-! ## The theorem: the returned score is the optimal score of the specification -/

theorem wfaAlignU3_score (sc : Scoring) (xa ya : Array Char) :
    (match wfaAlignU3 sc xa ya with
     | some result => some result.2
     | none => none) =
    (match getBestAlignment sc xa.toList ya.toList with
     | some result => some result.2
     | none => none) := by
  unfold wfaAlignU3
  cases hc : compactSmall sc xa ya with
  | some r =>
    have h := wfaAlignHC_score sc xa ya
    cases hs : getBestAlignment sc xa.toList ya.toList <;>
      simpa [wfaAlignHC, hc, hs] using h
  | none =>
    cases hr : certifiedRunsU3 sc xa ya with
    | some r =>
      cases hs : getBestAlignment sc xa.toList ya.toList <;>
        simpa [hs] using (certifiedRunsU3_spec sc xa ya r.1 r.2 hr).2.2
    | none =>
      cases hk : wfaAlignK sc xa ya <;>
        cases hs : getBestAlignment sc xa.toList ya.toList <;>
        simpa [hk, hs] using wfaAlignK_score sc xa ya


/-! ## Further theorems -/

/-- Any returned CIGAR is a valid alignment of the two sequences, and the
returned score is its score. -/
theorem wfaAlignU3_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignU3 sc xa ya = some (c, s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  unfold wfaAlignU3 at h
  cases hc : compactSmall sc xa ya with
  | some r =>
    apply wfaAlignHC_sound sc xa ya c s
    simpa [wfaAlignHC, hc] using h
  | none =>
    rw [hc] at h
    cases hr : certifiedRunsU3 sc xa ya with
    | some r =>
      rw [hr] at h
      cases h
      exact ⟨(certifiedRunsU3_spec sc xa ya c s hr).1, (certifiedRunsU3_spec sc xa ya c s hr).2.1⟩
    | none =>
      rw [hr] at h
      exact wfaAlignK_sound sc xa ya c s h

theorem wfaAlignU3_isSome (sc : Scoring) (xa ya : Array Char) : (wfaAlignU3 sc xa ya).isSome := by
  obtain ⟨best, hb⟩ := getBestAlignment_returns_some sc xa.toList ya.toList
  have h := wfaAlignU3_score sc xa ya
  rw [hb] at h
  cases hw : wfaAlignU3 sc xa ya with
  | none => rw [hw] at h; simp at h
  | some _ => rfl

theorem wfaAlignU3_score_eq_wfaAlign (sc : Scoring) (xa ya : Array Char) :
    (match wfaAlignU3 sc xa ya with
     | some result => some result.2
     | none => none) =
    (match wfaAlign sc xa.toList ya.toList with
     | some result => some result.2
     | none => none) := by
  apply (wfaAlignU3_score sc xa ya).trans
  cases hs : getBestAlignment sc xa.toList ya.toList <;>
    cases hw : wfaAlign sc xa.toList ya.toList <;>
    simpa [hs, hw] using (wfaAlign_score sc xa.toList ya.toList).symm

theorem wfaAlignU3_score_fun_eq :
    (fun sc (xa ya : Array Char) =>
      match wfaAlignU3 sc xa ya with
      | some result => some result.2
      | none => none) =
    (fun sc (xa ya : Array Char) =>
      match wfaAlign sc xa.toList ya.toList with
      | some result => some result.2
      | none => none) := by
  funext sc xa ya; exact wfaAlignU3_score_eq_wfaAlign sc xa ya

end AlignmentSpec.U32Proof

namespace AlignmentSpec
export U32Proof (wfaAlignU3 wfaAlignU3_score wfaAlignU3_sound wfaAlignU3_isSome
  wfaAlignU3_score_eq_wfaAlign wfaAlignU3_score_fun_eq)
end AlignmentSpec

#print axioms AlignmentSpec.U32Proof.wfaAlignU3_score
#print axioms AlignmentSpec.U32Proof.wfaAlignU3_sound
#print axioms AlignmentSpec.U32Proof.wfaAlignU3_isSome
#print axioms AlignmentSpec.U32Proof.wfaAlignU3_score_fun_eq
