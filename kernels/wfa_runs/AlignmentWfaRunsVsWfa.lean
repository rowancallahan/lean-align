import AlignmentWfaRuns

/-!
Function-level equality of the fast kernels with the proven `wfaAlign`, on
scores: for every scoring and every input, `wfaAlignK` (direct run-length
traceback, kernel `wfak`) and `wfaAlignCA` (kernel `wfaca`) return exactly
the score `wfaAlign` returns.  Walks are not claimed identical: each kernel
returns its own valid optimal walk (the `_sound` theorems), and `wfaAlign`
itself is specified up to score (`wfaAlign_score`).
-/
namespace AlignmentSpec

theorem wfaAlignK_score_eq_wfaAlign (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignK sc xa ya).map Prod.snd = (wfaAlign sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignK_score, wfaAlign_score]

theorem wfaAlignCA_score_eq_wfaAlign (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignCA sc xa ya).map Prod.snd = (wfaAlign sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignCA_score, wfaAlign_score]

/-- Point-free form: the score functions are equal as functions. -/
theorem wfaAlignK_score_fun_eq :
    (fun sc (xa ya : Array Char) => (wfaAlignK sc xa ya).map Prod.snd) =
      (fun sc (xa ya : Array Char) => (wfaAlign sc xa.toList ya.toList).map Prod.snd) := by
  funext sc xa ya; exact wfaAlignK_score_eq_wfaAlign sc xa ya

#print axioms wfaAlignK_score_eq_wfaAlign
#print axioms wfaAlignCA_score_eq_wfaAlign
#print axioms wfaAlignK_score_fun_eq

end AlignmentSpec
