import AlignmentWfaArray
import AlignmentSmallErrors
import AlignmentCompact
import AlignmentWfaRuns
import AlignmentWfaU32
import AlignmentWfaU32Kernel2
import AlignmentWfaU32Kernel3
open AlignmentSpec

def wordsC : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (wordsC n).flatMap fun w => [w, 'A' :: w, 'B' :: w]

def scoresC : List Scoring :=
  [demoScoring,
   {matchScore := 0, mismatchScore := -1, gapOpen := 0, gapExtend := -1},
   {matchScore := 0, mismatchScore := -1, gapOpen := -1, gapExtend := -1},
   {matchScore := 1, mismatchScore := -5, gapOpen := -1, gapExtend := -1},
   {matchScore := 3, mismatchScore := -2, gapOpen := -2, gapExtend := -4},
   {matchScore := -2, mismatchScore := 4, gapOpen := 2, gapExtend := 1}]

#eval do
  let mut checked := 0
  let mut rejected := 0
  let mut runRejected := 0
  let mut uRejected := 0
  let mut u2Rejected := 0
  let mut u3Rejected := 0
  let ws := (wordsC 4).eraseDups
  for sc in scoresC do
    for xs in ws do
      for ys in ws do
        let a := wfaAlignC sc xs ys
        if wfaAlignCA sc xs.toArray ys.toArray != a then
          throw (IO.userError "array/list result mismatch")
        let h := wfaAlignH sc xs.toArray ys.toArray
        let k := wfaAlignK sc xs.toArray ys.toArray
        if k.map Prod.snd != a.map Prod.snd then
          throw (IO.userError "direct run traceback score mismatch")
        let some (kc, ks) := k | throw (IO.userError "direct run traceback returned none")
        if walkCheck sc (expandCigar kc) xs ys none 0 != some ks then
          throw (IO.userError "direct run traceback is invalid")
        if wfaGateB sc && (certifiedRuns sc xs.toArray ys.toArray).isNone then
          runRejected := runRejected + 1
        let u := wfaAlignU sc xs.toArray ys.toArray
        if u.map Prod.snd != a.map Prod.snd then
          throw (IO.userError "UInt32 kernel score mismatch")
        let some (uc, us) := u | throw (IO.userError "UInt32 kernel returned none")
        if walkCheck sc (expandCigar uc) xs ys none 0 != some us then
          throw (IO.userError "UInt32 kernel traceback is invalid")
        if wfaGateB sc && (certifiedRunsU sc xs.toArray ys.toArray).isNone then
          uRejected := uRejected + 1
        let u2 := wfaAlignU2 sc xs.toArray ys.toArray
        if u2.map Prod.snd != a.map Prod.snd then
          throw (IO.userError "UInt32 kernel 2 score mismatch")
        let some (u2c, u2s) := u2 | throw (IO.userError "UInt32 kernel 2 returned none")
        if walkCheck sc (expandCigar u2c) xs ys none 0 != some u2s then
          throw (IO.userError "UInt32 kernel 2 traceback is invalid")
        if wfaGateB sc && (certifiedRunsU2 sc xs.toArray ys.toArray).isNone then
          u2Rejected := u2Rejected + 1
        let u3 := wfaAlignU3 sc xs.toArray ys.toArray
        if u3.map Prod.snd != a.map Prod.snd then
          throw (IO.userError "UInt32 kernel 3 score mismatch")
        let some (u3c, u3s) := u3 | throw (IO.userError "UInt32 kernel 3 returned none")
        if walkCheck sc (expandCigar u3c) xs ys none 0 != some u3s then
          throw (IO.userError "UInt32 kernel 3 traceback is invalid")
        if wfaGateB sc && (certifiedRunsU3 sc xs.toArray ys.toArray).isNone then
          u3Rejected := u3Rejected + 1
        let compact := (wfaAlignHC sc xs.toArray ys.toArray).map
          fun (r : Array (Step × Nat) × Int) => (expandCigar r.1, r.2)
        if compact != h then
          throw (IO.userError "compact traceback does not refine expanded result")
        if h.map Prod.snd != a.map Prod.snd then
          throw (IO.userError "small-error shortcut score mismatch")
        let some (hw, hs) := h | throw (IO.userError "small-error kernel returned none")
        if walkCheck sc hw xs ys none 0 != some hs then
          throw (IO.userError "small-error kernel returned invalid traceback")
        let b := gotohFusedAlign sc xs ys
        if a.map Prod.snd != b.map Prod.snd then
          throw (IO.userError s!"wrong score: {String.mk xs}/{String.mk ys}")
        let some (w, score) := a | throw (IO.userError "no result")
        if walkCheck sc w xs ys none 0 != some score then
          throw (IO.userError "invalid walk or score")
        if wfaGateB sc && (certifiedTraceR sc xs ys).isNone then
          rejected := rejected + 1
        checked := checked + 1
  IO.println s!"{checked} cases checked; zero mismatches; {rejected} fast-path rejections"
  IO.println s!"{runRejected} direct-run certificate rejections (exact fallback remains proved)"
  IO.println s!"{uRejected} UInt32-kernel certificate rejections (exact fallback remains proved)"
  IO.println s!"{u2Rejected} UInt32-kernel-2 certificate rejections (exact fallback remains proved)"
  IO.println s!"{u3Rejected} UInt32-kernel-3 certificate rejections (exact fallback remains proved)"

#print axioms wfaAlignC_score
#print axioms wfaAlignC_sound
#print axioms wfaAlignC_isSome
