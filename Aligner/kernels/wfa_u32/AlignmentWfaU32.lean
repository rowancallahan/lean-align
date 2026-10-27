import AlignmentWfaU32Loop
import AlignmentWfaRunsFast

/-!
# `wfaAlignU`: the padded UInt32 kernel, proven

Fast path: the UInt32 run `uRun` (proven to return the corner level of the
offsets-only model, `uRun_eq`), an (unproven) direct run-length traceback
over its history, the proven fast run checker `checkRunsFast3` and the
offsets score identity.  A result is returned only when the checker accepts
the traceback with the certified optimal score; otherwise the proven
`wfaAlignK` answers.  Front of the chain: the exact ≤2-substitution shortcut
`compactSmall`, as in `wfaAlignK`.

Theorems: `wfaAlignU_score` (score = frozen optimum), `wfaAlignU_sound`
(returned walk valid with its true score), `wfaAlignU_isSome`, and the
function equality of the score function with `wfaAlign`
(`wfaAlignU_score_fun_eq`).
-/
namespace AlignmentSpec
open U32Proof

/-- Signed code read on the history (`-1` = no cell), as `rgetI` in
AlignmentWfaCertified.lean. -/
@[inline] def ugetI (margin : Nat) (hist : Array U32Proof.ULevel) (L' : Nat)
    (sel : U32Proof.ULevel → Array UInt32) (t : Nat) : Int :=
  if L' < hist.size then ((U32Proof.uget margin hist[L']! sel t).toNat : Int) - 1 else -1

/-- Direct run traceback over the UInt32 history: the predecessor rules and
tie order of `traceRuns` (AlignmentTraceRuns.lean).  Its output is checked
by `checkRunsFast3`; `[]` requests the proven fallback. -/
def uTraceRunsP (m n pe po px margin : Nat) (hist : Array U32Proof.ULevel) (L : Nat) :
    List (Step × Nat) := Id.run do
  let mI : Int := m
  let nI : Int := n
  let len := m + n + 1
  let mut w : List (Step × Nat) := []
  let mut L := L
  let mut t := n
  let mut front : Nat := 0
  let mut off : Int := ugetI margin hist L (·.mf) n
  let mut fuel := 4 * (m + n) + 8
  while fuel > 0 do
    fuel := fuel - 1
    if front == 0 then
      let x := ugetI margin hist L (·.xf) t
      let y := ugetI margin hist L (·.yf) t
      let s := if px ≤ L then ugetI margin hist (L - px) (·.mf) t else -1
      let j := traceJoff mI t s
      let e : Int := if s < 0 then -1 else if s < mI && j < nI then s + 1
                     else if s ≥ 1 && j ≥ 1 then s else -1
      let b1 := if x ≤ e then e else x
      let b := if L == 0 then (0 : Int) else if y ≤ b1 then b1 else y
      let k := off - b
      if k > 0 then w := (.diag, k.toNat) :: w
      if L == 0 then break
      if b == e && (x ≤ e) && (y ≤ b1) then
        if s < mI && j < nI then w := (.diag, 1) :: w
        else return []
        L := L - px; front := 0; off := s
      else if b == b1 then
        front := 1; off := x
      else
        front := 2; off := y
    else if front == 1 then
      let sa := if pe ≤ L && t ≥ 1 then ugetI margin hist (L - pe) (·.xf) (t - 1) else -1
      let sb := if po ≤ L && t ≥ 1 then ugetI margin hist (L - po) (·.mf) (t - 1) else -1
      let ja := traceJoff mI (t - 1 : Nat) sa
      let jb := traceJoff mI (t - 1 : Nat) sb
      let a : Int := if sa < 0 then -1 else if ja < nI then sa else if sa ≥ 1 && ja ≥ 1 then sa - 1 else -1
      let b : Int := if sb < 0 then -1 else if jb < nI then sb else if sb ≥ 1 && jb ≥ 1 then sb - 1 else -1
      if b ≤ a then
        L := L - pe; front := 1; off := sa
      else
        L := L - po; front := 0; off := sb
      w := (.gapX, 1) :: w
      t := t - 1
    else
      let sa := if pe ≤ L && t + 1 < len then ugetI margin hist (L - pe) (·.yf) (t + 1) else -1
      let sb := if po ≤ L && t + 1 < len then ugetI margin hist (L - po) (·.mf) (t + 1) else -1
      let ja := traceJoff mI (t + 1) sa
      let jb := traceJoff mI (t + 1) sb
      let a : Int := if sa < 0 then -1 else if sa < mI then sa + 1 else if sa ≥ 1 && ja ≥ 1 then sa else -1
      let b : Int := if sb < 0 then -1 else if sb < mI then sb + 1 else if sb ≥ 1 && jb ≥ 1 then sb else -1
      if b ≤ a then
        L := L - pe; front := 2; off := sa
      else
        L := L - po; front := 0; off := sb
      w := (.gapY, 1) :: w
      t := t + 1
  return w

def certifiedRunsU (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  if wfaGateB sc && decide (xa.size + ya.size + 2 < 2 ^ 30) then
    match U32Proof.uRun xa.size ya.size xa ya (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat with
    | none => none
    | some (L, hist) =>
      let runs := uTraceRunsP xa.size ya.size (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat
        (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) hist L
      match checkRunsFast3 sc xa ya runs ⟨0,0,none,0⟩ with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xa.size : Int) + ya.size) then some (runs.toArray, s)
        else none
  else none

theorem certifiedRunsU_spec (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : certifiedRunsU sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold certifiedRunsU at h
  split at h
  · rename_i hg
    have hg' : wfaGateB sc = true := (Bool.and_eq_true _ _).mp hg |>.1
    have hb : xa.size + ya.size + 2 < 2 ^ 30 :=
      decide_eq_true_iff.mp ((Bool.and_eq_true _ _).mp hg |>.2)
    cases hrun : U32Proof.uRun xa.size ya.size xa ya (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat with
    | none => simp [hrun] at h
    | some r =>
      obtain ⟨L, hist⟩ := r
      rw [hrun] at h
      dsimp only at h
      split at h
      · simp at h
      · rename_i score hcheck
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [checkRunsFast3_eq] at hcheck
          obtain ⟨hv, hs⟩ := checkRuns_sound sc xa ya _ score hcheck
          refine ⟨hv, hs, ?_⟩
          rw [← hs]
          apply offsets_certify_score sc xa.toList ya.toList hg' L
          · rw [← uRun_eq sc xa ya hb, hrun]; rfl
          · simpa only [Array.length_toList, ← hs, beq_iff_eq] using hc
        · simp at h
  · simp at h

/-- The kernel: exact shortcut, UInt32 fast path, proven fallback. -/
def wfaAlignU (sc : Scoring) (xa ya : Array Char) : Option (Array (Step × Nat) × Int) :=
  match compactSmall sc xa ya with
  | some r => some r
  | none =>
    match certifiedRunsU sc xa ya with
    | some r => some r
    | none => wfaAlignK sc xa ya

theorem wfaAlignU_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignU sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold wfaAlignU
  cases hc : compactSmall sc xa ya with
  | some r =>
    have h := wfaAlignHC_score sc xa ya
    simpa [wfaAlignHC,hc] using h
  | none =>
    cases hr : certifiedRunsU sc xa ya with
    | some r => exact (certifiedRunsU_spec sc xa ya r.1 r.2 hr).2.2
    | none => exact wfaAlignK_score sc xa ya

theorem wfaAlignU_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignU sc xa ya = some (c,s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  unfold wfaAlignU at h
  cases hc : compactSmall sc xa ya with
  | some r =>
    apply wfaAlignHC_sound sc xa ya c s
    simpa [wfaAlignHC,hc] using h
  | none =>
    rw [hc] at h
    cases hr : certifiedRunsU sc xa ya with
    | some r =>
      rw [hr] at h
      cases h
      exact ⟨(certifiedRunsU_spec sc xa ya c s hr).1, (certifiedRunsU_spec sc xa ya c s hr).2.1⟩
    | none =>
      rw [hr] at h
      exact wfaAlignK_sound sc xa ya c s h

theorem wfaAlignU_isSome (sc : Scoring) (xa ya : Array Char) : (wfaAlignU sc xa ya).isSome := by
  obtain ⟨best,hb⟩ := getBestAlignment_returns_some sc xa.toList ya.toList
  have h := wfaAlignU_score sc xa ya
  rw [hb] at h
  cases hw : wfaAlignU sc xa ya with
  | none => rw [hw] at h; simp at h
  | some _ => rfl

theorem wfaAlignU_score_eq_wfaAlign (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignU sc xa ya).map Prod.snd = (wfaAlign sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignU_score, wfaAlign_score]

theorem wfaAlignU_score_fun_eq :
    (fun sc (xa ya : Array Char) => (wfaAlignU sc xa ya).map Prod.snd) =
      (fun sc (xa ya : Array Char) => (wfaAlign sc xa.toList ya.toList).map Prod.snd) := by
  funext sc xa ya; exact wfaAlignU_score_eq_wfaAlign sc xa ya

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignU_score
#print axioms AlignmentSpec.wfaAlignU_sound
#print axioms AlignmentSpec.wfaAlignU_isSome
#print axioms AlignmentSpec.wfaAlignU_score_fun_eq
