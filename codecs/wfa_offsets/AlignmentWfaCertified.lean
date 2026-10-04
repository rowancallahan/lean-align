import AlignmentWfaOffR
import AlignmentWfaPoint
import AlignmentWfaOffLoop
import AlignmentWfaFast

/-!
Offsets-only WFA with a checked traceback. The forward recurrence is proved
by refinement to the existing complete wavefront model. Traceback is accepted
only when its consumed lengths and exact score equal that proved optimum.
A rejected traceback uses the already-proved WFA. The exported correctness
statements are universal, including inputs/scorings outside the fast gate.

Algorithm reference: Marco-Sola et al., Fast gap-affine pairwise alignment
using the wavefront algorithm, Bioinformatics (2021), doi:10.1093/bioinformatics/btaa777.
Stored offsets followed by backtrace: https://github.com/smarco/WFA2-lib .
This is forward WFA, not the bidirectional BiWFA algorithm.
-/
namespace AlignmentSpec

def wfaLoopR (m n : Nat) (xa ya : Array Char) (len pe po px : Nat) :
    Nat → List RLevel → Nat → Array RLevel → Option (Nat × Array RLevel)
  | 0, _, _, _ => none
  | fuel + 1, hist, p, trace =>
      let lv := nextLevelP m n xa ya len pe po px hist
      let trace := trace.push lv
      if cornerR m n lv then some (p, trace)
      else wfaLoopR m n xa ya len pe po px fuel
        ((lv :: hist).take (max pe (max po px))) (p + 1) trace

theorem wfaLoopR_eq (m n : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) (pe po px : Nat) :
    ∀ fuel hist p trace,
    (wfaLoopR m n xa ya (m + n + 1) pe po px fuel hist p trace).map Prod.fst =
      wfaLoopO m n xs ys (m + n + 1) pe po px fuel
        (hist.map (rdenL (m + n + 1))) p := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist p trace
    simp only [wfaLoopR, wfaLoopO, nextLevelP_eq]
    rw [← rdenL_nextLevelR m n xs ys xa ya hx hy _ pe po px hist rfl,
      ← cornerR_eq m n (m + n + 1) (by omega)]
    split
    · rfl
    · rw [ih, List.map_take, List.map_cons]

def wfaRunR (sc : Scoring) (xs ys : List Char) : Option (Nat × Array RLevel) :=
  let m := xs.length
  let n := ys.length
  let xa := xs.toArray
  let ya := ys.toArray
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv := seedR m (m + n + 1) xa ya
  if cornerR m n lv then some (0, #[lv])
  else wfaLoopR m n xa ya (m + n + 1) pe po px
    ((m + n + 2) * po + 1) [lv] 1 #[lv]

theorem wfaRunR_eq (sc : Scoring) (xs ys : List Char) :
    (wfaRunR sc xs ys).map Prod.fst = wfaRunO sc xs ys := by
  simp only [wfaRunR, wfaRunO]
  rw [cornerR_eq xs.length ys.length (xs.length + ys.length + 1) (by omega),
    rdenL_seedR xs.length _ xs ys _ _ (by simp) (by simp) (by omega)]
  split
  · rfl
  · rw [wfaLoopR_eq _ _ xs ys _ _ (by simp) (by simp)]
    simp only [List.map_cons, List.map_nil]
    rw [rdenL_seedR xs.length (xs.length + ys.length + 1) xs ys xs.toArray ys.toArray
      (by simp) (by simp) (by omega)]

/-- A walk with the penalty certified by the offsets run has the optimum score. -/
theorem offsets_certify_score (sc : Scoring) (xs ys : List Char)
    (hg : wfaGateB sc) (L : Nat) (hL : wfaRunO sc xs ys = some L)
    (w : List Step)
    (hs : 2 * walkScore sc xs ys w + (L : Int) =
      sc.matchScore * ((xs.length : Int) + ys.length)) :
    some (walkScore sc xs ys w) = (getBestAlignment sc xs ys).map Prod.snd := by
  obtain ⟨hr, hpe, hpx⟩ := wfaGate_spec sc hg
  obtain ⟨wr, sr, hrun, heq⟩ := wfaRunO_spec sc hr hpe hpx xs ys L hL
  have hscore := wfaAlign_score sc xs ys
  unfold wfaAlign at hscore
  rw [wfaRunT_eq, if_pos hg, hrun] at hscore
  simp only [Option.map_some] at hscore
  have : walkScore sc xs ys w = sr := by omega
  simpa only [this] using hscore

@[inline] def rgetI (f : RFront) (t : Nat) : Int := (rget f t : Int) - 1
@[inline] def traceJoff (m t off : Int) : Int := off + t - m

/-- Reconstruct from offset history; the certificate below checks this result. -/
def traceR (m n : Nat) (pe po px : Nat) (hist : Array RLevel)
    (L : Nat) : List Step := Id.run do
  let mI : Int := m
  let nI : Int := n
  let get := fun (L' : Nat) (sel : RLevel → RFront) => sel hist[L']!
  let mut w : List Step := []      -- reversed walk (head = last step)
  let mut L := L
  let mut t := n
  let mut front : Nat := 0         -- 0 = mf, 1 = xf, 2 = yf
  let mut off : Int := rgetI (get L (·.mf)) n
  let mut fuel := 4 * (m + n) + 8
  while fuel > 0 do
    fuel := fuel - 1
    if front == 0 then
      -- mf cell: undo extension, then find base winner
      let x := rgetI (get L (·.xf)) t
      let y := rgetI (get L (·.yf)) t
      let s := if px ≤ L then rgetI (get (L - px) (·.mf)) t else -1
      let j := traceJoff mI t s
      let e : Int := if s < 0 then -1 else if s < mI && j < nI then s + 1
                     else if s ≥ 1 && j ≥ 1 then s else -1
      let b1 := if x ≤ e then e else x
      let b := if L == 0 then (0 : Int) else if y ≤ b1 then b1 else y
      -- extension steps
      let mut k := off - b
      while k > 0 do
        w := .diag :: w; k := k - 1
      if L == 0 then break
      if b == e && (x ≤ e) && (y ≤ b1) then
        -- diagonal step from mf[L-px][t] (source offset s)
        if s < mI && j < nI then w := .diag :: w
        else w := .diag :: (demoteWalk w).getD w   -- rejected by the certificate if boundary surgery is needed
        L := L - px; front := 0; off := s
      else if b == b1 then
        front := 1; off := x
      else
        front := 2; off := y
    else if front == 1 then
      -- xf[L][t] = better(gapX xf[L-pe][t-1], gapX mf[L-po][t-1])
      let sa := if pe ≤ L && t ≥ 1 then rgetI (get (L - pe) (·.xf)) (t - 1) else -1
      let sb := if po ≤ L && t ≥ 1 then rgetI (get (L - po) (·.mf)) (t - 1) else -1
      let ja := traceJoff mI (t - 1 : Nat) sa
      let jb := traceJoff mI (t - 1 : Nat) sb
      let a : Int := if sa < 0 then -1 else if ja < nI then sa else if sa ≥ 1 && ja ≥ 1 then sa - 1 else -1
      let b : Int := if sb < 0 then -1 else if jb < nI then sb else if sb ≥ 1 && jb ≥ 1 then sb - 1 else -1
      if b ≤ a then
        L := L - pe; front := 1; off := sa
        w := .gapX :: w
      else
        L := L - po; front := 0; off := sb
        w := .gapX :: w
      t := t - 1
    else
      let sa := if pe ≤ L && t + 1 < m + n + 1 then rgetI (get (L - pe) (·.yf)) (t + 1) else -1
      let sb := if po ≤ L && t + 1 < m + n + 1 then rgetI (get (L - po) (·.mf)) (t + 1) else -1
      let ja := traceJoff mI (t + 1) sa
      let jb := traceJoff mI (t + 1) sb
      let a : Int := if sa < 0 then -1 else if sa < mI then sa + 1 else if sa ≥ 1 && ja ≥ 1 then sa else -1
      let b : Int := if sb < 0 then -1 else if sb < mI then sb + 1 else if sb ≥ 1 && jb ≥ 1 then sb else -1
      if b ≤ a then
        L := L - pe; front := 2; off := sa
        w := .gapY :: w
      else
        L := L - po; front := 0; off := sb
        w := .gapY :: w
      t := t + 1
  return w


/-- Check consumption and compute the exact affine score in one tail-recursive pass. -/
def walkCheck (sc : Scoring) : List Step → List Char → List Char → Option Step → Int → Option Int
  | [], [], [], _, acc => some acc
  | .diag :: w, x :: xs, y :: ys, _, acc =>
      walkCheck sc w xs ys (some .diag) (acc + diagCost sc x y)
  | .gapX :: w, xs, _ :: ys, prev, acc =>
      walkCheck sc w xs ys (some .gapX) (acc + gapXCost sc prev)
  | .gapY :: w, _ :: xs, ys, prev, acc =>
      walkCheck sc w xs ys (some .gapY) (acc + gapYCost sc prev)
  | _, _, _, _, _ => none

theorem walkCheck_sound (sc : Scoring) (w : List Step) :
    ∀ xs ys prev acc s, walkCheck sc w xs ys prev acc = some s →
      IsMonotoneWalk w xs ys ∧ acc + scoreWalk sc w xs ys prev = s := by
  induction w with
  | nil =>
    intro xs ys prev acc s h
    cases xs <;> cases ys <;> simp_all [walkCheck, IsMonotoneWalk, scoreWalk]
  | cons step w ih =>
    intro xs ys prev acc s h
    cases step <;> cases xs <;> cases ys <;>
      simp only [walkCheck, reduceCtorEq] at h
    all_goals try contradiction
    all_goals
      obtain ⟨hv, hs⟩ := ih _ _ _ _ _ h
      obtain ⟨hx, hy⟩ := hv
      constructor
      · constructor <;> simp_all [List.map_cons, List.sum_cons, xConsumed, yConsumed, Nat.add_comm]
      · simp only [scoreWalk, diagCost, gapXCost, gapYCost] at *; omega

/-- The complete fast-path certificate includes optimality, not only validity. -/
def certifiedTraceR (sc : Scoring) (xs ys : List Char) : Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunR sc xs ys with
    | none => none
    | some (L, hist) =>
      let w := traceR xs.length ys.length (wfaPe sc).toNat (wfaPo sc).toNat
        (wfaPx sc).toNat hist L
      match walkCheck sc w xs ys none 0 with
      | none => none
      | some s =>
        if 2 * s + (L : Int) == sc.matchScore * ((xs.length : Int) + ys.length) then
          some (w, s)
        else none
  else none

theorem certifiedTraceR_spec (sc : Scoring) (xs ys : List Char)
    (w : List Step) (s : Int) (h : certifiedTraceR sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s ∧
      some s = (getBestAlignment sc xs ys).map Prod.snd := by
  unfold certifiedTraceR at h
  split at h
  · rename_i hg
    cases hrun : wfaRunR sc xs ys with
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
          obtain ⟨hv, hs⟩ := walkCheck_sound sc _ xs ys none 0 score hcheck
          simp only [Int.zero_add] at hs
          refine ⟨hv, hs, ?_⟩
          rw [← hs]
          apply offsets_certify_score sc xs ys hg L
          · rw [← wfaRunR_eq, hrun]; rfl
          · simpa only [← hs, beq_iff_eq, walkScore] using hc
        · simp at h
  · simp at h

def wfaAlignC (sc : Scoring) (xs ys : List Char) : Option (List Step × Int) :=
  match certifiedTraceR sc xs ys with
  | some r => some r
  | none => wfaAlignL sc xs ys

theorem wfaAlignC_score (sc : Scoring) (xs ys : List Char) :
    (wfaAlignC sc xs ys).map Prod.snd = (getBestAlignment sc xs ys).map Prod.snd := by
  unfold wfaAlignC
  cases h : certifiedTraceR sc xs ys with
  | none => exact wfaAlignL_score sc xs ys
  | some r => exact (certifiedTraceR_spec sc xs ys r.1 r.2 h).2.2

theorem wfaAlignC_sound (sc : Scoring) (xs ys : List Char) (w : List Step) (s : Int)
    (h : wfaAlignC sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  unfold wfaAlignC at h
  cases hr : certifiedTraceR sc xs ys with
  | none => rw [hr] at h; exact wfaAlignL_sound sc xs ys w s h
  | some r =>
    rw [hr] at h
    cases h
    exact ⟨(certifiedTraceR_spec sc xs ys w s hr).1,
      (certifiedTraceR_spec sc xs ys w s hr).2.1⟩

theorem wfaAlignC_isSome (sc : Scoring) (xs ys : List Char) :
    (wfaAlignC sc xs ys).isSome := by
  obtain ⟨best, hb⟩ := getBestAlignment_returns_some sc xs ys
  have h := wfaAlignC_score sc xs ys
  rw [hb] at h
  cases hw : wfaAlignC sc xs ys with
  | none => rw [hw] at h; simp at h
  | some _ => rfl

end AlignmentSpec
#print axioms AlignmentSpec.wfaAlignC_score
#print axioms AlignmentSpec.wfaAlignC_sound
#print axioms AlignmentSpec.wfaAlignC_isSome
