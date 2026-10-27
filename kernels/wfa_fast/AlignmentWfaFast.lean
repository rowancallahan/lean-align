import AlignmentWfa
import AlignmentWfaFused
import AlignmentWfaLazyLevel

/-!
Executed-path variants of the proven WFA, each proven EQUAL (as a
function value) to `wfaAlign`, so every theorem about `wfaAlign`
(`wfaAlign_score`, `wfaAlign_sound`, `wfaAlign_isSome`) transfers by
rewriting.  Nothing in AlignmentWfa.lean is touched.

Variant I: the same level step, re-compiled here from local copies of
the per-cell helpers that carry `@[inline]` (attributes cannot be added
to imported declarations).  Each copy has the identical body, so its
equality with the original is `rfl`, and so is `nextLevelI = nextLevelT`.
-/

namespace AlignmentSpec

@[inline] def betterCellI : Option WCell → Option WCell → Option WCell
  | none, b => b
  | some a, none => some a
  | some a, some b => if b.off ≤ a.off then some a else some b

theorem betterCellI_eq : @betterCellI = @betterCell := rfl

@[inline] def pushGapXI (c : WCell) : Option WCell :=
  match c.ysRem with
  | _ :: yr => some ⟨c.off, c.joff + 1, c.xsRem, yr, .gapX :: c.walk⟩
  | [] => none

theorem pushGapXI_eq : @pushGapXI = @pushGapX := rfl

@[inline] def pushGapYI (c : WCell) : Option WCell :=
  match c.xsRem with
  | _ :: xr => some ⟨c.off + 1, c.joff, xr, c.ysRem, .gapY :: c.walk⟩
  | [] => none

theorem pushGapYI_eq : @pushGapYI = @pushGapY := rfl

@[inline] def pushDiagI (c : WCell) : Option WCell :=
  match c.xsRem, c.ysRem with
  | _ :: xr, _ :: yr =>
      some ⟨c.off + 1, c.joff + 1, xr, yr, .diag :: c.walk⟩
  | _, _ => none

theorem pushDiagI_eq : @pushDiagI = @pushDiag := rfl

@[inline] def stepWithI (push : WCell → Option WCell) (xs ys : List Char) :
    Option WCell → Option WCell
  | some c =>
      match push c with
      | some r => some r
      | none => (demoteCell xs ys c).bind push
  | none => none

theorem stepWithI_eq : @stepWithI = @stepWith := rfl

@[inline] def extendCellI (c : WCell) : WCell :=
  extendGo c.off c.joff c.walk c.xsRem c.ysRem

theorem extendCellI_eq : @extendCellI = @extendCell := rfl

@[inline] def zipTI : TFront → TFront → TFront
  | ⟨_, []⟩, g => g
  | f, ⟨_, []⟩ => f
  | ⟨p, a⟩, ⟨q, b⟩ =>
      let lo := min p q
      ⟨lo, zipExt (List.replicate (p - lo) none ++ a)
        (List.replicate (q - lo) none ++ b)⟩

theorem zipTI_eq : @zipTI = @zipT := rfl

@[inline] def shiftUpTI (f : TFront) : TFront := ⟨f.pad + 1, f.body⟩

theorem shiftUpTI_eq : @shiftUpTI = @shiftUpT := rfl

@[inline] def shiftDownTI (len : Nat) (f : TFront) : TFront :=
  match f.pad with
  | p + 1 => ⟨p, f.body.take (len - (p + 1))⟩
  | 0 => ⟨0, (f.body.drop 1).take (len - 1)⟩

theorem shiftDownTI_eq : @shiftDownTI = @shiftDownT := rfl

@[inline] def mapTI (g : Option WCell → Option WCell) (f : TFront) : TFront :=
  ⟨f.pad, f.body.map g⟩

theorem mapTI_eq : @mapTI = @mapT := rfl

@[inline] def frontAtTI (hist : List TLevel) (delta : Nat)
    (sel : TLevel → TFront) : TFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => ⟨0, []⟩

theorem frontAtTI_eq : @frontAtTI = @frontAtT := rfl

@[inline] def tgetTI (f : TFront) (n : Nat) : Option WCell :=
  if n < f.pad then none else (f.body[n - f.pad]?).getD none

theorem tgetTI_eq : @tgetTI = @tgetT := rfl

@[inline] def cornerOfTI (n : Nat) (lv : TLevel) : Option WCell :=
  match tgetTI lv.mf n with
  | some c =>
      match c.xsRem, c.ysRem with
      | [], [] => some c
      | _, _ => none
  | none => none

theorem cornerOfTI_eq : @cornerOfTI = @cornerOfT := rfl

def nextLevelI (xs ys : List Char) (len : Nat) (pe po px : Nat)
    (hist : List TLevel) : TLevel :=
  let xf := zipTI
    (shiftUpTI (mapTI (stepWithI pushGapXI xs ys) (frontAtTI hist pe (·.xf))))
    (shiftUpTI (mapTI (stepWithI pushGapXI xs ys) (frontAtTI hist po (·.mf))))
  let yf := zipTI
    (shiftDownTI len
      (mapTI (stepWithI pushGapYI xs ys) (frontAtTI hist pe (·.yf))))
    (shiftDownTI len
      (mapTI (stepWithI pushGapYI xs ys) (frontAtTI hist po (·.mf))))
  let base := zipTI (zipTI
    (mapTI (stepWithI pushDiagI xs ys) (frontAtTI hist px (·.mf))) xf) yf
  ⟨mapTI (Option.map extendCellI) base, xf, yf⟩

theorem nextLevelI_eq (xs ys : List Char) (len pe po px : Nat)
    (hist : List TLevel) :
    nextLevelI xs ys len pe po px hist = nextLevelT xs ys len pe po px hist :=
  rfl

def wfaLoopI (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List TLevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevelI xs ys len pe po px hist
      match cornerOfTI n lv with
      | some c => some c
      | none =>
          wfaLoopI xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

theorem wfaLoopI_eq (xs ys : List Char) (len n pe po px : Nat) :
    ∀ (fuel : Nat) (hist : List TLevel),
      wfaLoopI xs ys len n pe po px fuel hist =
        wfaLoopT xs ys len n pe po px fuel hist := by
  intro fuel
  induction fuel with
  | zero => intro hist; rfl
  | succ f ih =>
      intro hist
      simp only [wfaLoopI, wfaLoopT, nextLevelI_eq, cornerOfTI_eq]
      cases cornerOfT n (nextLevelT xs ys len pe po px hist) with
      | some c => rfl
      | none => exact ih _

def wfaRunI (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevelT m xs ys
  let result :=
    match cornerOfTI n lv0 with
    | some c => some c
    | none => wfaLoopI xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

theorem wfaRunI_eq (sc : Scoring) (xs ys : List Char) :
    wfaRunI sc xs ys = wfaRunT sc xs ys := by
  simp only [wfaRunI, wfaRunT, cornerOfTI_eq]
  rw [wfaLoopI_eq]
  rfl

/-- Same gate, same fallback, same result as `wfaAlign`. -/
def wfaAlignI (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunI sc xs ys with
    | some r => some r
    | none => gotohFusedAlign sc xs ys
  else gotohFusedAlign sc xs ys

/-- Function equality with the proven kernel: every `wfaAlign` theorem
transfers by `rw [wfaAlignI_eq]`. -/
theorem wfaAlignI_eq (sc : Scoring) (xs ys : List Char) :
    wfaAlignI sc xs ys = wfaAlign sc xs ys := by
  simp only [wfaAlignI, wfaAlign]
  rw [wfaRunI_eq]
  rfl

theorem wfaAlignI_score (sc : Scoring) (xs ys : List Char) :
    (wfaAlignI sc xs ys).map (fun r => r.2) =
      (getBestAlignment sc xs ys).map (fun r => r.2) := by
  rw [wfaAlignI_eq]; exact wfaAlign_score sc xs ys

theorem wfaAlignI_sound (sc : Scoring) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaAlignI sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  rw [wfaAlignI_eq] at h; exact wfaAlign_sound sc xs ys w s h

theorem wfaAlignI_isSome (sc : Scoring) (xs ys : List Char) :
    (wfaAlignI sc xs ys).isSome := by
  rw [wfaAlignI_eq]; exact wfaAlign_isSome sc xs ys

#print axioms wfaAlignI_eq

end AlignmentSpec

/-!
Variant F: the fused level step from AlignmentWfaFused.lean
(`nextLevelF`, proven `= nextLevelT` by `nextLevelF_eq`), same loop.
-/
namespace AlignmentSpec

def wfaLoopF (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List TLevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevelF xs ys len pe po px hist
      match cornerOfTI n lv with
      | some c => some c
      | none =>
          wfaLoopF xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

theorem wfaLoopF_eq (xs ys : List Char) (len n pe po px : Nat) :
    ∀ (fuel : Nat) (hist : List TLevel),
      wfaLoopF xs ys len n pe po px fuel hist =
        wfaLoopT xs ys len n pe po px fuel hist := by
  intro fuel
  induction fuel with
  | zero => intro hist; rfl
  | succ f ih =>
      intro hist
      simp only [wfaLoopF, wfaLoopT, nextLevelF_eq, cornerOfTI_eq]
      cases cornerOfT n (nextLevelT xs ys len pe po px hist) with
      | some c => rfl
      | none => exact ih _

def wfaRunF (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevelT m xs ys
  let result :=
    match cornerOfTI n lv0 with
    | some c => some c
    | none => wfaLoopF xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

theorem wfaRunF_eq (sc : Scoring) (xs ys : List Char) :
    wfaRunF sc xs ys = wfaRunT sc xs ys := by
  simp only [wfaRunF, wfaRunT, cornerOfTI_eq]
  rw [wfaLoopF_eq]
  rfl

def wfaAlignF (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunF sc xs ys with
    | some r => some r
    | none => gotohFusedAlign sc xs ys
  else gotohFusedAlign sc xs ys

theorem wfaAlignF_eq (sc : Scoring) (xs ys : List Char) :
    wfaAlignF sc xs ys = wfaAlign sc xs ys := by
  simp only [wfaAlignF, wfaAlign]
  rw [wfaRunF_eq]
  rfl

theorem wfaAlignF_score (sc : Scoring) (xs ys : List Char) :
    (wfaAlignF sc xs ys).map (fun r => r.2) =
      (getBestAlignment sc xs ys).map (fun r => r.2) := by
  rw [wfaAlignF_eq]; exact wfaAlign_score sc xs ys

theorem wfaAlignF_sound (sc : Scoring) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaAlignF sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  rw [wfaAlignF_eq] at h; exact wfaAlign_sound sc xs ys w s h

theorem wfaAlignF_isSome (sc : Scoring) (xs ys : List Char) :
    (wfaAlignF sc xs ys).isSome := by
  rw [wfaAlignF_eq]; exact wfaAlign_isSome sc xs ys

#print axioms wfaAlignF_eq

end AlignmentSpec

/-!
Variant L: the fused level with lazy candidate selection from
AlignmentWfaLazyLevel.lean (`nextLevelL`, proven `= nextLevelT` by
`nextLevelL_eq`), same loop.
-/
namespace AlignmentSpec

def wfaLoopL (xs ys : List Char) (len n : Nat) (pe po px : Nat) :
    Nat → List TLevel → Option WCell
  | 0, _ => none
  | fuel + 1, hist =>
      let lv := nextLevelL xs ys len pe po px hist
      match cornerOfTI n lv with
      | some c => some c
      | none =>
          wfaLoopL xs ys len n pe po px fuel
            ((lv :: hist).take (max pe (max po px)))

theorem wfaLoopL_eq (xs ys : List Char) (len n pe po px : Nat) :
    ∀ (fuel : Nat) (hist : List TLevel),
      wfaLoopL xs ys len n pe po px fuel hist =
        wfaLoopT xs ys len n pe po px fuel hist := by
  intro fuel
  induction fuel with
  | zero => intro hist; rfl
  | succ f ih =>
      intro hist
      simp only [wfaLoopL, wfaLoopT, nextLevelL_eq, cornerOfTI_eq]
      cases cornerOfT n (nextLevelT xs ys len pe po px hist) with
      | some c => rfl
      | none => exact ih _

def wfaRunL (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedLevelT m xs ys
  let result :=
    match cornerOfTI n lv0 with
    | some c => some c
    | none => wfaLoopL xs ys len n pe po px ((m + n + 2) * po + 1) [lv0]
  result.map fun c =>
    let w := c.walk.reverse
    (w, walkScore sc xs ys w)

theorem wfaRunL_eq (sc : Scoring) (xs ys : List Char) :
    wfaRunL sc xs ys = wfaRunT sc xs ys := by
  simp only [wfaRunL, wfaRunT, cornerOfTI_eq]
  rw [wfaLoopL_eq]
  rfl

def wfaAlignL (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  if wfaGateB sc then
    match wfaRunL sc xs ys with
    | some r => some r
    | none => gotohFusedAlign sc xs ys
  else gotohFusedAlign sc xs ys

theorem wfaAlignL_eq (sc : Scoring) (xs ys : List Char) :
    wfaAlignL sc xs ys = wfaAlign sc xs ys := by
  simp only [wfaAlignL, wfaAlign]
  rw [wfaRunL_eq]
  rfl

theorem wfaAlignL_score (sc : Scoring) (xs ys : List Char) :
    (wfaAlignL sc xs ys).map (fun r => r.2) =
      (getBestAlignment sc xs ys).map (fun r => r.2) := by
  rw [wfaAlignL_eq]; exact wfaAlign_score sc xs ys

theorem wfaAlignL_sound (sc : Scoring) (xs ys : List Char)
    (w : List Step) (s : Int) (h : wfaAlignL sc xs ys = some (w, s)) :
    IsMonotoneWalk w xs ys ∧ walkScore sc xs ys w = s := by
  rw [wfaAlignL_eq] at h; exact wfaAlign_sound sc xs ys w s h

theorem wfaAlignL_isSome (sc : Scoring) (xs ys : List Char) :
    (wfaAlignL sc xs ys).isSome := by
  rw [wfaAlignL_eq]; exact wfaAlign_isSome sc xs ys

#print axioms wfaAlignL_eq

end AlignmentSpec
