import AlignmentWfa

/-!
# Offsets-only view of the proven wavefront (layer O)

The model (`nextLevel` / `wfaLoop` in AlignmentWfa.lean) carries a full
`WCell` per diagonal: offsets, string remainders and the walk.  Under
the model's own invariant (`CellOK` + the diagonal relation in
`FrontOK`), every push, demotion and extension is a function of the
offsets alone.  This file defines the offsets-only level step
`nextLevelO` and proves that projecting the model's level to offsets
(`projL`) commutes with it, and that the corner test is an offset test.

Nothing here is executed for speed; it is the proof bridge between the
model and the array-backed executed path (AlignmentWfaOffR.lean).
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- Definitions
-- ══════════════════════════════════════════════════════════════════

/-- The offset of an optional cell. -/
def offOf : Option WCell → Option Nat := Option.map (·.off)

abbrev OFrontW := List (Option Nat)

structure OLevelW where
  mf : OFrontW
  xf : OFrontW
  yf : OFrontW

def projF (f : WFront) : OFrontW := f.map offOf

def projL (lv : WLevel) : OLevelW := ⟨projF lv.mf, projF lv.xf, projF lv.yf⟩

/-- Left-biased choice of the larger offset (mirrors `betterCell`). -/
def betterO : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => if b ≤ a then some a else some b

/-- Length of the common prefix. -/
def lcp : List Char → List Char → Nat
  | x :: xr, y :: yr => if x = y then lcp xr yr + 1 else 0
  | _, _ => 0

/-- On diagonal `t` (index `t = joff − off + m`) a cell at offset `off`
has `joff = off + t − m`. -/
@[inline] def joffOf (m t off : Nat) : Nat := off + t - m

/-- gap-in-x push of the source cell on diagonal `t`: consumes one y
(`joff + 1`, `off` unchanged); pinned at the y end it demotes one
diagonal step first (`off − 1`), which needs `off ≥ 1` and `joff ≥ 1`. -/
def pushXO (m n t off : Nat) : Option Nat :=
  if joffOf m t off < n then some off
  else if 1 ≤ off ∧ 1 ≤ joffOf m t off then some (off - 1) else none

def pushYO (m n t off : Nat) : Option Nat :=
  if off < m then some (off + 1)
  else if 1 ≤ off ∧ 1 ≤ joffOf m t off then some off else none

def pushDO (m n t off : Nat) : Option Nat :=
  if off < m ∧ joffOf m t off < n then some (off + 1)
  else if 1 ≤ off ∧ 1 ≤ joffOf m t off then some off else none

def extO (m : Nat) (xs ys : List Char) (t off : Nat) : Nat :=
  off + lcp (xs.drop off) (ys.drop (joffOf m t off))

/-- Index-aware map from start index `t0` (`none` stays `none`). -/
def mapFrom (g : Nat → Nat → Option Nat) : Nat → OFrontW → OFrontW
  | _, [] => []
  | t, o :: rest => (o.bind (g t)) :: mapFrom g (t + 1) rest

def shiftUpO (f : OFrontW) : OFrontW := none :: f.dropLast
def shiftDownO (f : OFrontW) : OFrontW := f.drop 1 ++ [none]

def frontAtO (len : Nat) (hist : List OLevelW) (delta : Nat)
    (sel : OLevelW → OFrontW) : OFrontW :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => List.replicate len none

def nextLevelO (m n : Nat) (xs ys : List Char) (len : Nat)
    (pe po px : Nat) (hist : List OLevelW) : OLevelW :=
  let xf := List.zipWith betterO
    (shiftUpO (mapFrom (pushXO m n) 0 (frontAtO len hist pe (·.xf))))
    (shiftUpO (mapFrom (pushXO m n) 0 (frontAtO len hist po (·.mf))))
  let yf := List.zipWith betterO
    (shiftDownO (mapFrom (pushYO m n) 0 (frontAtO len hist pe (·.yf))))
    (shiftDownO (mapFrom (pushYO m n) 0 (frontAtO len hist po (·.mf))))
  let base := List.zipWith betterO
    (List.zipWith betterO
      (mapFrom (pushDO m n) 0 (frontAtO len hist px (·.mf))) xf) yf
  ⟨mapFrom (fun t off => some (extO m xs ys t off)) 0 base, xf, yf⟩

def seedO (m len : Nat) (xs ys : List Char) : OLevelW :=
  ⟨(List.replicate len (none : Option Nat)).set m (some (lcp xs ys)),
   List.replicate len none, List.replicate len none⟩

/-- The corner is reached when the cell on diagonal `n` has offset `m`. -/
def cornerO (m n : Nat) (lv : OLevelW) : Bool :=
  lv.mf[n]? == some (some m)

-- ══════════════════════════════════════════════════════════════════
-- Per-cell lemmas
-- ══════════════════════════════════════════════════════════════════

theorem offOf_betterCell (a b : Option WCell) :
    offOf (betterCell a b) = betterO (offOf a) (offOf b) := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      by_cases h : b.off ≤ a.off <;> simp [betterCell, offOf, betterO, h]

theorem extendGo_off_eq : ∀ (xr yr : List Char) (i j : Nat) (w : List Step),
    (extendGo i j w xr yr).off = i + lcp xr yr := by
  intro xr
  induction xr with
  | nil => intro yr i j w; cases yr <;> simp [extendGo, lcp]
  | cons x xr ih =>
    intro yr i j w
    cases yr with
    | nil => simp [extendGo, lcp]
    | cons y yr =>
      simp only [extendGo, lcp]
      split
      · rw [ih]; omega
      · simp

theorem pushGapX_none_iff (c : WCell) : pushGapX c = none ↔ c.ysRem = [] := by
  cases h : c.ysRem <;> simp [pushGapX, h]

theorem pushGapY_none_iff (c : WCell) : pushGapY c = none ↔ c.xsRem = [] := by
  cases h : c.xsRem <;> simp [pushGapY, h]

theorem pushDiag_none_iff (c : WCell) :
    pushDiag c = none ↔ c.xsRem = [] ∨ c.ysRem = [] := by
  cases hx : c.xsRem <;> cases hy : c.ysRem <;> simp [pushDiag, hx, hy]

theorem demoteCell_none_of (xs ys : List Char) (c : WCell)
    (h : ¬ (1 ≤ c.off ∧ 1 ≤ c.joff)) : demoteCell xs ys c = none := by
  unfold demoteCell
  cases hi : c.off with
  | zero => rfl
  | succ i =>
    cases hj : c.joff with
    | zero => rfl
    | succ j => exfalso; omega

/-- Under the invariant, a gap-in-x step is the offset function. -/
theorem offOf_stepX (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t) :
    offOf (stepWith pushGapX xs ys (some c)) =
      pushXO xs.length ys.length t c.off := by
  have hj : joffOf xs.length t c.off = c.joff := by unfold joffOf; omega
  simp only [stepWith]
  cases hp : pushGapX c with
  | some c' =>
    obtain ⟨hc', hlt, _⟩ := pushGapX_core sc xs ys c c' p hok hp
    subst hc'
    simp [offOf, pushXO, hj, hlt]
  | none =>
    have hys : c.ysRem = [] := (pushGapX_none_iff c).1 hp
    rw [hok.hys] at hys
    have hjn : ys.length ≤ c.joff := List.drop_eq_nil_iff.1 hys
    have hnlt : ¬ joffOf xs.length t c.off < ys.length := by omega
    by_cases hpos : 1 ≤ c.off ∧ 1 ≤ c.joff
    · obtain ⟨d, hdm, hdo, hdj, hdx, hdy⟩ :=
        demoteCell_isSome sc xs ys c p hok hpos.1 hpos.2
      rw [hdm]
      have hdys : d.ysRem ≠ [] := by
        rw [hdy]; intro hnil
        have := List.drop_eq_nil_iff.1 hnil
        have := hok.hjoff
        omega
      have hnlt' : ¬ c.joff < ys.length := by omega
      cases hdr : d.ysRem with
      | nil => exact absurd hdr hdys
      | cons y yr =>
        simp [pushGapX, hdr, offOf, pushXO, hj, hnlt', hpos]
        omega
    · have hnlt' : ¬ c.joff < ys.length := by omega
      rw [demoteCell_none_of xs ys c hpos]
      simp [offOf, pushXO, hj, hnlt', hpos]

theorem offOf_stepY (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t) :
    offOf (stepWith pushGapY xs ys (some c)) =
      pushYO xs.length ys.length t c.off := by
  have hj : joffOf xs.length t c.off = c.joff := by unfold joffOf; omega
  simp only [stepWith]
  cases hp : pushGapY c with
  | some c' =>
    obtain ⟨hc', hlt, _⟩ := pushGapY_core sc xs ys c c' p hok hp
    subst hc'
    simp [offOf, pushYO, hlt]
  | none =>
    have hxs : c.xsRem = [] := (pushGapY_none_iff c).1 hp
    rw [hok.hxs] at hxs
    have hom : xs.length ≤ c.off := List.drop_eq_nil_iff.1 hxs
    have hnlt : ¬ c.off < xs.length := by omega
    by_cases hpos : 1 ≤ c.off ∧ 1 ≤ c.joff
    · obtain ⟨d, hdm, hdo, hdj, hdx, hdy⟩ :=
        demoteCell_isSome sc xs ys c p hok hpos.1 hpos.2
      rw [hdm]
      have hdxs : d.xsRem ≠ [] := by
        rw [hdx]; intro hnil
        have := List.drop_eq_nil_iff.1 hnil
        have := hok.hoff
        omega
      cases hdr : d.xsRem with
      | nil => exact absurd hdr hdxs
      | cons x xr =>
        simp [pushGapY, hdr, offOf, pushYO, hj, hnlt, hpos]
        omega
    · rw [demoteCell_none_of xs ys c hpos]
      simp [offOf, pushYO, hj, hnlt, hpos]

theorem offOf_stepD (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t) :
    offOf (stepWith pushDiag xs ys (some c)) =
      pushDO xs.length ys.length t c.off := by
  have hj : joffOf xs.length t c.off = c.joff := by unfold joffOf; omega
  simp only [stepWith]
  cases hp : pushDiag c with
  | some c' =>
    obtain ⟨hc', hlt1, hlt2, _⟩ := pushDiag_core sc xs ys c c' p hok hp
    subst hc'
    simp [offOf, pushDO, hj, hlt1, hlt2]
  | none =>
    have hor := (pushDiag_none_iff c).1 hp
    have hnlt : ¬ (c.off < xs.length ∧ c.joff < ys.length) := by
      rcases hor with h | h
      · rw [hok.hxs] at h; have := List.drop_eq_nil_iff.1 h; omega
      · rw [hok.hys] at h; have := List.drop_eq_nil_iff.1 h; omega
    by_cases hpos : 1 ≤ c.off ∧ 1 ≤ c.joff
    · obtain ⟨d, hdm, hdo, hdj, hdx, hdy⟩ :=
        demoteCell_isSome sc xs ys c p hok hpos.1 hpos.2
      rw [hdm]
      have hdxs : d.xsRem ≠ [] := by
        rw [hdx]; intro hnil
        have := List.drop_eq_nil_iff.1 hnil
        have := hok.hoff
        omega
      have hdys : d.ysRem ≠ [] := by
        rw [hdy]; intro hnil
        have := List.drop_eq_nil_iff.1 hnil
        have := hok.hjoff
        omega
      cases hdr : d.xsRem with
      | nil => exact absurd hdr hdxs
      | cons x xr =>
        cases hdr' : d.ysRem with
        | nil => exact absurd hdr' hdys
        | cons y yr =>
          simp [pushDiag, hdr, hdr', offOf, pushDO, hj, hnlt, hpos]
          omega
    · rw [demoteCell_none_of xs ys c hpos]
      simp [offOf, pushDO, hj, hnlt, hpos]

/-- Position facts a pushed cell carries (no walk information). -/
structure CellPos (xs ys : List Char) (c : WCell) : Prop where
  hxs : c.xsRem = xs.drop c.off
  hys : c.ysRem = ys.drop c.joff

theorem stepX_pos (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c c' : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t)
    (h : stepWith pushGapX xs ys (some c) = some c') :
    CellPos xs ys c' ∧ c'.joff + xs.length = c'.off + (t + 1) := by
  simp only [stepWith] at h
  cases hp : pushGapX c with
  | some c0 =>
    rw [hp] at h; simp at h; subst h
    obtain ⟨hc0, _, _⟩ := pushGapX_core sc xs ys c c0 p hok hp
    subst hc0
    exact ⟨⟨hok.hxs, rfl⟩, by simp; omega⟩
  | none =>
    rw [hp] at h
    cases hdm : demoteCell xs ys c with
    | none => rw [hdm] at h; simp at h
    | some d =>
      rw [hdm] at h; simp at h
      obtain ⟨hokd, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c d p hok hdm
      obtain ⟨hc', _, _⟩ := pushGapX_core sc xs ys d c' p hokd h
      subst hc'
      exact ⟨⟨hokd.hxs, rfl⟩, by simp; omega⟩

theorem stepY_pos (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c c' : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t)
    (h : stepWith pushGapY xs ys (some c) = some c') :
    CellPos xs ys c' ∧ c'.joff + xs.length + 1 = c'.off + t := by
  simp only [stepWith] at h
  cases hp : pushGapY c with
  | some c0 =>
    rw [hp] at h; simp at h; subst h
    obtain ⟨hc0, _, _⟩ := pushGapY_core sc xs ys c c0 p hok hp
    subst hc0
    exact ⟨⟨rfl, hok.hys⟩, by simp; omega⟩
  | none =>
    rw [hp] at h
    cases hdm : demoteCell xs ys c with
    | none => rw [hdm] at h; simp at h
    | some d =>
      rw [hdm] at h; simp at h
      obtain ⟨hokd, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c d p hok hdm
      obtain ⟨hc', _, _⟩ := pushGapY_core sc xs ys d c' p hokd h
      subst hc'
      exact ⟨⟨rfl, hokd.hys⟩, by simp; omega⟩

theorem stepD_pos (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Int) (c c' : WCell) (t : Nat)
    (hok : CellOK sc xs ys p c) (hd : c.joff + xs.length = c.off + t)
    (h : stepWith pushDiag xs ys (some c) = some c') :
    CellPos xs ys c' ∧ c'.joff + xs.length = c'.off + t := by
  simp only [stepWith] at h
  cases hp : pushDiag c with
  | some c0 =>
    rw [hp] at h; simp at h; subst h
    obtain ⟨hc0, _, _, _⟩ := pushDiag_core sc xs ys c c0 p hok hp
    subst hc0
    exact ⟨⟨rfl, rfl⟩, by simp; omega⟩
  | none =>
    rw [hp] at h
    cases hdm : demoteCell xs ys c with
    | none => rw [hdm] at h; simp at h
    | some d =>
      rw [hdm] at h; simp at h
      obtain ⟨hokd, hdo, hdj⟩ := demoteCell_sound sc hr xs ys c d p hok hdm
      obtain ⟨hc', _, _, _⟩ := pushDiag_core sc xs ys d c' p hokd h
      subst hc'
      exact ⟨⟨rfl, rfl⟩, by simp; omega⟩

theorem offOf_extend (xs ys : List Char) (c : WCell) (t : Nat)
    (hpos : CellPos xs ys c) (hd : c.joff + xs.length = c.off + t) :
    offOf (some (extendCell c)) = some (extO xs.length xs ys t c.off) := by
  have hj : joffOf xs.length t c.off = c.joff := by unfold joffOf; omega
  simp only [offOf, Option.map, extendCell, extO, hj]
  rw [extendGo_off_eq, hpos.hxs, hpos.hys]

-- ══════════════════════════════════════════════════════════════════
-- Front-level lemmas
-- ══════════════════════════════════════════════════════════════════

/-- Facts about source cells (from the model's `FrontOK`), indices offset by `t0`. -/
def SrcFacts (sc : Scoring) (xs ys : List Char) (f : WFront) (t0 : Nat) : Prop :=
  ∀ i c, f[i]? = some (some c) →
    (∃ p, CellOK sc xs ys p c) ∧ c.joff + xs.length = c.off + (t0 + i)

/-- Facts about freshly pushed cells; `d` is the pending index shift. -/
def DstFacts (xs ys : List Char) (f : WFront) (t0 : Nat) (d : Int) : Prop :=
  ∀ i c, f[i]? = some (some c) →
    CellPos xs ys c ∧ ((c.joff : Int) + xs.length = c.off + (t0 + i : Nat) + d)

theorem srcFacts_tail (sc : Scoring) (xs ys : List Char) (o : Option WCell)
    (f : WFront) (t0 : Nat) (h : SrcFacts sc xs ys (o :: f) t0) :
    SrcFacts sc xs ys f (t0 + 1) := by
  intro i c hi
  have := h (i + 1) c (by simpa using hi)
  refine ⟨this.1, ?_⟩
  have := this.2; omega

theorem dstFacts_cons (xs ys : List Char) (o : Option WCell) (f : WFront)
    (t0 : Nat) (d : Int)
    (h0 : ∀ c, o = some c → CellPos xs ys c ∧ ((c.joff : Int) + xs.length = c.off + t0 + d))
    (h : DstFacts xs ys f (t0 + 1) d) : DstFacts xs ys (o :: f) t0 d := by
  intro i c hi
  cases i with
  | zero => simp at hi; have := h0 c hi; exact ⟨this.1, by simp; omega⟩
  | succ i => have := h i c (by simpa using hi); exact ⟨this.1, by have := this.2; push_cast at *; omega⟩

theorem map_stepX (sc : Scoring) (hr : ReasonableScoring sc) (xs ys : List Char) :
    ∀ (f : WFront) (t0 : Nat), SrcFacts sc xs ys f t0 →
      projF (f.map (stepWith pushGapX xs ys)) =
        mapFrom (pushXO xs.length ys.length) t0 (projF f) ∧
      DstFacts xs ys (f.map (stepWith pushGapX xs ys)) t0 1 := by
  intro f
  induction f with
  | nil => intro t0 _; exact ⟨rfl, fun i c h => by simp at h⟩
  | cons o f ih =>
    intro t0 hf
    obtain ⟨ihe, ihd⟩ := ih (t0 + 1) (srcFacts_tail sc xs ys o f t0 hf)
    refine ⟨?_, ?_⟩
    · simp only [projF, List.map_cons, mapFrom] at ihe ⊢
      rw [ihe]
      congr 1
      cases o with
      | none => rfl
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        rw [show (offOf (some c)).bind (pushXO xs.length ys.length t0) =
            pushXO xs.length ys.length t0 c.off from rfl]
        exact offOf_stepX sc hr xs ys p c t0 hok (by simpa using hd)
    · simp only [List.map_cons]
      refine dstFacts_cons xs ys _ _ t0 1 ?_ ihd
      intro c' hc'
      cases o with
      | none => simp [stepWith] at hc'
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        have := stepX_pos sc hr xs ys p c c' t0 hok (by simpa using hd) hc'
        exact ⟨this.1, by have := this.2; omega⟩

theorem map_stepY (sc : Scoring) (hr : ReasonableScoring sc) (xs ys : List Char) :
    ∀ (f : WFront) (t0 : Nat), SrcFacts sc xs ys f t0 →
      projF (f.map (stepWith pushGapY xs ys)) =
        mapFrom (pushYO xs.length ys.length) t0 (projF f) ∧
      DstFacts xs ys (f.map (stepWith pushGapY xs ys)) t0 (-1) := by
  intro f
  induction f with
  | nil => intro t0 _; exact ⟨rfl, fun i c h => by simp at h⟩
  | cons o f ih =>
    intro t0 hf
    obtain ⟨ihe, ihd⟩ := ih (t0 + 1) (srcFacts_tail sc xs ys o f t0 hf)
    refine ⟨?_, ?_⟩
    · simp only [projF, List.map_cons, mapFrom] at ihe ⊢
      rw [ihe]
      congr 1
      cases o with
      | none => rfl
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        rw [show (offOf (some c)).bind (pushYO xs.length ys.length t0) =
            pushYO xs.length ys.length t0 c.off from rfl]
        exact offOf_stepY sc hr xs ys p c t0 hok (by simpa using hd)
    · simp only [List.map_cons]
      refine dstFacts_cons xs ys _ _ t0 (-1) ?_ ihd
      intro c' hc'
      cases o with
      | none => simp [stepWith] at hc'
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        have := stepY_pos sc hr xs ys p c c' t0 hok (by simpa using hd) hc'
        exact ⟨this.1, by have := this.2; omega⟩

theorem map_stepD (sc : Scoring) (hr : ReasonableScoring sc) (xs ys : List Char) :
    ∀ (f : WFront) (t0 : Nat), SrcFacts sc xs ys f t0 →
      projF (f.map (stepWith pushDiag xs ys)) =
        mapFrom (pushDO xs.length ys.length) t0 (projF f) ∧
      DstFacts xs ys (f.map (stepWith pushDiag xs ys)) t0 0 := by
  intro f
  induction f with
  | nil => intro t0 _; exact ⟨rfl, fun i c h => by simp at h⟩
  | cons o f ih =>
    intro t0 hf
    obtain ⟨ihe, ihd⟩ := ih (t0 + 1) (srcFacts_tail sc xs ys o f t0 hf)
    refine ⟨?_, ?_⟩
    · simp only [projF, List.map_cons, mapFrom] at ihe ⊢
      rw [ihe]
      congr 1
      cases o with
      | none => rfl
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        rw [show (offOf (some c)).bind (pushDO xs.length ys.length t0) =
            pushDO xs.length ys.length t0 c.off from rfl]
        exact offOf_stepD sc hr xs ys p c t0 hok (by simpa using hd)
    · simp only [List.map_cons]
      refine dstFacts_cons xs ys _ _ t0 0 ?_ ihd
      intro c' hc'
      cases o with
      | none => simp [stepWith] at hc'
      | some c =>
        obtain ⟨⟨p, hok⟩, hd⟩ := hf 0 c (by simp)
        have := stepD_pos sc hr xs ys p c c' t0 hok (by simpa using hd) hc'
        exact ⟨this.1, by have := this.2; omega⟩

theorem map_extend (xs ys : List Char) :
    ∀ (f : WFront) (t0 : Nat), DstFacts xs ys f t0 0 →
      projF (f.map (Option.map extendCell)) =
        mapFrom (fun t off => some (extO xs.length xs ys t off)) t0 (projF f) := by
  intro f
  induction f with
  | nil => intro t0 _; rfl
  | cons o f ih =>
    intro t0 hf
    have hf' : DstFacts xs ys f (t0 + 1) 0 := by
      intro i c hi
      have := hf (i + 1) c (by simpa using hi)
      exact ⟨this.1, by have := this.2; push_cast at *; omega⟩
    simp only [projF, List.map_cons, mapFrom] at ih ⊢
    rw [ih (t0 + 1) hf']
    congr 1
    cases o with
    | none => rfl
    | some c =>
      obtain ⟨hpos, hd⟩ := hf 0 c (by simp)
      have hd' : c.joff + xs.length = c.off + t0 := by simp at hd; omega
      have := offOf_extend xs ys c t0 hpos hd'
      simpa [offOf] using this


theorem projF_shiftUp (f : WFront) : projF (shiftUp f) = shiftUpO (projF f) := by
  simp [projF, shiftUp, shiftUpO, List.map_dropLast, offOf]

theorem projF_shiftDown (f : WFront) : projF (shiftDown f) = shiftDownO (projF f) := by
  simp only [projF, shiftDown, shiftDownO, List.map_append, List.map_drop, List.map_cons,
    List.map_nil]
  rfl

theorem projF_zipWith (a b : WFront) :
    projF (List.zipWith betterCell a b) = List.zipWith betterO (projF a) (projF b) := by
  simp only [projF, List.map_zipWith, List.zipWith_map, offOf_betterCell]

theorem dst_shiftUp (xs ys : List Char) (f : WFront) (h : DstFacts xs ys f 0 1) :
    DstFacts xs ys (shiftUp f) 0 0 := by
  intro i c hi
  cases i with
  | zero => simp [shiftUp] at hi
  | succ i =>
    simp only [shiftUp, List.getElem?_cons_succ, List.getElem?_dropLast] at hi
    split at hi
    · have := h i c hi
      exact ⟨this.1, by have := this.2; push_cast at *; omega⟩
    · simp at hi

theorem dst_shiftDown (xs ys : List Char) (f : WFront) (h : DstFacts xs ys f 0 (-1)) :
    DstFacts xs ys (shiftDown f) 0 0 := by
  intro i c hi
  simp only [shiftDown] at hi
  by_cases hlt : i < (List.drop 1 f).length
  · rw [List.getElem?_append_left hlt, List.getElem?_drop] at hi
    have := h (1 + i) c hi
    exact ⟨this.1, by have := this.2; push_cast at *; omega⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    have hno : ∀ k : Nat, ([none] : WFront)[k]? ≠ some (some c) := by
      intro k; cases k <;> simp
    exact absurd hi (hno _)

theorem dst_zip (xs ys : List Char) (a b : WFront)
    (ha : DstFacts xs ys a 0 0) (hb : DstFacts xs ys b 0 0) :
    DstFacts xs ys (List.zipWith betterCell a b) 0 0 := by
  intro i c hi
  rw [List.getElem?_zipWith] at hi
  cases hai : a[i]? with
  | none => rw [hai] at hi; simp at hi
  | some x =>
    cases hbi : b[i]? with
    | none => rw [hai, hbi] at hi; simp at hi
    | some y =>
      rw [hai, hbi] at hi; simp at hi
      rcases betterCell_cases x y c hi with h | h
      · subst h; exact ha i c hai
      · subst h; exact hb i c hbi

theorem projF_emptyFront (len : Nat) : projF (emptyFront len) = List.replicate len none := by
  simp [projF, emptyFront, List.map_replicate, offOf]

theorem projF_frontAt (len : Nat) (hist : List WLevel) (d : Nat)
    (sel : WLevel → WFront) (selO : OLevelW → OFrontW)
    (hsel : ∀ lv, projF (sel lv) = selO (projL lv)) :
    projF (frontAt len hist d sel) = frontAtO len (hist.map projL) d selO := by
  simp only [frontAt, frontAtO, List.getElem?_map]
  cases hist[d - 1]? with
  | none => exact projF_emptyFront len
  | some lv => exact hsel lv

theorem src_frontAt (sc : Scoring) (xs ys : List Char) (p : Nat) (hist : List WLevel)
    (hh : HistOK sc xs ys p hist) (len d : Nat) (sel : WLevel → WFront)
    (hsel : ∀ q lv, LevelOK sc xs ys q lv → ∃ e, FrontOK sc xs ys q e (sel lv)) :
    SrcFacts sc xs ys (frontAt len hist d sel) 0 := by
  intro i c hi
  simp only [frontAt] at hi
  cases hg : hist[d - 1]? with
  | none =>
    rw [hg] at hi
    simp only [emptyFront, List.getElem?_replicate] at hi
    split at hi <;> simp at hi
  | some lv =>
    rw [hg] at hi
    obtain ⟨e, hfo⟩ := hsel _ lv (hh (d - 1) lv hg)
    obtain ⟨hok, hdiag, _⟩ := hfo.2 i c hi
    exact ⟨⟨_, hok⟩, by simpa using hdiag⟩

theorem levelOK_mf (sc : Scoring) (xs ys : List Char) (q : Int) (lv : WLevel)
    (h : LevelOK sc xs ys q lv) : ∃ e, FrontOK sc xs ys q e lv.mf := ⟨_, h.hmf⟩
theorem levelOK_xf (sc : Scoring) (xs ys : List Char) (q : Int) (lv : WLevel)
    (h : LevelOK sc xs ys q lv) : ∃ e, FrontOK sc xs ys q e lv.xf := ⟨_, h.hxf⟩
theorem levelOK_yf (sc : Scoring) (xs ys : List Char) (q : Int) (lv : WLevel)
    (h : LevelOK sc xs ys q lv) : ∃ e, FrontOK sc xs ys q e lv.yf := ⟨_, h.hyf⟩

/-- The projection commutes with one level step, given the model's
history invariant. -/
theorem projL_nextLevel (sc : Scoring) (hr : ReasonableScoring sc)
    (xs ys : List Char) (p : Nat) (len pe po px : Nat) (hist : List WLevel)
    (hh : HistOK sc xs ys p hist) :
    projL (nextLevel xs ys len pe po px hist) =
      nextLevelO xs.length ys.length xs ys len pe po px (hist.map projL) := by
  have hxe := map_stepX sc hr xs ys _ 0 (src_frontAt sc xs ys p hist hh len pe _ (levelOK_xf sc xs ys))
  have hxo := map_stepX sc hr xs ys _ 0 (src_frontAt sc xs ys p hist hh len po _ (levelOK_mf sc xs ys))
  have hye := map_stepY sc hr xs ys _ 0 (src_frontAt sc xs ys p hist hh len pe _ (levelOK_yf sc xs ys))
  have hyo := map_stepY sc hr xs ys _ 0 (src_frontAt sc xs ys p hist hh len po _ (levelOK_mf sc xs ys))
  have hdm := map_stepD sc hr xs ys _ 0 (src_frontAt sc xs ys p hist hh len px _ (levelOK_mf sc xs ys))
  have hxf := dst_zip xs ys _ _ (dst_shiftUp xs ys _ hxe.2) (dst_shiftUp xs ys _ hxo.2)
  have hyf := dst_zip xs ys _ _ (dst_shiftDown xs ys _ hye.2) (dst_shiftDown xs ys _ hyo.2)
  have hbase := dst_zip xs ys _ _ (dst_zip xs ys _ _ hdm.2 hxf) hyf
  have hext := map_extend xs ys _ 0 hbase
  simp only [nextLevel, nextLevelO, projL]
  rw [hext]
  simp only [projF_zipWith, projF_shiftUp, projF_shiftDown, hxe.1, hxo.1, hye.1, hyo.1, hdm.1]
  simp only [projF_frontAt len hist pe (·.xf) (·.xf) (fun _ => rfl),
    projF_frontAt len hist po (·.mf) (·.mf) (fun _ => rfl),
    projF_frontAt len hist pe (·.yf) (·.yf) (fun _ => rfl),
    projF_frontAt len hist px (·.mf) (·.mf) (fun _ => rfl)]

theorem projL_seedLevel (m len : Nat) (xs ys : List Char) :
    projL (seedLevel m len xs ys) = seedO m len xs ys := by
  simp only [projL, seedLevel, seedO, projF, emptyFront, List.map_set, List.map_replicate, offOf]
  simp [extendCell, extendGo_off_eq]

/-- Under `LevelOK`, the model's corner test is the offset test. -/
theorem cornerOf_iff_cornerO (sc : Scoring) (xs ys : List Char) (q : Int) (lv : WLevel)
    (h : LevelOK sc xs ys q lv) :
    (cornerOf ys.length lv).isSome = cornerO xs.length ys.length (projL lv) := by
  simp only [cornerOf, cornerO, projL, projF, List.getElem?_map]
  cases hg : lv.mf[ys.length]? with
  | none => simp
  | some o =>
    cases o with
    | none => simp [offOf]
    | some c =>
      obtain ⟨hok, hdiag, _⟩ := h.hmf.2 _ c hg
      simp only [offOf, Option.map, Option.some.injEq, beq_iff_eq]
      cases hx : c.xsRem with
      | cons x xr =>
        have hlt : c.off < xs.length := by
          rcases Nat.lt_or_ge c.off xs.length with hlt | hge
          · exact hlt
          · have h1 := hok.hxs
            rw [hx, List.drop_eq_nil_iff.2 hge] at h1
            simp at h1
        simp [hx]; omega
      | nil =>
        have hom : xs.length ≤ c.off := by
          have h1 := hok.hxs; rw [hx] at h1; exact List.drop_eq_nil_iff.1 h1.symm
        have hoff : c.off = xs.length := by have := hok.hoff; omega
        have hjn : c.joff = ys.length := by omega
        cases hy : c.ysRem with
        | nil => simp [hx, hy, hoff]
        | cons y yr =>
          exfalso
          have h1 := hok.hys; rw [hy, hjn] at h1
          simp at h1


end AlignmentSpec
