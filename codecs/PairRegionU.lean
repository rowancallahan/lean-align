import PairBox
import PairRegion

/-!
# Region search results as `RROk` facts (for the box certificates)

* the search's end state (`InvP` over a genome) gives the best hit, its placement and
  the tie flag over all hits (`rrOk_of_inv`);
* a search over the one-chromosome genome holding letters `[x0, x1)` of chromosome
  `c` gives them over the hits inside that view (`rrOk_view`);
* results of two regions combine into the result of their union (`rrOk_join`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Search end state → region result (virtual windows decoded to placements). -/
def toRRes (n P : Nat) (b : Best) : RRes :=
  if b.pen ≤ P then ⟨some (decB n b.win, -(b.pen : Int)), b.amb⟩ else ⟨none, false⟩

theorem hit_key (P : Nat) (read : List Char) (g : Genome) (st : Strand) (w : Window) (s : Int) :
    (strandScore g read st w = some s ∧ -(P : Int) ≤ s) ↔
      (cwS P read g st w ≤ P ∧ s = -(cwS P read g st w : Int)) := by
  cases st with
  | fwd => exact cwT_iff P read g w s
  | rev => exact cwT_iff P (revComp read) g w s

/-- **The search's end state is a region result over all hits.** -/
theorem rrOk_of_inv (P : Nat) (read : List Char) (g : Genome) (S : Window → Prop) (b : Best)
    (hi : InvP P (cwB P read g) S b) (hall : ∀ w, cwB P read g w ≤ P → S w) :
    RROk (hitsBoth sc0 (-(P : Int)) g read) (fun _ => true) (toRRes g.length P b) := by
  -- a hit is a window of `S` at its penalty
  have hhit : ∀ p s, (p, s) ∈ hitsBoth sc0 (-(P : Int)) g read →
      S (encB g.length p) ∧ cwB P read g (encB g.length p) = cwS P read g p.2 p.1 ∧
        cwS P read g p.2 p.1 ≤ P ∧ s = -(cwS P read g p.2 p.1 : Int) := by
    intro p s hm
    rw [mem_hitsBoth_T] at hm
    obtain ⟨h1, h2⟩ := (hit_key P read g p.2 p.1 s).mp ⟨hm.2.1, hm.2.2⟩
    have he := cwB_encB P read g p h1
    exact ⟨hall _ (by rw [he]; exact h1), he, h1, h2⟩
  unfold toRRes
  split
  · next hp =>
    unfold RROk
    simp only
    have hw := hi.hit hp
    have hd := cwS_decB P read g b.win
    refine ⟨?_, trivial, ?_, ?_⟩
    · rw [mem_hitsBoth_T]
      have h2 := (hit_key P read g (decB g.length b.win).2 (decB g.length b.win).1
        (-(cwS P read g (decB g.length b.win).2 (decB g.length b.win).1 : Int))).mpr ⟨by omega, rfl⟩
      rw [hd, hw] at h2
      exact ⟨strandScore_allWindows g read _ _ _ h2.1, h2.1, h2.2⟩
    · rintro ⟨p, s⟩ hm -
      obtain ⟨hS, he, -, hs⟩ := hhit p s hm
      have := hi.min _ hS
      simp only
      omega
    · rintro ha ⟨p, s⟩ hm - hs
      obtain ⟨hS, he, hle, hs'⟩ := hhit p s hm
      simp only at hs hs' ⊢
      have heq : encB g.length p = b.win := by
        apply Classical.byContradiction
        intro hne
        have := (hi.amb hp).mpr ⟨_, hS, hne, by omega⟩
        rw [ha] at this
        cases this
      rw [← heq, decB_encB _ _ (cwS_chr_lt P read g p hle)]
  · next hp =>
    unfold RROk
    simp only
    rintro ⟨p, s⟩ hm
    obtain ⟨hS, he, hle, -⟩ := hhit p s hm
    have := hi.min _ hS
    omega

/-! ## One view -/

/-- Placement inside letters `[x0, x1)` of chromosome `c`. -/
def inView (c x0 x1 : Nat) (p : Placement) : Bool :=
  decide (p.1.chr = c) && decide (x0 ≤ p.1.start) && decide (p.1.start + p.1.len ≤ x1)

/-- A placement of the one-view genome → the genome. -/
def shiftP (c x0 : Nat) (p : Placement) : Placement := (⟨c, x0 + p.1.start, p.1.len⟩, p.2)

def shiftR (c x0 : Nat) (r : RRes) : RRes := ⟨r.best.map (fun x => (shiftP c x0 x.1, x.2)), r.amb⟩

/-- The one-chromosome genome of letters `[x0, x1)` of chromosome `c`. -/
def viewG (g : Genome) (c x0 x1 : Nat) : Genome :=
  [⟨"", (((g[c]?).map (·.seq)).getD [] |>.drop x0).take (x1 - x0)⟩]

theorem strandScore_congr (g g' : Genome) (read : List Char) (st : Strand) (w w' : Window)
    (h : windowSeq g w = windowSeq g' w') : strandScore g read st w = strandScore g' read st w' := by
  cases st <;> simp only [strandScore, windowScore, h]

section view
variable (g : Genome) (c x0 x1 : Nat) (hc : c < g.length) (hx : x0 ≤ x1) (hx1 : x1 ≤ (g[c]).seq.length)
include hc hx hx1

omit hx hx1 in
theorem viewG_eq : viewG g c x0 x1 = [⟨"", ((g[c]).seq.drop x0).take (x1 - x0)⟩] := by
  simp [viewG, List.getElem?_eq_getElem hc]

theorem windowSeq_viewG (w : Window) (hw : windowSeq (viewG g c x0 x1) w ≠ none) :
    w.chr = 0 ∧ w.start + w.len ≤ x1 - x0 ∧
      windowSeq (viewG g c x0 x1) w = windowSeq g ⟨c, x0 + w.start, w.len⟩ := by
  rw [viewG_eq g c x0 x1 hc] at hw ⊢
  rcases w with ⟨wc, st, len⟩
  have hfit : wc = 0 ∧ st + len ≤ x1 - x0 := by
    unfold windowSeq at hw
    cases wc with
    | zero =>
      simp only [List.getElem?_cons_zero, List.length_take, List.length_drop] at hw
      split at hw
      · exact ⟨rfl, by omega⟩
      · exact absurd rfl hw
    | succ k => simp at hw
  obtain ⟨rfl, hle⟩ := hfit
  refine ⟨rfl, hle, ?_⟩
  have := windowSeq_region g c hc x0 x1 hx1 ⟨c, x0 + st, len⟩ rfl (by simp) (by simp; omega)
  simp only [Nat.add_sub_cancel_left] at this
  exact this

/-- **One view.**  A region result over the one-view genome is one over the hits
inside the view. -/
theorem rrOk_view (T : Int) (read : List Char) (r : RRes)
    (h : RROk (hitsBoth sc0 T (viewG g c x0 x1) read) (fun _ => true) r) :
    RROk (hitsBoth sc0 T g read) (inView c x0 x1) (shiftR c x0 r) := by
  -- hits of the view genome ↔ hits of the genome inside the view
  have fwdH : ∀ p s, (p, s) ∈ hitsBoth sc0 T (viewG g c x0 x1) read →
      (shiftP c x0 p, s) ∈ hitsBoth sc0 T g read ∧ inView c x0 x1 (shiftP c x0 p) = true := by
    intro p s hm
    rw [mem_hitsBoth_T] at hm
    obtain ⟨-, hs, hT⟩ := hm
    have hne : windowSeq (viewG g c x0 x1) p.1 ≠ none := by
      intro hn
      cases hst : p.2 <;> (rw [hst] at hs; simp [strandScore, windowScore, hn] at hs)
    obtain ⟨-, hle, hseq⟩ := windowSeq_viewG g c x0 x1 hc hx hx1 p.1 hne
    have hs' := (strandScore_congr _ _ read p.2 _ _ hseq).symm.trans hs
    refine ⟨?_, ?_⟩
    · rw [mem_hitsBoth_T]
      exact ⟨strandScore_allWindows g read _ _ _ hs', hs', hT⟩
    · simp only [inView, shiftP, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨trivial, decide_eq_true (Nat.le_add_right _ _)⟩, decide_eq_true ?_⟩
      omega
  have backH : ∀ q s, (q, s) ∈ hitsBoth sc0 T g read → inView c x0 x1 q = true →
      ((⟨0, q.1.start - x0, q.1.len⟩, q.2), s) ∈ hitsBoth sc0 T (viewG g c x0 x1) read ∧
        shiftP c x0 (⟨0, q.1.start - x0, q.1.len⟩, q.2) = q := by
    intro q s hm hv
    simp only [inView, decide_eq_true_eq, Bool.and_eq_true] at hv
    obtain ⟨⟨hqc, h0⟩, h1⟩ := hv
    rw [mem_hitsBoth_T] at hm
    obtain ⟨-, hs, hT⟩ := hm
    have hseq : windowSeq (viewG g c x0 x1) ⟨0, q.1.start - x0, q.1.len⟩ = windowSeq g q.1 := by
      rw [viewG_eq g c x0 x1 hc]
      exact windowSeq_region g c hc x0 x1 hx1 q.1 hqc h0 h1
    have hs' := (strandScore_congr _ _ read q.2 _ _ hseq).trans hs
    refine ⟨?_, ?_⟩
    · rw [mem_hitsBoth_T]
      exact ⟨strandScore_allWindows _ read _ _ _ hs', hs', hT⟩
    · obtain ⟨⟨qc, qs, ql⟩, qt⟩ := q
      simp only at hqc h0 ⊢
      simp only [shiftP, Prod.mk.injEq, Window.mk.injEq, and_true]
      omega
  unfold RROk at h ⊢
  unfold shiftR
  cases hb : r.best with
  | none =>
    rw [hb] at h
    simp only [Option.map_none]
    intro x hx
    cases hv : inView c x0 x1 x.1 with
    | false => rfl
    | true =>
      have := (backH x.1 x.2 hx hv).1
      exact absurd (h _ this) (by simp)
  | some ps =>
    rw [hb] at h
    obtain ⟨p, s⟩ := ps
    obtain ⟨hm, -, hle, hu⟩ := h
    simp only [Option.map_some]
    obtain ⟨hm', hv'⟩ := fwdH p s hm
    refine ⟨hm', hv', ?_, ?_⟩
    · intro x hx hv
      exact hle ((⟨0, x.1.1.start - x0, x.1.1.len⟩, x.1.2), x.2) (backH x.1 x.2 hx hv).1 rfl
    · intro ha x hx hv hs
      obtain ⟨hb1, hb2⟩ := backH x.1 x.2 hx hv
      have := hu ha _ hb1 rfl hs
      simp only at this
      rw [← hb2, this]

end view

/-! ## Unions -/

/-- Result over the union of two regions. -/
def rrJoin (r1 r2 : RRes) : RRes :=
  match r1.best, r2.best with
  | none, _ => r2
  | _, none => r1
  | some (p1, s1), some (p2, s2) =>
    if s2 < s1 then r1 else if s1 < s2 then r2
    else ⟨some (p1, s1), r1.amb || r2.amb || !decide (p1 = p2)⟩

theorem rrOk_join (h : List (Placement × Int)) (hf : ScoreFun h) (R1 R2 : Placement → Bool) (r1 r2 : RRes)
    (h1 : RROk h R1 r1) (h2 : RROk h R2 r2) : RROk h (fun p => R1 p || R2 p) (rrJoin r1 r2) := by
  unfold RROk at h1 h2
  unfold rrJoin
  cases e1 : r1.best with
  | none =>
    rw [e1] at h1
    simp only
    unfold RROk
    cases e2 : r2.best with
    | none =>
      rw [e2] at h2
      intro x hx
      simp [h1 x hx, h2 x hx]
    | some q =>
      rw [e2] at h2
      obtain ⟨q1, q2⟩ := q
      obtain ⟨hm, hR, hle, hu⟩ := h2
      refine ⟨hm, by simp [hR], ?_, ?_⟩
      · intro x hx hR'
        have := h1 x hx
        simp only [this, Bool.false_or] at hR'
        exact hle x hx hR'
      · intro ha x hx hR' hs
        have := h1 x hx
        simp only [this, Bool.false_or] at hR'
        exact hu ha x hx hR' hs
  | some p =>
    rw [e1] at h1
    obtain ⟨p1, s1⟩ := p
    obtain ⟨hm1, hR1, hle1, hu1⟩ := h1
    cases e2 : r2.best with
    | none =>
      rw [e2] at h2
      simp only
      unfold RROk
      rw [e1]
      refine ⟨hm1, by simp [hR1], ?_, ?_⟩
      · intro x hx hR'
        have := h2 x hx
        simp only [this, Bool.or_false] at hR'
        exact hle1 x hx hR'
      · intro ha x hx hR' hs
        have := h2 x hx
        simp only [this, Bool.or_false] at hR'
        exact hu1 ha x hx hR' hs
    | some q =>
      rw [e2] at h2
      obtain ⟨q1, q2⟩ := q
      obtain ⟨hm2, hR2, hle2, hu2⟩ := h2
      simp only
      have hx1 : ∀ x ∈ h, (R1 x.1 || R2 x.1) = true → R1 x.1 = true ∨ R2 x.1 = true := by
        intro x _ hx; simpa using hx
      split
      · next hlt =>
        unfold RROk
        rw [e1]
        refine ⟨hm1, by simp [hR1], ?_, ?_⟩
        · intro x hx hR'
          rcases hx1 x hx hR' with h' | h'
          · exact hle1 x hx h'
          · have := hle2 x hx h'; omega
        · intro ha x hx hR' hs
          rcases hx1 x hx hR' with h' | h'
          · exact hu1 ha x hx h' hs
          · have := hle2 x hx h'; omega
      · split
        · next hlt' hlt =>
          unfold RROk
          rw [e2]
          refine ⟨hm2, by simp [hR2], ?_, ?_⟩
          · intro x hx hR'
            rcases hx1 x hx hR' with h' | h'
            · have := hle1 x hx h'; omega
            · exact hle2 x hx h'
          · intro ha x hx hR' hs
            rcases hx1 x hx hR' with h' | h'
            · have := hle1 x hx h'; omega
            · exact hu2 ha x hx h' hs
        · next hlt' hlt =>
          have hs12 : s1 = q2 := by omega
          unfold RROk
          simp only
          refine ⟨hm1, by simp [hR1], ?_, ?_⟩
          · intro x hx hR'
            rcases hx1 x hx hR' with h' | h'
            · exact hle1 x hx h'
            · have := hle2 x hx h'; omega
          · intro ha x hx hR' hs
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at ha
            obtain ⟨⟨ha1, ha2⟩, hpq⟩ := ha
            rcases hx1 x hx hR' with h' | h'
            · exact hu1 ha1 x hx h' hs
            · rw [hu2 ha2 x hx h' (by omega), hpq]

end MapSpec.Fast

#print axioms MapSpec.Fast.rrOk_of_inv
#print axioms MapSpec.Fast.rrOk_view
#print axioms MapSpec.Fast.rrOk_join
