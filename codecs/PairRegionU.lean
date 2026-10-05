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


theorem rrOk_congrR (h : List (Placement × Int)) (R R' : Placement → Bool) (r : RRes)
    (hRR : ∀ x ∈ h, R x.1 = R' x.1) (H : RROk h R' r) : RROk h R r := by
  unfold RROk at H ⊢
  cases hb : r.best with
  | none =>
    rw [hb] at H
    intro x hx; rw [hRR x hx]; exact H x hx
  | some ps =>
    rw [hb] at H
    obtain ⟨p, s⟩ := ps
    obtain ⟨hm, hR, hle, hu⟩ := H
    refine ⟨hm, by rw [hRR _ hm]; exact hR, fun x hx hR' => hle x hx (by rw [← hRR x hx]; exact hR'),
      fun ha x hx hR' hs => hu ha x hx (by rw [← hRR x hx]; exact hR') hs⟩

/-! ## The region search, bytes and packed -/

section regionrr
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)

include hg hr

/-- **Region result.**  The search over bytes `B` = letters `[x0, x1)` of chromosome
`c` alone (lookups exact on `B`) is the region result over the hits inside the view. -/
theorem region_rr (c x0 x1 : Nat) (B : ByteArray) (hc : c < gbs.size) (hx : x0 ≤ x1)
    (hx1 : x1 ≤ gbs[c]!.size) (hB : B.size = x1 - x0)
    (hBi : ∀ i, i < x1 - x0 → B.get! i = gbs[c]!.get! (x0 + i))
    {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS B R' s base 0 (LookG.look ix B R' s base (LookG.prep ix (seedHashAt R' s))))
    (hf : fastT P R = true) (b : Best) (hb : mapChromsGB P ix B #[0] #[B] R = b) :
    RROk (hitsBoth sc0 (-(P : Int)) g read) (inView c x0 x1) (shiftR c x0 (toRRes 1 P b)) := by
  have hgl : gbs.size = g.length := hg.1
  have hc' : c < g.length := by omega
  have hgc : gbs[c]! = gbs[c] := getElem!_pos gbs c hc
  have henc := hg.2 c hc hc'
  have hL : gbs[c]!.size = (g[c]).seq.length := by rw [hgc]; exact henc.1
  have hx1' : x1 ≤ (g[c]).seq.length := by omega
  have hgR : GenomeBytes #[B] (viewG g c x0 x1) := by
    rw [viewG_eq g c x0 x1 hc']
    refine ⟨rfl, fun c' h1 h2 => ?_⟩
    have hc0 : c' = 0 := by simp at h1; omega
    subst hc0
    refine ⟨by simp [hB]; omega, fun i hi => ?_⟩
    simp only [List.getElem_cons_zero, List.length_take, List.length_drop] at hi ⊢
    show (B.get! i).toNat = _
    rw [hBi i (by omega), hgc, henc.2 (x0 + i) (by omega)]
    simp [List.getElem_take, List.getElem_drop]
  have hcatR : catOk B #[0] #[B] = true := by
    unfold catOk
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    intro c' hc''
    have hc0 : c' = 0 := by simp at hc''; omega
    subst hc0
    simp only [List.getElem!_toArray, List.getElem!_cons_zero]
    refine ⟨by omega, ?_⟩
    rw [eqRun_spec]
    intro t _
    rfl
  unfold fastT at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  have H := mapChromsGB_inv P read (viewG g c x0 x1) #[B] R hgR hr ix B #[0] hcatR hlk hf.1 hf.2
  rw [hb] at H
  obtain ⟨S, hi, hall⟩ := H
  have h1 := rrOk_of_inv P read (viewG g c x0 x1) S _ hi hall
  have hlen : (viewG g c x0 x1).length = 1 := rfl
  rw [hlen] at h1
  exact rrOk_view g c x0 x1 hc' hx hx1' _ read _ h1

end regionrr

/-- Region result of read `R` (cap `P`) over letters `[x0, x1)` of chromosome `c`
(clipped to the chromosome): the proved search on a packed view, lookups cut to it.
`none`: not on the fast path, or an empty view. -/
def regionRRKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (rl : Nat → Nat → L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (c x0 x1 : Nat) : Option RRes :=
  if c < pgs.size && fastT P R then
    let x1' := min x1 pgs[c]!.n
    if x0 < x1' then
      let v := view pgs[c]! x0 (x1' - x0)
      some (shiftR c x0 (toRRes 1 P (mapChromsGBKG P (rl (offs[c]! + x0) (offs[c]! + x1')) G #[0] #[v] #[v] R)))
    else none
  else none

/-- A hit inside `[x0, x1)` is inside `[x0, min x1 n)` (it fits its chromosome). -/
theorem inView_clip (P : Nat) (g : Genome) (read : List Char) (c x0 x1 n : Nat) (hn : ∀ ch, g[c]? = some ch → ch.seq.length = n)
    (p : Placement) (s : Int) (hm : (p, s) ∈ hitsBoth sc0 (-(P : Int)) g read) :
    inView c x0 x1 p = inView c x0 (min x1 n) p := by
  rw [mem_hitsBoth_T] at hm
  obtain ⟨ch, hch, hfit, -⟩ := len_le_of_score P g read p.2 p.1 s hm.2.1 hm.2.2
  unfold inView
  by_cases hpc : p.1.chr = c
  · rw [hpc] at hch
    have := hn ch hch
    simp only [hpc, decide_true, Bool.true_and]
    by_cases h0 : x0 ≤ p.1.start <;> by_cases h1 : p.1.start + p.1.len ≤ x1 <;>
      simp [h0, h1] <;> omega
  · simp [hpc]

section packedrr
variable (P : Nat) (read : List Char) (g : Genome) (pgs : Array PGen) (R : ByteArray)
  (hg : GenomeBytes (pgs.map Mz.unpack) g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (rl : Nat → Nat → L) (G G' : ByteArray) (offs : Array Nat)
  (hG : ∀ a b (G1 : ByteArray) R s base p, LookG.look (rl a b) G R s base p = LookG.look (rl a b) G1 R s base p)
  (hcat : catOk G' offs (pgs.map Mz.unpack) = true)
  (hlk : ∀ a b (B : ByteArray), b ≤ G'.size → B.size = b - a → (∀ i, i < b - a → B.get! i = G'.get! (a + i)) →
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS B R' s base 0 (LookG.look (rl a b) B R' s base (LookG.prep (rl a b) (seedHashAt R' s))))

include hg hr hG hcat hlk

/-- **Packed region result.** -/
theorem regionRRKP_ok (c x0 x1 : Nat) (r : RRes) (h : regionRRKP P rl G offs pgs R c x0 x1 = some r) :
    RROk (hitsBoth sc0 (-(P : Int)) g read) (inView c x0 x1) r := by
  unfold regionRRKP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · next hcf =>
    obtain ⟨hc, hf⟩ := hcf
    split at h
    · next hx =>
      simp only [Option.some.injEq] at h
      generalize hx1' : min x1 pgs[c]!.n = x1' at hx h
      generalize hv : view pgs[c]! x0 (x1' - x0) = v at h
      rw [mapChromsGBKG_one P _ G (Mz.unpack v) (hG _ _ (Mz.unpack v))] at h
      generalize hb : mapChromsGB P (rl (offs[c]! + x0) (offs[c]! + x1')) (Mz.unpack v) #[0]
        #[Mz.unpack v] R = b at h
      subst h
      have hsz : (pgs.map Mz.unpack).size = pgs.size := by simp
      have hgc : (pgs.map Mz.unpack)[c]! = Mz.unpack pgs[c]! := by
        rw [getElem!_pos (pgs.map Mz.unpack) c (by rw [hsz]; exact hc), getElem!_pos pgs c hc]
        simp
      have hn : (Mz.unpack pgs[c]!).size = pgs[c]!.n := (Mz.rep_unpack _).1.symm
      have hBs : (Mz.unpack v).size = x1' - x0 := by
        rw [← (Mz.rep_unpack _).1, ← hv]; rfl
      have hx1n : x1' ≤ pgs[c]!.n := by omega
      have hBi : ∀ i, i < x1' - x0 → (Mz.unpack v).get! i = (pgs.map Mz.unpack)[c]!.get! (x0 + i) := fun i hi => by
        rw [hgc, ← (Mz.rep_unpack _).2, ← (Mz.rep_unpack _).2, ← hv]
        have h2 : x0 + i < pgs[c]!.n := by omega
        simp only [PGen.get, view, hi, h2, if_true, Nat.add_assoc]
        rfl
      have hcat' := hcat
      unfold catOk at hcat'
      simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hcat'
      obtain ⟨hcs, hce⟩ := hcat' c (by rw [hsz]; exact hc)
      rw [eqRun_spec] at hce
      rw [hgc, hn] at hcs
      have hlk' := hlk (offs[c]! + x0) (offs[c]! + x1') (Mz.unpack v)
        (by omega) (by rw [hBs]; omega) (fun i hi => by
          rw [hBi i (by omega)]
          have := hce (x0 + i) (by rw [hgc, hn]; omega)
          rw [Nat.zero_add] at this
          rw [← this, Nat.add_assoc])
      have hc3 : c < (pgs.map Mz.unpack).size := by rw [hsz]; exact hc
      have hx3 : x0 ≤ x1' := by omega
      have hx4 : x1' ≤ (pgs.map Mz.unpack)[c]!.size := by rw [hgc, hn]; omega
      have hrr := region_rr P read g (pgs.map Mz.unpack) R hg hr c x0 x1' (Mz.unpack v)
        hc3 hx3 hx4 hBs hBi (rl (offs[c]! + x0) (offs[c]! + x1')) hlk' hf b hb
      -- the view is clipped to the chromosome: same hits inside
      have hcl : ∀ x ∈ hitsBoth sc0 (-(P : Int)) g read, inView c x0 x1 x.1 = inView c x0 x1' x.1 := by
        intro x hx
        rw [← hx1']
        apply inView_clip P g read c x0 x1 pgs[c]!.n _ x.1 x.2 hx
        intro ch hch
        have hc2 : c < g.length := by rw [← hg.1, hsz]; exact hc
        rw [List.getElem?_eq_getElem hc2] at hch
        simp only [Option.some.injEq] at hch
        subst hch
        have := (hg.2 c (by rw [hsz]; exact hc) hc2).1
        rw [← this, ← getElem!_pos (pgs.map Mz.unpack) c (by rw [hsz]; exact hc), hgc, hn]
      exact rrOk_congrR _ _ _ _ hcl hrr
    · simp at h
  · simp at h

end packedrr

end MapSpec.Fast

#print axioms MapSpec.Fast.rrOk_of_inv
#print axioms MapSpec.Fast.rrOk_view
#print axioms MapSpec.Fast.rrOk_join
#print axioms MapSpec.Fast.regionRRKP_ok
