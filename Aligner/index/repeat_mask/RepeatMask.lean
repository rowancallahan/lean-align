import MapSpec                    -- the mapping specification (spec/, draft)
import MapperGapless              -- selectUnique_eq_some_iff
import SeedMapper                 -- take_drop_window

/-!
# Exact duplicates and safe repeat masking

Two different windows with the same letters get the same score, so
`mapSpec` can never report either one alone; a read whose best window lies in
an exactly duplicated region is unmapped.

    windowSeq g w' = windowSeq g w → windowScore … w' = windowScore … w      (windowScore_eq_of_seq)
    w' ≠ w → windowSeq g w' = windowSeq g w → mapSpec … ≠ some (w, s)       (mapSpec_ne_of_duplicate)
    w best (score ≥ T, nothing scores higher), duplicated → mapSpec … = none (mapSpec_none_of_best_duplicated)
    a window inside one copy of a duplicated stretch has a different
      window with the same letters in the other copy                        (duplicate_in_region)
    best window inside a duplicated stretch → mapSpec … = none              (mapSpec_none_of_best_in_region)

## Masking

An index may drop places inside duplicated stretches, but the mapper must
still learn that the best window is tied.  What it must keep, stated on the
candidate windows `C` and a flag `dup : Window → Bool`:

* `DupSound`: `dup r = true` only if some other window has the same letters as `r`;
* `MaskCover`: every window scoring ≥ T is in `C`, or has a different window
  `r ∈ C` with the same letters and `dup r = true` (one representative per
  duplicated copy, flagged with multiplicity ≥ 2).

`mapMasked` scores `C`, and reports "tie" (`none`) when the unique best
candidate is flagged.  `mapMasked_eq_mapSpec`: under these two conditions it
returns `mapSpec`.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Best candidate, but a flagged (duplicated) best is a tie. -/
def mapMasked (score : Window → Option Int) (T : Int) (C : List Window) (dup : Window → Bool) :
    Option (Window × Int) :=
  match selectUnique (hitsOf score T C) with
  | some (w, s) => if dup w then none else some (w, s)
  | none => none

/-- `dup` flags only windows that have an exact copy elsewhere. -/
def DupSound (g : Genome) (dup : Window → Bool) : Prop :=
  ∀ r, dup r = true → ∃ r', r' ≠ r ∧ windowSeq g r' = windowSeq g r

/-- Every hit is a candidate or is represented by a flagged copy among the candidates. -/
def MaskCover (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (dup : Window → Bool) : Prop :=
  ∀ w s, windowScore sc read g w = some s → T ≤ s →
    w ∈ C ∨ ∃ r ∈ C, r ≠ w ∧ windowSeq g r = windowSeq g w ∧ dup r = true

/-! ## Proof -/

theorem windowScore_eq_of_seq (sc : Scoring) (read : List Char) (g : Genome) (w w' : Window)
    (h : windowSeq g w' = windowSeq g w) : windowScore sc read g w' = windowScore sc read g w := by
  unfold windowScore; rw [h]

theorem mem_allWindows_of_score' (sc : Scoring) (read : List Char) (g : Genome) (w : Window) (s : Int)
    (h : windowScore sc read g w = some s) : w ∈ allWindows g := by
  apply (mem_allWindows g w).mpr
  unfold windowScore at h
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some _ => rfl

theorem specHits_functional (sc : Scoring) (T : Int) (g : Genome) (read : List Char) :
    ∀ a ∈ hitsOf (windowScore sc read g) T (allWindows g),
    ∀ b ∈ hitsOf (windowScore sc read g) T (allWindows g), a.1 = b.1 → a.2 = b.2 := by
  rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
  rw [mem_hitsOf] at ha hb
  simp only at hww
  subst hww
  have := ha.2.1.symm.trans hb.2.1
  simpa using this

theorem mapSpec_some_iff (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (w : Window) (s : Int) :
    mapSpec sc T g read = some (w, s) ↔
      (windowScore sc read g w = some s ∧ T ≤ s) ∧
      ∀ w' s', windowScore sc read g w' = some s' → T ≤ s' → s' < s ∨ w' = w := by
  unfold mapSpec
  rw [selectUnique_eq_some_iff _ (specHits_functional sc T g read), mem_hitsOf]
  constructor
  · rintro ⟨⟨-, hs, hT⟩, hall⟩
    exact ⟨⟨hs, hT⟩, fun w' s' hs' hT' =>
      hall (w', s') ((mem_hitsOf _ _ _ _ _).mpr ⟨mem_allWindows_of_score' sc read g w' s' hs', hs', hT'⟩)⟩
  · rintro ⟨⟨hs, hT⟩, hall⟩
    refine ⟨⟨mem_allWindows_of_score' sc read g w s hs, hs, hT⟩, ?_⟩
    rintro ⟨w', s'⟩ hb
    rw [mem_hitsOf] at hb
    exact hall w' s' hb.2.1 hb.2.2

/-- **Exact duplicate.**  A window with an exact copy elsewhere is never reported. -/
theorem mapSpec_ne_of_duplicate (sc : Scoring) (T : Int) (g : Genome) (read : List Char)
    (w w' : Window) (hne : w' ≠ w) (hseq : windowSeq g w' = windowSeq g w) (s : Int) :
    mapSpec sc T g read ≠ some (w, s) := by
  intro h
  obtain ⟨⟨hs, hT⟩, hall⟩ := (mapSpec_some_iff sc T g read w s).mp h
  have hs' : windowScore sc read g w' = some s := by rw [windowScore_eq_of_seq sc read g w w' hseq, hs]
  rcases hall w' s hs' hT with h | h
  · omega
  · exact hne h

/-- **Best window duplicated → unmapped.** -/
theorem mapSpec_none_of_best_duplicated (sc : Scoring) (T : Int) (g : Genome) (read : List Char)
    (w : Window) (s : Int) (hs : windowScore sc read g w = some s) (hT : T ≤ s)
    (hbest : ∀ w'' s'', windowScore sc read g w'' = some s'' → s'' ≤ s)
    (w' : Window) (hne : w' ≠ w) (hseq : windowSeq g w' = windowSeq g w) :
    mapSpec sc T g read = none := by
  cases h : mapSpec sc T g read with
  | none => rfl
  | some a =>
    obtain ⟨a, sa⟩ := a
    obtain ⟨⟨hsa, hTa⟩, hall⟩ := (mapSpec_some_iff sc T g read a sa).mp h
    have hle := hbest a sa hsa
    have hs' : windowScore sc read g w' = some s := by rw [windowScore_eq_of_seq sc read g w w' hseq, hs]
    rcases hall w s hs hT with h1 | h1
    · omega
    · rcases hall w' s hs' hT with h2 | h2
      · omega
      · exact absurd (h2.trans h1.symm) hne

/-- A window inside one copy of an exactly duplicated stretch has the same
letters as the shifted window in the other copy. -/
theorem duplicate_in_region (g : Genome) (c c' p p' L : Nat) (ch ch' : Chromosome)
    (hc : g[c]? = some ch) (hc' : g[c']? = some ch')
    (hL : p + L ≤ ch.seq.length) (hL' : p' + L ≤ ch'.seq.length)
    (hdup : (ch.seq.drop p).take L = (ch'.seq.drop p').take L)
    (a len : Nat) (ha : a + len ≤ L) :
    windowSeq g ⟨c', p' + a, len⟩ = windowSeq g ⟨c, p + a, len⟩ := by
  unfold windowSeq
  simp only [hc, hc']
  rw [if_pos (by omega), if_pos (by omega)]
  congr 1
  rw [← take_drop_window ch.seq p L a len ha, ← take_drop_window ch'.seq p' L a len ha, hdup]

/-- **Best window in a duplicated stretch → unmapped.** -/
theorem mapSpec_none_of_best_in_region (sc : Scoring) (T : Int) (g : Genome) (read : List Char)
    (c c' p p' L : Nat) (ch ch' : Chromosome)
    (hc : g[c]? = some ch) (hc' : g[c']? = some ch')
    (hL : p + L ≤ ch.seq.length) (hL' : p' + L ≤ ch'.seq.length)
    (hdup : (ch.seq.drop p).take L = (ch'.seq.drop p').take L) (hdiff : (c, p) ≠ (c', p'))
    (a len : Nat) (ha : a + len ≤ L) (s : Int)
    (hs : windowScore sc read g ⟨c, p + a, len⟩ = some s) (hT : T ≤ s)
    (hbest : ∀ w'' s'', windowScore sc read g w'' = some s'' → s'' ≤ s) :
    mapSpec sc T g read = none := by
  apply mapSpec_none_of_best_duplicated sc T g read _ s hs hT hbest ⟨c', p' + a, len⟩
  · intro h
    simp only [Window.mk.injEq] at h
    apply hdiff
    simp only [Prod.mk.injEq]
    omega
  · exact duplicate_in_region g c c' p p' L ch ch' hc hc' hL hL' hdup a len ha

/-- A best hit is a candidate (a flagged representative would tie it). -/
theorem mem_C_of_best (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (dup : Window → Bool) (hcov : MaskCover sc T g read C dup) (a : Window) (sa : Int)
    (h : mapSpec sc T g read = some (a, sa)) : a ∈ C := by
  obtain ⟨⟨hsa, hTa⟩, hall⟩ := (mapSpec_some_iff sc T g read a sa).mp h
  rcases hcov a sa hsa hTa with h1 | ⟨r, -, hra, hseq, -⟩
  · exact h1
  · have hsr : windowScore sc read g r = some sa := by
      rw [windowScore_eq_of_seq sc read g a r hseq, hsa]
    rcases hall r sa hsr hTa with h2 | h2
    · omega
    · exact absurd h2 hra

/-- **Masked index, exact answer.** -/
theorem mapMasked_eq_mapSpec (sc : Scoring) (T : Int) (g : Genome) (read : List Char)
    (score : Window → Option Int) (hs : ∀ w, score w = windowScore sc read g w)
    (C : List Window) (dup : Window → Bool) (hsound : DupSound g dup)
    (hcov : MaskCover sc T g read C dup) :
    mapMasked score T C dup = mapSpec sc T g read := by
  have hsc : score = windowScore sc read g := funext hs
  subst hsc
  have hfunC : ∀ a ∈ hitsOf (windowScore sc read g) T C, ∀ b ∈ hitsOf (windowScore sc read g) T C,
      a.1 = b.1 → a.2 = b.2 := by
    rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this
  -- the spec's best, if any, is the candidates' best
  have hbestC : ∀ a sa, mapSpec sc T g read = some (a, sa) →
      selectUnique (hitsOf (windowScore sc read g) T C) = some (a, sa) := by
    intro a sa h
    have haC := mem_C_of_best sc T g read C dup hcov a sa h
    obtain ⟨⟨hsa, hTa⟩, hall⟩ := (mapSpec_some_iff sc T g read a sa).mp h
    rw [selectUnique_eq_some_iff _ hfunC, mem_hitsOf]
    refine ⟨⟨haC, hsa, hTa⟩, ?_⟩
    rintro ⟨w', s'⟩ hb
    rw [mem_hitsOf] at hb
    exact hall w' s' hb.2.1 hb.2.2
  unfold mapMasked
  cases hsel : selectUnique (hitsOf (windowScore sc read g) T C) with
  | none =>
    cases h : mapSpec sc T g read with
    | none => rfl
    | some a => obtain ⟨a, sa⟩ := a; rw [hbestC a sa h] at hsel; cases hsel
  | some r =>
    obtain ⟨w, s⟩ := r
    obtain ⟨hmem, hq⟩ := (selectUnique_eq_some_iff _ hfunC (w, s)).mp hsel
    rw [mem_hitsOf] at hmem
    obtain ⟨hwC, hws, hTw⟩ := hmem
    simp only
    cases hd : dup w with
    | true =>
      simp only [if_true]
      cases h : mapSpec sc T g read with
      | none => rfl
      | some a =>
        obtain ⟨a, sa⟩ := a
        have := hbestC a sa h
        rw [hsel] at this
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        obtain ⟨w', hne, hseq⟩ := hsound w hd
        exact absurd h (mapSpec_ne_of_duplicate sc T g read w w' hne hseq s)
    | false =>
      simp only [Bool.false_eq_true, if_false]
      symm
      rw [mapSpec_some_iff]
      refine ⟨⟨hws, hTw⟩, fun w' s' hs' hT' => ?_⟩
      rcases hcov w' s' hs' hT' with h1 | ⟨r, hrC, hrw, hseq, hdr⟩
      · exact hq (w', s') ((mem_hitsOf _ _ _ _ _).mpr ⟨h1, hs', hT'⟩)
      · have hsr : windowScore sc read g r = some s' := by
          rw [windowScore_eq_of_seq sc read g w' r hseq, hs']
        rcases hq (r, s') ((mem_hitsOf _ _ _ _ _).mpr ⟨hrC, hsr, hT'⟩) with h2 | h2
        · exact Or.inl h2
        · simp only at h2
          subst h2
          rw [hd] at hdr; cases hdr

end MapSpec

#print axioms MapSpec.mapSpec_ne_of_duplicate
#print axioms MapSpec.mapSpec_none_of_best_duplicated
#print axioms MapSpec.mapSpec_none_of_best_in_region
#print axioms MapSpec.mapMasked_eq_mapSpec
