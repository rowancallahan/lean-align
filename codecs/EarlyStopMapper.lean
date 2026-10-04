import MapSpec                    -- the mapping specification (spec/, draft)
import MapperSeedsAmong           -- pool: clean seed among any chosen seeds
import MapperGapless              -- pool: selectUnique lemmas
import SeedMapper2                -- mapWithK and its theorem
import LowErrorMapper             -- mem_allWindows_of_score

/-!
# Codec `mapEarly`: seed lookups in any order, stopping early

The seeds of `mapWithK` are looked up one at a time, in a caller-chosen order
(any permutation of the seed indices).  After each lookup, let `B` be the best
score among the hits found so far.  A window that ties or beats `B` spoils at
most `seedBound sc B` seeds (default scoring: `P / 4` for penalty `P = −B`),
so once more than `seedBound sc B` seeds have been looked up, every window
that can tie or beat `B` is already a candidate: stop and answer.

General facts used (any candidate list `C`, scorer = `windowScore`):

    selectUnique_cover_all    C has every window scoring ≥ T → answer = mapSpec
    selectUnique_cover_above  T ≤ S, C has every window scoring ≥ S and one
                              window scoring ≥ S → answer = mapSpec
    mem_seedCands_among       a window scoring ≥ S is a candidate of any
                              `seedBound sc S + 1` distinct seeds
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Windows from seed `j` alone (one term of `seedCandidatesK`). -/
def seedCands (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (read : List Char) (k d d2 : Nat) (j : Nat) : List Window :=
  ((lookup (((read.drop (j * (read.length / (k + 1)))).take (read.length / (k + 1))).take l0)).filter
      (keep ((read.drop (j * (read.length / (k + 1)))).take (read.length / (k + 1))))).flatMap
    fun place =>
      (shapes d d2).filterMap fun st =>
        if ((j * (read.length / (k + 1)) : Nat) : Int) + st.1 ≤ place.2 ∧
            0 ≤ (read.length : Int) + st.1 + st.2 then
          some { chr := place.1, start := ((place.2 : Int) - (j * (read.length / (k + 1)) : Nat) - st.1).toNat,
                 len := ((read.length : Int) + st.1 + st.2).toNat }
        else none

/-- Look up seeds in `order`, accumulating hits; stop as soon as the number of
seeds looked up exceeds `bound B` for the best hit score `B` so far. -/
def earlyLoop (cands : Nat → List Window) (score : Window → Option Int) (T : Int) (bound : Int → Nat) :
    List Nat → Nat → List (Window × Int) → List (Window × Int)
  | [], _, acc => acc
  | j :: rest, m, acc =>
    let acc' := acc ++ hitsOf score T (cands j)
    match (acc'.map (·.2)).max? with
    | some B => if bound B < m + 1 then acc' else earlyLoop cands score T bound rest (m + 1) acc'
    | none => earlyLoop cands score T bound rest (m + 1) acc'

/-- Early-stopping mapper; the seed `order` is free. -/
def mapEarly (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (score : Window → Option Int) (bound : Int → Nat) (l0 : Nat) (T : Int) (k d d2 : Nat)
    (g : Genome) (read : List Char) (order : List Nat) : Option (Window × Int) :=
  if 0 < l0 ∧ l0 ≤ read.length / (k + 1) then
    selectUnique (earlyLoop (seedCands keep lookup l0 read k d d2) score T bound order 0 [])
  else mapWithK keep lookup score l0 T k d d2 g read

/-! ## The theorem

    order ~ List.range (seedBound sc T + 1) →
      mapEarly keep lookup score (seedBound sc) l0 T
        (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read order
      = mapSpec sc T g read                                                (mapEarly_eq_mapSpec)

given `ValidScoring sc`, `LookupComplete g l0 lookup`, `KeepComplete g keep`
and a scorer equal to `windowScore`. -/

/-! ## Proof -/

theorem selectUnique_cover_all (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window)
    (hC : ∀ w s, windowScore sc read g w = some s → T ≤ s → w ∈ C) :
    selectUnique (hitsOf (windowScore sc read g) T C) = mapSpec sc T g read := by
  unfold mapSpec
  apply selectUnique_congr
  · rintro ⟨w, s⟩
    rw [mem_hitsOf, mem_hitsOf]
    constructor
    · rintro ⟨-, hs, hT⟩; exact ⟨mem_allWindows_of_score sc read g w s hs, hs, hT⟩
    · rintro ⟨-, hs, hT⟩; exact ⟨hC w s hs hT, hs, hT⟩
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

theorem hits_functional (sc : Scoring) (T : Int) (g : Genome) (read : List Char) (C : List Window) :
    ∀ a ∈ hitsOf (windowScore sc read g) T C, ∀ b ∈ hitsOf (windowScore sc read g) T C,
      a.1 = b.1 → a.2 = b.2 := by
  rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
  rw [mem_hitsOf] at ha hb
  simp only at hww
  subst hww
  have := ha.2.1.symm.trans hb.2.1
  simpa using this

/-- **Cover above `S`.**  If the candidates contain every window scoring at
least `S ≥ T`, and one of them scores at least `S`, the answer is `mapSpec`. -/
theorem selectUnique_cover_above (sc : Scoring) (T S : Int) (hTS : T ≤ S) (g : Genome) (read : List Char)
    (C : List Window) (hC : ∀ w s, windowScore sc read g w = some s → S ≤ s → w ∈ C)
    (w0 : Window) (s0 : Int) (hw0 : w0 ∈ C) (hs0 : windowScore sc read g w0 = some s0) (hS0 : S ≤ s0) :
    selectUnique (hitsOf (windowScore sc read g) T C) = mapSpec sc T g read := by
  unfold mapSpec
  have hm0 : (w0, s0) ∈ hitsOf (windowScore sc read g) T C :=
    (mem_hitsOf _ _ _ _ _).mpr ⟨hw0, hs0, by omega⟩
  have hm0' : (w0, s0) ∈ hitsOf (windowScore sc read g) T (allWindows g) :=
    (mem_hitsOf _ _ _ _ _).mpr ⟨mem_allWindows_of_score sc read g w0 s0 hs0, hs0, by omega⟩
  rw [← selectUnique_filter _ S (hits_functional sc T g read C) ⟨_, hm0, hS0⟩,
    ← selectUnique_filter _ S (hits_functional sc T g read _) ⟨_, hm0', hS0⟩]
  apply selectUnique_congr
  · rintro ⟨w, s⟩
    simp only [List.mem_filter, decide_eq_true_eq, mem_hitsOf]
    constructor
    · rintro ⟨⟨-, hs, hT⟩, hSs⟩; exact ⟨⟨mem_allWindows_of_score sc read g w s hs, hs, hT⟩, hSs⟩
    · rintro ⟨⟨-, hs, hT⟩, hSs⟩; exact ⟨⟨hC w s hs hSs, hs, hT⟩, hSs⟩
  · intro a ha b hb hab
    exact hits_functional sc T g read C a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1 hab

theorem shapeOk_mono (d d2 D D2 : Nat) (s t : Int) (h : shapeOk d d2 s t) (hd : d ≤ D) (hd2 : d2 ≤ D2) :
    shapeOk D D2 s t := by
  unfold shapeOk at *; omega

theorem gapBound_mono (sc : Scoring) (hv : ValidScoring sc) (T S : Int) (h : T ≤ S) :
    gapBound sc S ≤ gapBound sc T ∧ gapBound2 sc S ≤ gapBound2 sc T := by
  have hE : 0 < -sc.gapExtend := by have := hv.2.2.2; omega
  unfold gapBound gapBound2
  exact ⟨Int.toNat_le_toNat (Int.ediv_le_ediv hE (by omega)),
    Int.toNat_le_toNat (Int.ediv_le_ediv hE (by omega))⟩

/-- **Coverage by any chosen seeds.**  A window scoring at least `S` is a
candidate of any `J` of more than `seedBound sc S` distinct seeds, provided
the shape bounds `d, d2` are at least those at `S`. -/
theorem mem_seedCands_among (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (S : Int) (g : Genome)
    (hl : LookupComplete g l0 lookup) (hk : KeepComplete g keep)
    (read : List Char) (k d d2 : Nat) (hcond : 0 < l0 ∧ l0 ≤ read.length / (k + 1))
    (hd : gapBound sc S ≤ d) (hd2 : gapBound2 sc S ≤ d2)
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBound sc S < J.length)
    (w : Window) (s : Int) (hscore : windowScore sc read g w = some s) (hS : S ≤ s) :
    w ∈ J.flatMap (seedCands keep lookup l0 read k d d2) := by
  unfold windowScore at hscore
  cases hseq : windowSeq g w with
  | none => rw [hseq] at hscore; cases hscore
  | some ys =>
    rw [hseq] at hscore
    simp only at hscore
    cases hbest : getBestAlignment sc read ys with
    | none => rw [hbest] at hscore; cases hscore
    | some best =>
      rw [hbest] at hscore
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hscore
      subst hsb
      obtain ⟨hwalk, hws⟩ := getBestAlignment_returns_a_valid_walk sc read ys path bs hbest
      obtain ⟨j, hjJ, o, ho, hseed, hshape⟩ :=
        exists_clean_seed_among sc hv S read ys path hwalk (by rw [hws]; exact hS) k J hJn hJk hJl
      have hj := hJk j hjJ
      have hshape' := shapeOk_mono _ _ _ _ _ _ hshape hd hd2
      unfold windowSeq at hseq
      cases hc : g[w.chr]? with
      | none => rw [hc] at hseq; cases hseq
      | some chromosome =>
        rw [hc] at hseq
        simp only at hseq
        split at hseq
        · next hfit =>
          have hys : ys = (chromosome.seq.drop w.start).take w.len := by
            simpa using hseq.symm
          have hyl : ys.length = w.len := by
            rw [hys, List.length_take, List.length_drop]; omega
          generalize hq : read.length / (k + 1) = q at *
          have hjq : j * q + q ≤ read.length := by
            have h1 : (k + 1) * q ≤ read.length := by
              rw [← hq, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
            have : j * q ≤ k * q := Nat.mul_le_mul_right q hj
            rw [Nat.add_mul] at h1; omega
          have hseedlen : ((read.drop (j * q)).take q).length = q := by
            simp; omega
          have hgen : (chromosome.seq.drop (w.start + o)).take q = (read.drop (j * q)).take q := by
            rw [← hseed, hys, take_drop_window _ _ _ _ _ (by omega)]
          rw [List.mem_flatMap]
          refine ⟨j, hjJ, ?_⟩
          simp only [seedCands, hq]
          rw [List.mem_flatMap]
          refine ⟨(w.chr, w.start + o), ?_, ?_⟩
          · rw [List.mem_filter]
            constructor
            · have hkey : ((read.drop (j * q)).take q).take l0 =
                  (chromosome.seq.drop (w.start + o)).take l0 := by
                rw [← hgen, List.take_take, Nat.min_eq_left hcond.2]
              rw [hkey]
              exact hl w.chr chromosome (w.start + o) hc (by omega)
            · exact hk w.chr chromosome (w.start + o) _ hc (by rw [hseedlen]; omega)
                (by rw [hseedlen]; exact hgen)
          · rw [List.mem_filterMap]
            refine ⟨_, mem_shapes _ _ _ _ hshape', ?_⟩
            rw [if_pos (by constructor <;> omega)]
            cases w
            simp only [Option.some.injEq, Window.mk.injEq] at *
            refine ⟨trivial, by omega, by omega⟩
        · cases hseq

theorem hitsOf_append (score : Window → Option Int) (T : Int) (a b : List Window) :
    hitsOf score T (a ++ b) = hitsOf score T a ++ hitsOf score T b := by
  unfold hitsOf; exact List.filterMap_append

/-- What `earlyLoop` returns: the hits of the seeds looked up (a prefix of the
order), and either all seeds were looked up or it stopped because more than
`bound B` seeds were looked up, `B` the best hit score. -/
theorem earlyLoop_spec (cands : Nat → List Window) (score : Window → Option Int) (T : Int)
    (bound : Int → Nat) (rest done : List Nat) :
    ∃ taken, taken <+: rest ∧
      earlyLoop cands score T bound rest done.length (hitsOf score T (done.flatMap cands)) =
        hitsOf score T ((done ++ taken).flatMap cands) ∧
      (taken = rest ∨ ∃ B, ((hitsOf score T ((done ++ taken).flatMap cands)).map (·.2)).max? = some B ∧
        bound B < (done ++ taken).length) := by
  induction rest generalizing done with
  | nil => exact ⟨[], List.prefix_refl _, by simp [earlyLoop], Or.inl rfl⟩
  | cons j rest ih =>
    have hacc : hitsOf score T (done.flatMap cands) ++ hitsOf score T (cands j) =
        hitsOf score T ((done ++ [j]).flatMap cands) := by
      rw [List.flatMap_append, hitsOf_append]; simp
    obtain ⟨taken, hpre, heq, halt⟩ := ih (done ++ [j])
    have hlen : (done ++ [j]).length = done.length + 1 := by simp
    rw [hlen] at heq
    have hcont : earlyLoop cands score T bound (j :: rest) done.length (hitsOf score T (done.flatMap cands)) =
        earlyLoop cands score T bound rest (done.length + 1) (hitsOf score T ((done ++ [j]).flatMap cands)) ∨
        (∃ B, ((hitsOf score T ((done ++ [j]).flatMap cands)).map (·.2)).max? = some B ∧
          bound B < done.length + 1 ∧
          earlyLoop cands score T bound (j :: rest) done.length (hitsOf score T (done.flatMap cands)) =
            hitsOf score T ((done ++ [j]).flatMap cands)) := by
      simp only [earlyLoop, hacc]
      split
      · rename_i B hB
        split
        · right; exact ⟨B, hB, by omega, rfl⟩
        · left; rfl
      · left; rfl
    rcases hcont with hc | ⟨B, hB, hbB, hc⟩
    · refine ⟨j :: taken, List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, ?_, ?_⟩
      · rw [hc, heq]; simp
      · rcases halt with h | ⟨B, hB, hbB⟩
        · left; rw [h]
        · right; exact ⟨B, by simpa using hB, by simpa using hbB⟩
    · refine ⟨[j], List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩, hc, Or.inr ⟨B, hB, by simpa using hbB⟩⟩

/-- **Early stop, any seed order.**  `mapEarly` returns the specification's
answer for every order that is a permutation of the seed indices. -/
theorem mapEarly_eq_mapSpec (keep : List Char → Nat × Nat → Bool)
    (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hk : KeepComplete g keep)
    (hs : ∀ w, score w = windowScore sc read g w)
    (order : List Nat) (hperm : order.Perm (List.range (seedBound sc T + 1))) :
    mapEarly keep lookup score (seedBound sc) l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T)
      g read order = mapSpec sc T g read := by
  unfold mapEarly
  split
  · rename_i hcond
    have hsc : score = windowScore sc read g := funext hs
    obtain ⟨taken, hpre, heq, halt⟩ := earlyLoop_spec
      (seedCands keep lookup l0 read (seedBound sc T) (gapBound sc T) (gapBound2 sc T))
      score T (seedBound sc) order []
    simp only [List.length_nil, List.flatMap_nil, List.nil_append] at heq halt
    have hnil : hitsOf score T [] = [] := rfl
    rw [hnil] at heq
    rw [heq, hsc]
    have hnd : order.Nodup := hperm.nodup_iff.mpr List.nodup_range
    have hk' : ∀ j ∈ order, j ≤ seedBound sc T := by
      intro j hj
      have := List.mem_range.mp (hperm.mem_iff.mp hj)
      omega
    have hTn : taken.Nodup := hnd.sublist hpre.sublist
    have hTk : ∀ j ∈ taken, j ≤ seedBound sc T := fun j hj => hk' j (hpre.subset hj)
    rcases halt with h | ⟨B, hB, hbB⟩
    · subst h
      apply selectUnique_cover_all
      intro w s hws hT
      exact mem_seedCands_among keep lookup l0 sc hv T g hl hk read _ _ _ hcond (Nat.le_refl _)
        (Nat.le_refl _) taken hTn hTk (by rw [hperm.length_eq]; simp) w s hws hT
    · rw [hsc] at hB
      obtain ⟨⟨w0, s0⟩, hm0, hs0⟩ := List.mem_map.mp (List.max?_mem hB)
      simp only at hs0
      subst hs0
      obtain ⟨hw0, hws0, hT0⟩ := (mem_hitsOf _ _ _ _ _).mp hm0
      have hmono := gapBound_mono sc hv T s0 hT0
      apply selectUnique_cover_above sc T s0 hT0 g read _ _ w0 s0 hw0 hws0 (Int.le_refl _)
      intro w s hws hS
      exact mem_seedCands_among keep lookup l0 sc hv s0 g hl hk read _ _ _ hcond hmono.1 hmono.2
        taken hTn hTk hbB w s hws hS
  · exact mapWithK_eq_mapSpec keep lookup score l0 sc hv T g read hl hk hs

end MapSpec

#print axioms MapSpec.selectUnique_cover_all
#print axioms MapSpec.selectUnique_cover_above
#print axioms MapSpec.mem_seedCands_among
#print axioms MapSpec.mapEarly_eq_mapSpec
