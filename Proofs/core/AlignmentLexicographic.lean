import AlignmentAlgorithms

/-!
The tie-break characterization theorem: the path returned by the frozen
`getBestAlignment` is exactly the LEXICOGRAPHICALLY LEAST optimal path,
under the step order diag < gapX < gapY.

This modularizes the frozen contract's tie policy: a submission can now
prove (i) its returned path is a valid walk achieving the optimal score
and (ii) it is lexicographically least among optimal paths, instead of
replaying the spec's enumeration order.  No spec change — this is a
theorem ABOUT the frozen definition.
-/

namespace AlignmentSpec

def stepIdx : Step → Nat
  | .diag => 0
  | .gapX => 1
  | .gapY => 2

def stepLT (a b : Step) : Prop := stepIdx a < stepIdx b

/-- Strict lexicographic order on step lists: smaller step at the first
differing position wins; a proper prefix is smaller. -/
inductive LexLT : List Step → List Step → Prop
  | nil {b : Step} {bs : List Step} : LexLT [] (b :: bs)
  | head {a b : Step} {as bs : List Step} :
      stepLT a b → LexLT (a :: as) (b :: bs)
  | tail {a : Step} {as bs : List Step} :
      LexLT as bs → LexLT (a :: as) (a :: bs)

/-- The spec's enumeration lists alignments in strictly increasing
lexicographic order. -/
theorem allPaths_pairwise_lexLT (xs ys : List Char) :
    (allPaths xs ys).Pairwise LexLT := by
  induction xs, ys using allPaths.induct with
  | case1 =>
      simp [allPaths]
  | case2 y ys ih =>
      rw [allPaths]
      exact (List.pairwise_map).mpr (ih.imp fun h => .tail h)
  | case3 x xs ih =>
      rw [allPaths]
      exact (List.pairwise_map).mpr (ih.imp fun h => .tail h)
  | case4 x xs y ys ihDiag ihGapX ihGapY =>
      rw [allPaths]
      apply (List.pairwise_append).mpr
      refine ⟨(List.pairwise_append).mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · exact (List.pairwise_map).mpr (ihDiag.imp fun h => .tail h)
      · exact (List.pairwise_map).mpr (ihGapX.imp fun h => .tail h)
      · intro p hp q hq
        obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
        obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
        exact .head (by simp [stepLT, stepIdx])
      · exact (List.pairwise_map).mpr (ihGapY.imp fun h => .tail h)
      · intro p hp q hq
        obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
          exact .head (by simp [stepLT, stepIdx])
        · obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
          exact .head (by simp [stepLT, stepIdx])

/-- The earliest maximum splits the list into a strictly-smaller prefix,
the maximum itself, and a remainder. -/
theorem maxOn?_earliest_split {α : Type} (f : α → Int) (l : List α)
    (b : α) (h : l.maxOn? f = some b) :
    ∃ l1 l2, l = l1 ++ b :: l2 ∧ ∀ a ∈ l1, f a < f b := by
  induction l generalizing b with
  | nil => simp at h
  | cons a t ih =>
      rw [List.maxOn?_cons] at h
      cases htm : t.maxOn? f with
      | none =>
          have ht : t = [] := by
            have := (List.isSome_maxOn?_iff (f := f) (xs := t))
            cases t with
            | nil => rfl
            | cons c u =>
                rw [htm] at this
                simp at this
          subst ht
          rw [htm] at h
          simp at h
          exact ⟨[], [], by simp [h], by simp⟩
      | some c =>
          rw [htm] at h
          simp only [Option.elim_some, Option.some.injEq] at h
          by_cases hcase : f c ≤ f a
          · rw [maxOn_eq_left hcase] at h
            subst h
            refine ⟨[], t, rfl, by simp⟩
          · rw [maxOn_eq_right hcase] at h
            subst h
            obtain ⟨t1, t2, hsplit, hsmall⟩ := ih c htm
            refine ⟨a :: t1, t2, by simp [hsplit], ?_⟩
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · omega
            · exact hsmall d hd

/-- THE TIE-BREAK CHARACTERIZATION: the path the frozen spec returns is
lexicographically least among all optimal valid walks. -/
theorem getBestAlignment_lex_least (sc : Scoring) (xs ys : List Char)
    (p : List Step) (s : Int)
    (hret : getBestAlignment sc xs ys = some (p, s))
    (q : List Step)
    (hq : IsMonotoneWalk q xs ys)
    (hopt : walkScore sc xs ys q = s) :
    p = q ∨ LexLT p q := by
  rw [getBestAlignment] at hret
  obtain ⟨l1, l2, hsplit, hsmall⟩ :=
    maxOn?_earliest_split _ _ _ hret
  have hqmem : q ∈ allPaths xs ys :=
    mem_allPaths_of_isMonotoneWalk q xs ys hq
  have hqpair : (q, s) ∈
      (allPaths xs ys).map fun path => (path, walkScore sc xs ys path) :=
    List.mem_map.mpr ⟨q, hqmem, by rw [hopt]⟩
  rw [hsplit] at hqpair
  have hpw :
      (((allPaths xs ys).map
        fun path => (path, walkScore sc xs ys path)).Pairwise
          fun u v => LexLT u.1 v.1) :=
    (List.pairwise_map).mpr
      ((allPaths_pairwise_lexLT xs ys).imp fun h => h)
  rw [hsplit] at hpw
  rcases List.mem_append.mp hqpair with hin | hin
  · exact absurd (hsmall _ hin) (by simp)
  · rcases List.mem_cons.mp hin with heq | hin
    · left
      exact (congrArg Prod.fst heq.symm : _)
    · right
      have := (List.pairwise_append.mp hpw).2.1
      rw [List.pairwise_cons] at this
      exact this.1 (q, s) hin

/-- Packaging: together with the frozen spec's own theorems, the
returned pair is characterized as "a valid walk, achieving the optimal
score, lexicographically least among walks that achieve it".  A future
submission may prove those three properties of its output instead of
replaying the enumeration. -/
theorem getBestAlignment_characterization (sc : Scoring)
    (xs ys : List Char) (p : List Step) (s : Int)
    (hret : getBestAlignment sc xs ys = some (p, s)) :
    IsMonotoneWalk p xs ys ∧
    walkScore sc xs ys p = s ∧
    (∀ q, IsMonotoneWalk q xs ys →
      walkScore sc xs ys q ≤ s) ∧
    (∀ q, IsMonotoneWalk q xs ys → walkScore sc xs ys q = s →
      p = q ∨ LexLT p q) := by
  obtain ⟨hvalid, hscore⟩ :=
    getBestAlignment_returns_a_valid_walk sc xs ys p s hret
  refine ⟨hvalid, hscore, ?_, ?_⟩
  · intro q hq
    exact getBestAlignment_returns_a_maximum_score sc xs ys p s q hret hq
  · intro q hq hopt
    exact getBestAlignment_lex_least sc xs ys p s hret q hq hopt

end AlignmentSpec
