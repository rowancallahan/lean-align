import MapperDefs

/-! List and table membership lemmas for the seed-and-index mapper. -/

namespace MapSpec

/-- When at most one member of `l` satisfies `p`, `find?` returns exactly that member. -/
private theorem find?_eq_some_iff_of_unique {α : Type} (p : α → Bool) (l : List α)
    (huniq : ∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) (a : α) :
    l.find? p = some a ↔ a ∈ l ∧ p a = true := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩
  · intro ⟨hm, hp⟩
    cases h : l.find? p with
    | none =>
      have := List.find?_eq_none.1 h a hm
      exact absurd hp this
    | some b =>
      have hb := huniq b (List.mem_of_find?_eq_some h) a hm (List.find?_some h) hp
      rw [hb]

/-- `selectUnique` depends only on which hits are present. -/
theorem selectUnique_congr (l₁ l₂ : List (Window × Int))
    (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂)
    (hfun : ∀ a ∈ l₁, ∀ b ∈ l₁, a.1 = b.1 → a.2 = b.2) :
    selectUnique l₁ = selectUnique l₂ := by
  have hp : (fun a : Window × Int => l₂.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1))
      = (fun a : Window × Int => l₁.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) := by
    funext a
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h b hb
      exact h b ((hmem b).1 hb)
    · intro h b hb
      exact h b ((hmem b).2 hb)
  have huniq : ∀ a ∈ l₁, ∀ b ∈ l₁,
      (l₁.all fun c => decide (c.2 < a.2) || decide (c.1 = a.1)) = true →
      (l₁.all fun c => decide (c.2 < b.2) || decide (c.1 = b.1)) = true → a = b := by
    intro a ha b hb pa pb
    have h1 := List.all_eq_true.1 pa b hb
    have h2 := List.all_eq_true.1 pb a ha
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 h2
    have h12 : a.1 = b.1 := by
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · omega
        · exact h2
      · exact h1.symm
    exact Prod.ext h12 (hfun a ha b hb h12)
  have huniq₂ : ∀ a ∈ l₂, ∀ b ∈ l₂,
      (l₁.all fun c => decide (c.2 < a.2) || decide (c.1 = a.1)) = true →
      (l₁.all fun c => decide (c.2 < b.2) || decide (c.1 = b.1)) = true → a = b :=
    fun a ha b hb => huniq a ((hmem a).2 ha) b ((hmem b).2 hb)
  unfold selectUnique
  rw [hp]
  apply Option.ext
  intro a
  rw [find?_eq_some_iff_of_unique _ l₁ huniq a, find?_eq_some_iff_of_unique _ l₂ huniq₂ a, hmem a]

theorem mem_hitsOf (score : Window → Option Int) (T : Int) (ws : List Window) (w : Window) (s : Int) :
    (w, s) ∈ hitsOf score T ws ↔ w ∈ ws ∧ score w = some s ∧ T ≤ s := by
  unfold hitsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨w', hw', h⟩
    cases hs : score w' with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs] at h
      by_cases hT : T ≤ s'
      · simp only [hT, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hw', hs, hT⟩
      · simp [hT] at h
  · rintro ⟨hw, hs, hT⟩
    exact ⟨w, hw, by simp [hs, hT]⟩

theorem mem_allWindows (g : Genome) (w : Window) :
    w ∈ allWindows g ↔ (windowSeq g w).isSome := by
  cases w with
  | mk c st ln =>
  unfold allWindows windowSeq
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Window.mk.injEq]
  constructor
  · rintro ⟨c', hc', st', hst', ln', hln', rfl, rfl, rfl⟩
    have hg : g[c']? = some g[c'] := List.getElem?_eq_getElem hc'
    simp only [hg] at hst' hln' ⊢
    have : st' + ln' ≤ g[c'].seq.length := by omega
    simp [this]
  · intro h
    cases hg : g[c]? with
    | none => simp [hg] at h
    | some ch =>
      simp only [hg] at h ⊢
      by_cases hle : st + ln ≤ ch.seq.length
      · have hc : c < g.length := by
          obtain ⟨hc, _⟩ := List.getElem?_eq_some_iff.1 hg
          exact hc
        refine ⟨c, hc, st, ?_, ln, ?_, rfl, rfl, rfl⟩
        · simp only [hg]; omega
        · simp only [hg]; omega
      · simp [hle] at h

theorem mem_wordsOf (l0 c : Nat) (seq : List Char) (p : Nat) (h : p + l0 ≤ seq.length) :
    ((seq.drop p).take l0, (c, p)) ∈ wordsOf l0 c seq := by
  unfold wordsOf
  exact List.mem_map.2 ⟨p, List.mem_range.2 (by omega), rfl⟩

private theorem mem_foldl_table (items : List (List Char × (Nat × Nat))) (key : List Char)
    (place : Nat × Nat) :
    ∀ (m : Std.HashMap (List Char) (List (Nat × Nat))),
      ((key, place) ∈ items ∨ place ∈ m.getD key []) →
      place ∈ (items.foldl (fun m (x : List Char × (Nat × Nat)) =>
        m.insert x.1 (x.2 :: m.getD x.1 [])) m).getD key [] := by
  induction items with
  | nil =>
    intro m h
    rcases h with h | h
    · cases h
    · exact h
  | cons x xs ih =>
    intro m h
    rw [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.1 h with h | h
      · right
        subst h
        rw [Std.HashMap.getD_insert]
        simp
      · exact Or.inl h
    · right
      rw [Std.HashMap.getD_insert]
      by_cases hk : (x.1 == key) = true
      · rw [if_pos hk]
        have : x.1 = key := by simpa using hk
        subst this
        exact List.mem_cons_of_mem _ h
      · rw [if_neg hk]
        exact h

theorem mem_buildTable (items : List (List Char × (Nat × Nat))) (key : List Char) (place : Nat × Nat)
    (h : (key, place) ∈ items) :
    place ∈ (buildTable items).getD key [] :=
  mem_foldl_table items key place ∅ (Or.inl h)

#print axioms selectUnique_congr
#print axioms mem_hitsOf
#print axioms mem_allWindows
#print axioms mem_wordsOf
#print axioms mem_buildTable

end MapSpec
