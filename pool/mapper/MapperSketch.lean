import MapSpec

/-! Seed sketches: what a seed index may store instead of every word.

A sketch maps a string to (key, offset) summaries.  The mapper only needs two
facts about it (`SeedSketch`):

* `conserved`: every summary of `x` is a summary of every string `y` that
  contains `x` (at the shifted offset).  So a summary of a clean read seed is
  found in the genome at the place the seed occurs.
* `nonempty`: every string of length ≥ `L` has a summary.

From these, an exact match of length `L` shares a key at the same relative
offset (`SeedSketch.anchored`).  Instances:

* `windowSketch L sel`: any function of each `L`-letter window (key + offset
  chosen from the window's own letters).  Every k-mer (`kmerSketch`) and
  `(w, k)` minimizers under any order (`minimizerSketch`, `L = w + k - 1`)
  are window sketches; there is nothing to prove about the order.
* `ctxSketch sel L`: context-free selection — whether a key starts at a
  position, and its length, is decided by the key's own letters
  (`PrefixDet`).  Needs a hitting property (`Hits sel L`): every `L`-letter
  string contains a selected key.  Fixed-length instance: closed syncmers
  (`closedSyncmer_hits`, `L = 2k - s - 1`, any order on s-mers).  Variable
  length keys fit the same form. -/

namespace MapSpec

/-- (key, offset) summaries with the two properties the mapper needs. -/
structure SeedSketch (κ : Type) where
  L : Nat
  sketch : List Char → List (κ × Nat)
  conserved : ∀ (x y : List Char) (b : Nat), b + x.length ≤ y.length →
    (y.drop b).take x.length = x → ∀ e ∈ sketch x, (e.1, b + e.2) ∈ sketch y
  nonempty : ∀ x : List Char, L ≤ x.length → sketch x ≠ []

theorem take_drop_sub (seq : List Char) (st len o m : Nat) (h : o + m ≤ len) :
    (((seq.drop st).take len).drop o).take m = (seq.drop (st + o)).take m := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

/-- **Exact match ⇒ shared key.**  If `x` at `a` and `y` at `b` agree on `L`
letters, some key sits at `a + d` in `x` and at `b + d` in `y`. -/
theorem SeedSketch.anchored {κ : Type} (S : SeedSketch κ) (x y : List Char) (a b : Nat)
    (hx : a + S.L ≤ x.length) (hy : b + S.L ≤ y.length)
    (h : (x.drop a).take S.L = (y.drop b).take S.L) :
    ∃ key d, (key, a + d) ∈ S.sketch x ∧ (key, b + d) ∈ S.sketch y := by
  have hu : ((x.drop a).take S.L).length = S.L := by simp; omega
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (S.nonempty _ (Nat.le_of_eq hu.symm))
  refine ⟨e.1, e.2, S.conserved _ x a (by omega) (by rw [hu]) e he, ?_⟩
  exact S.conserved _ y b (by omega) (by rw [hu, h]) e he

/-! ## Window sketches: any function of the `L`-letter windows -/

/-- For each `L`-letter window at `i`: `sel window = (key, d)` gives the summary
`(key, i + d)`. -/
def windowSketchFn {κ : Type} (L : Nat) (sel : List Char → κ × Nat) (x : List Char) :
    List (κ × Nat) :=
  (List.range (x.length + 1 - L)).map fun i =>
    ((sel ((x.drop i).take L)).1, i + (sel ((x.drop i).take L)).2)

theorem mem_windowSketchFn {κ : Type} (L : Nat) (sel : List Char → κ × Nat) (x : List Char)
    (e : κ × Nat) :
    e ∈ windowSketchFn L sel x ↔ ∃ i, i + L ≤ x.length ∧
      e = ((sel ((x.drop i).take L)).1, i + (sel ((x.drop i).take L)).2) := by
  unfold windowSketchFn
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [List.mem_range] at hi; omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mpr (by omega), rfl⟩

def windowSketch {κ : Type} (L : Nat) (sel : List Char → κ × Nat) : SeedSketch κ where
  L := L
  sketch := windowSketchFn L sel
  conserved := by
    intro x y b hb hx e he
    rw [mem_windowSketchFn] at he ⊢
    obtain ⟨i, hi, rfl⟩ := he
    refine ⟨b + i, by omega, ?_⟩
    have hw : (y.drop (b + i)).take L = (x.drop i).take L := by
      conv => rhs; rw [← hx]
      rw [take_drop_sub _ _ _ _ _ hi]
    rw [hw]
    simp only [Prod.mk.injEq, true_and]
    omega
  nonempty := by
    intro x hx h
    have := (mem_windowSketchFn L sel x _).mpr ⟨0, by omega, rfl⟩
    rw [h] at this
    cases this

/-- Every k-mer, keyed by its letters. -/
def kmerSketch (k : Nat) : SeedSketch (List Char) := windowSketch k fun w => (w, 0)

/-- Leftmost index in `[0, w)` minimising `f` (`0` when `w = 0`). -/
def argminLeft (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => if f w < f (argminLeft f w) then w else argminLeft f w

theorem argminLeft_lt (f : Nat → Nat) (w : Nat) (hw : 0 < w) : argminLeft f w < w := by
  induction w with
  | zero => omega
  | succ w ih =>
    unfold argminLeft
    split
    · omega
    · rcases Nat.eq_zero_or_pos w with h | h
      · subst h; simp [argminLeft]
      · have := ih h; omega

theorem argminLeft_le (f : Nat → Nat) (w : Nat) : ∀ i, i < w → f (argminLeft f w) ≤ f i := by
  induction w with
  | zero => intro i hi; omega
  | succ w ih =>
    intro i hi
    unfold argminLeft
    split
    · rename_i h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · have := ih i hi; omega
      · subst hi; omega
    · rename_i h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih i hi
      · subst hi; omega

/-- `(w, k)` minimizers: in each window of `w` consecutive k-mers, the
leftmost k-mer of least `ord`.  Any `ord` (random hash, decycling-based,
…): the order changes only the density. -/
def minimizerSketch (k w : Nat) (ord : List Char → Nat) : SeedSketch (List Char) :=
  windowSketch (w + k - 1) fun win =>
    let m := argminLeft (fun i => ord ((win.drop i).take k)) w
    ((win.drop m).take k, m)

/-- A minimizer's key is the k-mer at its offset (so an index can store
positions only). -/
theorem minimizerSketch_key (k w : Nat) (ord : List Char → Nat) (hw : 0 < w) (x : List Char)
    (e : List Char × Nat) (he : e ∈ (minimizerSketch k w ord).sketch x) :
    e.1 = (x.drop e.2).take k ∧ e.2 + k ≤ x.length := by
  simp only [minimizerSketch, windowSketch] at he
  rw [mem_windowSketchFn] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hm := argminLeft_lt (fun j => ord ((((x.drop i).take (w + k - 1)).drop j).take k)) w hw
  exact ⟨take_drop_sub _ _ _ _ _ (by omega), by omega⟩

theorem kmerSketch_key (k : Nat) (x : List Char) (e : List Char × Nat)
    (he : e ∈ (kmerSketch k).sketch x) : e.1 = (x.drop e.2).take k ∧ e.2 + k ≤ x.length := by
  simp only [kmerSketch, windowSketch] at he
  rw [mem_windowSketchFn] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨by simp, by omega⟩

/-! ## Context-free sketches: selection by the key's own letters -/

/-- `sel u = some ℓ`: a key of `ℓ` letters starts at the front of `u`.  The
answer is decided by those `ℓ` letters alone. -/
def PrefixDet (sel : List Char → Option Nat) : Prop :=
  ∀ (u v : List Char) (ℓ : Nat), sel u = some ℓ → ℓ ≤ u.length → ℓ ≤ v.length →
    v.take ℓ = u.take ℓ → sel v = some ℓ

/-- Every `L`-letter string contains a selected key. -/
def Hits (sel : List Char → Option Nat) (L : Nat) : Prop :=
  ∀ u : List Char, u.length = L → ∃ i ℓ, sel (u.drop i) = some ℓ ∧ i + ℓ ≤ L

def ctxSketchFn (sel : List Char → Option Nat) (x : List Char) : List (List Char × Nat) :=
  (List.range (x.length + 1)).filterMap fun i =>
    match sel (x.drop i) with
    | some ℓ => if i + ℓ ≤ x.length then some ((x.drop i).take ℓ, i) else none
    | none => none

theorem mem_ctxSketchFn (sel : List Char → Option Nat) (x : List Char) (e : List Char × Nat) :
    e ∈ ctxSketchFn sel x ↔ ∃ i ℓ, sel (x.drop i) = some ℓ ∧ i + ℓ ≤ x.length ∧
      e = ((x.drop i).take ℓ, i) := by
  unfold ctxSketchFn
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    cases hs : sel (x.drop i) with
    | none => rw [hs] at h; cases h
    | some ℓ =>
      rw [hs] at h
      simp only at h
      split at h
      · exact ⟨i, ℓ, hs, by assumption, (Option.some.inj h).symm⟩
      · cases h
  · rintro ⟨i, ℓ, hs, hl, rfl⟩
    refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
    rw [hs]
    simp [hl]

def ctxSketch (sel : List Char → Option Nat) (L : Nat) (hp : PrefixDet sel) (hh : Hits sel L) :
    SeedSketch (List Char) where
  L := L
  sketch := ctxSketchFn sel
  conserved := by
    intro x y b hb hx e he
    rw [mem_ctxSketchFn] at he ⊢
    obtain ⟨i, ℓ, hs, hl, rfl⟩ := he
    have hw : (y.drop (b + i)).take ℓ = (x.drop i).take ℓ := by
      conv => rhs; rw [← hx]
      rw [take_drop_sub _ _ _ _ _ hl]
    refine ⟨b + i, ℓ, hp _ _ ℓ hs (by simp; omega) (by simp; omega) hw, by omega, ?_⟩
    rw [hw]
  nonempty := by
    intro x hx h
    obtain ⟨i, ℓ, hs, hl⟩ := hh (x.take L) (by simp; omega)
    have hw : (x.drop i).take ℓ = ((x.take L).drop i).take ℓ := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
    have hs' := hp _ (x.drop i) ℓ hs (by simp; omega) (by simp; omega) hw
    have := (mem_ctxSketchFn sel x _).mpr ⟨i, ℓ, hs', by omega, rfl⟩
    rw [h] at this
    cases this

/-- Fixed-length context-free selection: the k-mer at the front, if `P` accepts it. -/
def fixedSel (k : Nat) (P : List Char → Bool) (u : List Char) : Option Nat :=
  if k ≤ u.length ∧ P (u.take k) = true then some k else none

theorem fixedSel_prefixDet (k : Nat) (P : List Char → Bool) : PrefixDet (fixedSel k P) := by
  intro u v ℓ hs hu hv hw
  unfold fixedSel at hs ⊢
  split at hs
  · rename_i h
    have hk : ℓ = k := (Option.some.inj hs).symm
    subst hk
    rw [if_pos ⟨hv, by rw [hw]; exact h.2⟩]
  · cases hs

/-- Variable-length context-free selection: the shortest prefix (of at most
`lmax` letters) in the dictionary `D`.  `D` can be built from genome counts
(longer keys where short ones are frequent); `PrefixDet` holds for any `D`. -/
def dictSel (D : List Char → Bool) (lmax : Nat) (u : List Char) : Option Nat :=
  (List.range (min lmax u.length + 1)).find? fun ℓ => D (u.take ℓ)

theorem dictSel_prefixDet (D : List Char → Bool) (lmax : Nat) : PrefixDet (dictSel D lmax) := by
  intro u v ℓ hs hu hv hw
  unfold dictSel at hs ⊢
  rw [List.find?_eq_some_iff_getElem] at hs ⊢
  obtain ⟨hD, i, hi, hgi, hbefore⟩ := hs
  simp only [List.getElem_range] at hgi
  subst hgi
  simp only [List.length_range] at hi
  refine ⟨?_, i, by simp; omega, by simp, ?_⟩
  · have : v.take i = u.take i := hw
    rw [this]; exact hD
  · intro j hj
    have hb := hbefore j (by omega)
    simp only [List.getElem_range] at hb ⊢
    have : v.take j = u.take j := by
      rw [← Nat.min_eq_left (Nat.le_of_lt hj), ← List.take_take, hw, List.take_take]
    rw [this]; exact hb

/-- Variable-length keys on a fixed-length selection: where `P` selects a
k-mer `z`, the key is extended by `ext z` letters (longer keys for frequent
k-mers, so their buckets split). -/
def extSel (k : Nat) (P : List Char → Bool) (ext : List Char → Nat) (u : List Char) : Option Nat :=
  if k ≤ u.length ∧ P (u.take k) = true then some (k + ext (u.take k)) else none

theorem extSel_prefixDet (k : Nat) (P : List Char → Bool) (ext : List Char → Nat) :
    PrefixDet (extSel k P ext) := by
  intro u v ℓ hs hu hv hw
  unfold extSel at hs ⊢
  split at hs
  · rename_i h
    have hl : ℓ = k + ext (u.take k) := (Option.some.inj hs).symm
    have hk : v.take k = u.take k := by
      rw [← Nat.min_eq_left (show k ≤ ℓ by omega), ← List.take_take, hw, List.take_take]
    rw [if_pos ⟨by omega, by rw [hk]; exact h.2⟩, hk, hl]
  · cases hs

/-- Extending keys by at most `emax` letters costs `emax` letters of guarantee. -/
theorem extSel_hits (k : Nat) (P : List Char → Bool) (ext : List Char → Nat) (L emax : Nat)
    (hh : Hits (fixedSel k P) L) (he : ∀ z, ext z ≤ emax) : Hits (extSel k P ext) (L + emax) := by
  intro u hu
  obtain ⟨i, ℓ, hs, hl⟩ := hh (u.take L) (by simp; omega)
  unfold fixedSel at hs
  split at hs
  · rename_i h
    have hk : ℓ = k := (Option.some.inj hs).symm
    subst hk
    have hw : (u.drop i).take ℓ = ((u.take L).drop i).take ℓ := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
    refine ⟨i, ℓ + ext ((u.drop i).take ℓ), ?_, ?_⟩
    · unfold extSel
      rw [if_pos ⟨by simp; omega, by rw [hw]; exact h.2⟩]
    · have := he ((u.drop i).take ℓ); omega
  · cases hs

/-! ## Closed syncmers: a k-mer whose least s-mer is its first or its last -/

def closedSyncmer (k s : Nat) (ord : List Char → Nat) (z : List Char) : Bool :=
  (List.range (k - s + 1)).all (fun j => decide (ord (z.take s) ≤ ord ((z.drop j).take s))) ||
  (List.range (k - s + 1)).all (fun j =>
    decide (ord ((z.drop (k - s)).take s) ≤ ord ((z.drop j).take s)))

/-- **Window guarantee.**  Every string of `2k - s - 1` letters contains a
closed syncmer (`s < k`), whatever the order on s-mers. -/
theorem closedSyncmer_hits (k s : Nat) (ord : List Char → Nat) (hs : s < k) :
    Hits (fixedSel k (closedSyncmer k s ord)) (2 * k - s - 1) := by
  intro u hu
  let f := fun j => ord ((u.drop j).take s)
  let J := argminLeft f (2 * (k - s))
  have hJ : J < 2 * (k - s) := argminLeft_lt f _ (by omega)
  have hmin : ∀ i, i < 2 * (k - s) → f J ≤ f i := argminLeft_le f _
  -- the s-mer at offset j of the k-mer at i is the s-mer of u at i + j
  have sub : ∀ i j, j + s ≤ k → (((u.drop i).take k).drop j).take s = (u.drop (i + j)).take s :=
    fun i j h => take_drop_sub _ _ _ _ _ h
  by_cases hc : J < k - s
  · refine ⟨J, k, ?_, by omega⟩
    unfold fixedSel
    rw [if_pos]
    refine ⟨by simp; omega, ?_⟩
    unfold closedSyncmer
    rw [Bool.or_eq_true]
    left
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have h0 : ((u.drop J).take k).take s = (u.drop J).take s := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [h0, sub J j (by omega)]
    exact decide_eq_true (hmin (J + j) (by omega))
  · refine ⟨J - (k - s), k, ?_, by omega⟩
    unfold fixedSel
    rw [if_pos]
    refine ⟨by simp; omega, ?_⟩
    unfold closedSyncmer
    rw [Bool.or_eq_true]
    right
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [sub _ (k - s) (by omega), sub _ j (by omega)]
    have : J - (k - s) + (k - s) = J := by omega
    rw [this]
    exact decide_eq_true (hmin (J - (k - s) + j) (by omega))

/-- Closed `(k, s)` syncmers as a seed sketch with `L = 2k - s - 1`. -/
def syncmerSketch (k s : Nat) (ord : List Char → Nat) (hs : s < k) : SeedSketch (List Char) :=
  ctxSketch (fixedSel k (closedSyncmer k s ord)) (2 * k - s - 1)
    (fixedSel_prefixDet _ _) (closedSyncmer_hits k s ord hs)

/-- Closed syncmers with keys extended by `ext ≤ emax` letters:
`L = 2k - s - 1 + emax`. -/
def syncmerExtSketch (k s : Nat) (ord : List Char → Nat) (hs : s < k) (ext : List Char → Nat)
    (emax : Nat) (he : ∀ z, ext z ≤ emax) : SeedSketch (List Char) :=
  ctxSketch (extSel k (closedSyncmer k s ord) ext) (2 * k - s - 1 + emax)
    (extSel_prefixDet _ _ _) (extSel_hits _ _ _ _ _ (closedSyncmer_hits k s ord hs) he)

/-- A context-free key is the letters at its offset. -/
theorem ctxSketch_key (sel : List Char → Option Nat) (x : List Char) (e : List Char × Nat)
    (he : e ∈ ctxSketchFn sel x) : ∃ ℓ, e.1 = (x.drop e.2).take ℓ ∧ e.2 + ℓ ≤ x.length := by
  rw [mem_ctxSketchFn] at he
  obtain ⟨i, ℓ, -, hl, rfl⟩ := he
  exact ⟨ℓ, rfl, hl⟩

end MapSpec

#print axioms MapSpec.SeedSketch.anchored
#print axioms MapSpec.minimizerSketch_key
#print axioms MapSpec.dictSel_prefixDet
#print axioms MapSpec.closedSyncmer_hits
#print axioms MapSpec.ctxSketch_key
#print axioms MapSpec.extSel_prefixDet
#print axioms MapSpec.extSel_hits
