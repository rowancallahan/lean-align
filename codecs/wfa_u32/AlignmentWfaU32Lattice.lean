import AlignmentWfaOffLoop

/-!
# Lattice property of the offsets-only run

If the three penalties `pe, po, px` share a factor `g`, the run with the
penalties divided by `g` visits exactly the levels `0, g, 2g, …` of the
original run: every original level whose index is not a multiple of `g`
is empty (each of its sources is an empty or absent level), and the
corner is found at original level `g * k` iff the divided run finds it
at level `k`.  `wfaRunO_lattice` states this for `wfaRunO`.

The history relation `HRel g len i hG h'` says: the original window
`hG` at phase `i` (`0 ≤ i < g`) holds the divided window `h'` at the
indices `i, i + g, i + 2g, …` and only absent or empty levels elsewhere.
The original loop stutters through phases `0, 1, …, g - 1` (building
empty levels) and then builds the divided loop's next level, returning
to phase `0`.
-/

namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- gcd on scalars
-- ══════════════════════════════════════════════════════════════════

def gcdGo : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | f + 1, a, b => if b = 0 then a else gcdGo f b (a % b)

/-- Euclid on scalars (`Nat.gcd` at runtime converts to GMP). -/
def gcdU (a b : Nat) : Nat := gcdGo (a + b + 1) a b

theorem gcdGo_eq : ∀ (f a b : Nat), b < f → gcdGo f a b = Nat.gcd a b := by
  intro f
  induction f with
  | zero => intro a b h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro a b h
    simp only [gcdGo]
    split
    · next hb => subst hb; simp
    · next hb =>
      rw [ih b (a % b) (by have := Nat.mod_lt a (Nat.pos_of_ne_zero hb); omega)]
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]

theorem gcdU_eq (a b : Nat) : gcdU a b = Nat.gcd a b :=
  gcdGo_eq _ a b (by omega)

-- ══════════════════════════════════════════════════════════════════
-- The run with explicit penalties and fuel
-- ══════════════════════════════════════════════════════════════════

/-- The offsets-only run with explicit penalties and fuel. -/
def wfaRunOP (m n : Nat) (xs ys : List Char) (pe po px fuel : Nat) : Option Nat :=
  let len := m + n + 1
  let lv0 := seedO m len xs ys
  if cornerO m n lv0 then some 0
  else wfaLoopO m n xs ys len pe po px fuel [lv0] 1

-- ══════════════════════════════════════════════════════════════════
-- Empty levels
-- ══════════════════════════════════════════════════════════════════

def emptyO (len : Nat) : OLevelW :=
  ⟨List.replicate len none, List.replicate len none, List.replicate len none⟩

theorem mulS (g q : Nat) : g * (q + 1) = g * q + g := Nat.mul_succ g q

theorem mapFrom_replicate (f : Nat → Nat → Option Nat) :
    ∀ (len t : Nat), mapFrom f t (List.replicate len none) = List.replicate len none := by
  intro len
  induction len with
  | zero => intro t; rfl
  | succ l ih => intro t; simp [mapFrom, List.replicate_succ, ih]

theorem shiftUpO_replicate (len : Nat) (h : 1 ≤ len) :
    shiftUpO (List.replicate len none) = List.replicate len none := by
  obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩
  simp [shiftUpO, List.replicate_succ]

theorem shiftDownO_replicate (len : Nat) (h : 1 ≤ len) :
    shiftDownO (List.replicate len none) = List.replicate len none := by
  obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩
  simp only [shiftDownO, List.drop_replicate, Nat.add_sub_cancel]
  exact List.replicate_succ'.symm

theorem nextLevelO_empty (m n : Nat) (xs ys : List Char) (len : Nat) (hlen : 1 ≤ len)
    (pe po px : Nat) (hist : List OLevelW)
    (h1 : frontAtO len hist pe (·.xf) = List.replicate len none)
    (h2 : frontAtO len hist po (·.mf) = List.replicate len none)
    (h3 : frontAtO len hist pe (·.yf) = List.replicate len none)
    (h4 : frontAtO len hist px (·.mf) = List.replicate len none) :
    nextLevelO m n xs ys len pe po px hist = emptyO len := by
  simp only [nextLevelO, h1, h2, h3, h4, mapFrom_replicate, shiftUpO_replicate len hlen,
    shiftDownO_replicate len hlen, List.zipWith_replicate', betterO, emptyO]

theorem cornerO_empty (m n len : Nat) : cornerO m n (emptyO len) = false := by
  simp only [cornerO, emptyO, List.getElem?_replicate]
  split <;> simp

theorem frontAtO_of_empty (len : Nat) (hist : List OLevelW) (d : Nat)
    (sel : OLevelW → OFrontW) (hsel : sel (emptyO len) = List.replicate len none)
    (h : hist[d - 1]? = none ∨ hist[d - 1]? = some (emptyO len)) :
    frontAtO len hist d sel = List.replicate len none := by
  simp only [frontAtO]
  rcases h with h | h <;> simp [h, hsel]

-- ══════════════════════════════════════════════════════════════════
-- The history relation
-- ══════════════════════════════════════════════════════════════════

/-- `hG` (original window, phase `i`) holds `h'` (divided window) at the
indices `i + g * q` and only absent or empty levels at other indices. -/
def HRel (g len i : Nat) (hG h' : List OLevelW) : Prop :=
  (∀ q j, j = i + g * q → hG[j]? = h'[q]?) ∧
  (∀ j, (∀ q, j ≠ i + g * q) → hG[j]? = none ∨ hG[j]? = some (emptyO len))

theorem hrel_src_empty (g len i : Nat) (hG h' : List OLevelW) (hr : HRel g len i hG h')
    (hi : i + 1 < g) (d : Nat) (hd : 1 ≤ d) :
    hG[g * d - 1]? = none ∨ hG[g * d - 1]? = some (emptyO len) := by
  apply hr.2
  intro q hq
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [mulS] at hq
  rcases Nat.lt_or_ge q (d' + 1) with hlt | hge
  · have := Nat.mul_le_mul_left g (Nat.le_of_lt_succ hlt)
    omega
  · have := Nat.mul_le_mul_left g hge
    rw [mulS] at this
    omega

theorem hrel_src_real (g len : Nat) (hG h' : List OLevelW) (hr : HRel g len (g - 1) hG h')
    (hg : 0 < g) (d : Nat) (hd : 1 ≤ d) : hG[g * d - 1]? = h'[d - 1]? := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply hr.1 d'
  rw [mulS]
  generalize g * d' = x
  omega

theorem frontAtO_real (g len : Nat) (hG h' : List OLevelW) (hr : HRel g len (g - 1) hG h')
    (hg : 0 < g) (d : Nat) (hd : 1 ≤ d) (sel : OLevelW → OFrontW) :
    frontAtO len hG (g * d) sel = frontAtO len h' d sel := by
  simp only [frontAtO, hrel_src_real g len hG h' hr hg d hd]

/-- Phase `i < g - 1`: the original level built from `hG` is empty. -/
theorem nextLevelO_stutter (m n : Nat) (xs ys : List Char) (len : Nat) (hlen : 1 ≤ len)
    (g pe' po' px' : Nat) (hpe : 1 ≤ pe') (hpo : 1 ≤ po') (hpx : 1 ≤ px')
    (i : Nat) (hi : i + 1 < g) (hG h' : List OLevelW) (hr : HRel g len i hG h') :
    nextLevelO m n xs ys len (g * pe') (g * po') (g * px') hG = emptyO len :=
  nextLevelO_empty m n xs ys len hlen _ _ _ hG
    (frontAtO_of_empty len hG _ (·.xf) rfl (hrel_src_empty g len i hG h' hr hi pe' hpe))
    (frontAtO_of_empty len hG _ (·.mf) rfl (hrel_src_empty g len i hG h' hr hi po' hpo))
    (frontAtO_of_empty len hG _ (·.yf) rfl (hrel_src_empty g len i hG h' hr hi pe' hpe))
    (frontAtO_of_empty len hG _ (·.mf) rfl (hrel_src_empty g len i hG h' hr hi px' hpx))

/-- Phase `g - 1`: the original level built from `hG` is the divided level built from `h'`. -/
theorem nextLevelO_real (m n : Nat) (xs ys : List Char) (len : Nat)
    (g : Nat) (hg : 0 < g) (pe' po' px' : Nat) (hpe : 1 ≤ pe') (hpo : 1 ≤ po') (hpx : 1 ≤ px')
    (hG h' : List OLevelW) (hr : HRel g len (g - 1) hG h') :
    nextLevelO m n xs ys len (g * pe') (g * po') (g * px') hG =
      nextLevelO m n xs ys len pe' po' px' h' := by
  simp only [nextLevelO, frontAtO_real g len hG h' hr hg pe' hpe,
    frontAtO_real g len hG h' hr hg po' hpo, frontAtO_real g len hG h' hr hg px' hpx]

theorem hrel_cons_empty (g len i W' : Nat) (hG h' : List OLevelW) (hr : HRel g len i hG h')
    (hi : i + 1 < g) (hl : h'.length ≤ W') :
    HRel g len (i + 1) ((emptyO len :: hG).take (g * W')) h' := by
  refine ⟨?_, ?_⟩
  · intro q j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [List.getElem?_take]
    split
    · next hlt =>
      rw [List.getElem?_cons_succ]
      exact hr.1 q j' (by omega)
    · next hge =>
      rcases Nat.lt_or_ge q W' with hq | hq
      · exfalso
        have := Nat.mul_le_mul_left g (show q + 1 ≤ W' from hq)
        rw [mulS] at this
        omega
      · rw [List.getElem?_eq_none (by omega)]
  · intro j hj
    rw [List.getElem?_take]
    split
    · next hlt =>
      cases j with
      | zero => right; rfl
      | succ j' =>
        rw [List.getElem?_cons_succ]
        exact hr.2 j' (fun q hq => hj q (by omega))
    · next _ => left; rfl

theorem hrel_cons_real (g len W' : Nat) (hG h' : List OLevelW) (hr : HRel g len (g - 1) hG h')
    (hg : 0 < g) (hW : 1 ≤ W') (lv : OLevelW) :
    HRel g len 0 ((lv :: hG).take (g * W')) ((lv :: h').take W') := by
  have hgW : g ≤ g * W' := by
    have := Nat.mul_le_mul_left g hW; rwa [Nat.mul_one] at this
  refine ⟨?_, ?_⟩
  · intro q j hj
    rw [List.getElem?_take, List.getElem?_take]
    cases q with
    | zero =>
      have hj0 : j = 0 := by rw [Nat.mul_zero] at hj; omega
      subst hj0
      rw [if_pos (show 0 < g * W' by omega), if_pos (show 0 < W' by omega)]
      rfl
    | succ q' =>
      rw [mulS] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rcases Nat.lt_or_ge (q' + 1) W' with hq | hq
      · have := Nat.mul_le_mul_left g (show q' + 1 + 1 ≤ W' from hq)
        rw [mulS, mulS] at this
        rw [if_pos (show j' + 1 < g * W' by omega), if_pos hq,
          List.getElem?_cons_succ, List.getElem?_cons_succ]
        exact hr.1 q' j' (by omega)
      · have := Nat.mul_le_mul_left g hq
        rw [mulS] at this
        rw [if_neg (show ¬ j' + 1 < g * W' by omega), if_neg (show ¬ q' + 1 < W' by omega)]
  · intro j hj
    rw [List.getElem?_take]
    split
    · next hlt =>
      cases j with
      | zero => exact (hj 0 (by simp)).elim
      | succ j' =>
        rw [List.getElem?_cons_succ]
        refine hr.2 j' (fun q hq => hj (q + 1) ?_)
        rw [mulS]; omega
    · next _ => left; rfl

theorem hrel_init (g len : Nat) (hg : 0 < g) (lv : OLevelW) : HRel g len 0 [lv] [lv] := by
  refine ⟨?_, ?_⟩
  · intro q j hj
    cases q with
    | zero =>
      rw [Nat.mul_zero] at hj
      have hj0 : j = 0 := by omega
      subst hj0; rfl
    | succ q' =>
      rw [mulS] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rfl
  · intro j hj
    cases j with
    | zero => exact (hj 0 (by simp)).elim
    | succ j' => left; rfl

-- ══════════════════════════════════════════════════════════════════
-- The loop
-- ══════════════════════════════════════════════════════════════════

theorem max_mul (g a b : Nat) : max (g * a) (g * b) = g * max a b := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.mul_le_mul_left g h)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.mul_le_mul_left g h)]

theorem max_mul3 (g a b c : Nat) :
    max (g * a) (max (g * b) (g * c)) = g * max a (max b c) := by
  rw [max_mul, max_mul]

/-- Fuel monotonicity: a returned level stays returned with more fuel. -/
theorem wfaLoopO_fuel_mono (m n : Nat) (xs ys : List Char) (len pe po px : Nat) :
    ∀ (f f' : Nat) (hist : List OLevelW) (p r : Nat), f ≤ f' →
      wfaLoopO m n xs ys len pe po px f hist p = some r →
      wfaLoopO m n xs ys len pe po px f' hist p = some r := by
  intro f
  induction f with
  | zero => intro f' hist p r _ h; simp [wfaLoopO] at h
  | succ f ih =>
    intro f' hist p r hf h
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    simp only [wfaLoopO] at h ⊢
    split at h
    · next hc => rw [if_pos hc]; exact h
    · next hc => rw [if_neg hc]; exact ih f'' _ _ r (by omega) h

/-- From phase `i` with `i + c + 1 = g`, `c` original steps build empty
levels and reach phase `g - 1`. -/
theorem loop_stutter (m n : Nat) (xs ys : List Char) (len : Nat) (hlen : 1 ≤ len)
    (g pe' po' px' : Nat) (hpe : 1 ≤ pe') (hpo : 1 ≤ po') (hpx : 1 ≤ px')
    (h' : List OLevelW) (hl : h'.length ≤ max pe' (max po' px')) :
    ∀ (c i : Nat) (hG : List OLevelW) (fuel p : Nat), i + c + 1 = g → HRel g len i hG h' →
      ∃ hG', HRel g len (g - 1) hG' h' ∧
        wfaLoopO m n xs ys len (g * pe') (g * po') (g * px') (fuel + c) hG p =
          wfaLoopO m n xs ys len (g * pe') (g * po') (g * px') fuel hG' (p + c) := by
  intro c
  induction c with
  | zero =>
    intro i hG fuel p hc hr
    refine ⟨hG, ?_, rfl⟩
    rw [show g - 1 = i by omega]; exact hr
  | succ c ih =>
    intro i hG fuel p hc hr
    have hW := max_mul3 g pe' po' px'
    have hlv := nextLevelO_stutter m n xs ys len hlen g pe' po' px' hpe hpo hpx i
      (by omega) hG h' hr
    obtain ⟨hG', hr', heq⟩ := ih (i + 1) ((emptyO len :: hG).take (g * max pe' (max po' px')))
      fuel (p + 1) (by omega) (hrel_cons_empty g len i _ hG h' hr (by omega) hl)
    refine ⟨hG', hr', ?_⟩
    rw [show fuel + (c + 1) = fuel + c + 1 by omega, show p + (c + 1) = p + 1 + c by omega,
      ← heq]
    simp only [wfaLoopO, hlv, cornerO_empty, Bool.false_eq_true, ↓reduceIte, hW]

/-- The divided loop at position `k + 1` returning `r` means the original
loop at position `g * k + 1` with `g` times the fuel returns `g * r`. -/
theorem loop_lattice (m n : Nat) (xs ys : List Char) (len : Nat) (hlen : 1 ≤ len)
    (g : Nat) (hg : 0 < g) (pe' po' px' : Nat) (hpe : 1 ≤ pe') (hpo : 1 ≤ po') (hpx : 1 ≤ px') :
    ∀ (fuel' k : Nat) (hG h' : List OLevelW) (r : Nat),
      HRel g len 0 hG h' → h'.length ≤ max pe' (max po' px') →
      wfaLoopO m n xs ys len pe' po' px' fuel' h' (k + 1) = some r →
      wfaLoopO m n xs ys len (g * pe') (g * po') (g * px') (g * fuel') hG (g * k + 1) =
        some (g * r) := by
  intro fuel'
  induction fuel' with
  | zero => intro k hG h' r _ _ h; simp [wfaLoopO] at h
  | succ fuel' ih =>
    intro k hG h' r hr hl h
    have hW := max_mul3 g pe' po' px'
    obtain ⟨hG', hr', heq⟩ := loop_stutter m n xs ys len hlen g pe' po' px' hpe hpo hpx h' hl
      (g - 1) 0 hG (g * fuel' + 1) (g * k + 1) (by omega) hr
    rw [show g * (fuel' + 1) = g * fuel' + 1 + (g - 1) by rw [mulS]; omega, heq,
      show g * k + 1 + (g - 1) = g * (k + 1) by rw [mulS]; omega]
    have hlv := nextLevelO_real m n xs ys len g hg pe' po' px' hpe hpo hpx hG' h' hr'
    simp only [wfaLoopO] at h ⊢
    rw [hlv, hW]
    by_cases hc : cornerO m n (nextLevelO m n xs ys len pe' po' px' h') = true
    · rw [if_pos hc] at h ⊢
      cases h; rfl
    · rw [if_neg hc] at h ⊢
      exact ih (k + 1) _ _ r
        (hrel_cons_real g len _ hG' h' hr' hg (Nat.le_trans hpe (Nat.le_max_left _ _)) _)
        (by rw [List.length_take]; exact Nat.min_le_left _ _)
        h

-- ══════════════════════════════════════════════════════════════════
-- The run
-- ══════════════════════════════════════════════════════════════════

theorem wfaRunO_lattice (sc : Scoring) (xs ys : List Char) (g : Nat) (hg : 0 < g)
    (hpe : g ∣ (wfaPe sc).toNat) (hpo : g ∣ (wfaPo sc).toNat) (hpx : g ∣ (wfaPx sc).toNat)
    (hpe1 : 1 ≤ (wfaPe sc).toNat) (hpo1 : 1 ≤ (wfaPo sc).toNat) (hpx1 : 1 ≤ (wfaPx sc).toNat)
    (k : Nat)
    (h : wfaRunOP xs.length ys.length xs ys ((wfaPe sc).toNat / g) ((wfaPo sc).toNat / g)
      ((wfaPx sc).toNat / g) ((xs.length + ys.length + 2) * ((wfaPo sc).toNat / g)) = some k) :
    wfaRunO sc xs ys = some (g * k) := by
  obtain ⟨pe', hpe'⟩ := hpe
  obtain ⟨po', hpo'⟩ := hpo
  obtain ⟨px', hpx'⟩ := hpx
  rw [hpe', hpo', hpx', Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg,
    Nat.mul_div_cancel_left _ hg] at h
  rw [hpe'] at hpe1
  rw [hpo'] at hpo1
  rw [hpx'] at hpx1
  have hpe1' : 1 ≤ pe' := Nat.pos_of_ne_zero (by rintro rfl; simp at hpe1)
  have hpo1' : 1 ≤ po' := Nat.pos_of_ne_zero (by rintro rfl; simp at hpo1)
  have hpx1' : 1 ≤ px' := Nat.pos_of_ne_zero (by rintro rfl; simp at hpx1)
  simp only [wfaRunOP] at h
  simp only [wfaRunO]
  rw [hpe', hpo', hpx']
  by_cases hc : cornerO xs.length ys.length
      (seedO xs.length (xs.length + ys.length + 1) xs ys) = true
  · rw [if_pos hc] at h ⊢
    cases h; simp
  · rw [if_neg hc] at h ⊢
    have hloop := loop_lattice xs.length ys.length xs ys (xs.length + ys.length + 1)
      (by omega) g hg pe' po' px' hpe1' hpo1' hpx1'
      ((xs.length + ys.length + 2) * po') 0 _ _ k (hrel_init g _ hg _)
      (Nat.le_trans hpe1' (Nat.le_max_left _ _)) h
    rw [Nat.mul_zero, Nat.zero_add] at hloop
    exact wfaLoopO_fuel_mono _ _ _ _ _ _ _ _ _ _ _ _ _
      (by rw [Nat.mul_left_comm]; omega) hloop

#print axioms gcdU_eq
#print axioms wfaRunO_lattice

end AlignmentSpec.U32Proof
