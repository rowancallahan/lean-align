import AlignmentCigarCheck

/-!
# A faster run checker, proven equal to `checkRuns`

`checkRunsFast3` checks a run-length walk one run at a time: bounds decided
once per run, diagonal runs scanned by an unboxed `USize` loop counting
mismatches, gap runs by index arithmetic.  `checkRunsFast3_eq` proves it
returns exactly what the proven `checkRuns` returns, so every kernel that
certifies its traceback with `checkRuns` can use it unchanged.

Written by a subagent (probe idea 3, 2026-09-11); measured share of
`checkRuns` in the fast probe at 1 kb / 1 %: 59 % of the time before,
17 % after.  Standard axioms only (see the `#print axioms` lines).
-/
namespace AlignmentSpec

def diagMis3 (xa ya : Array Char) : (k i j mis : Nat) →
    i + k ≤ xa.size → j + k ≤ ya.size → Nat
  | 0, _, _, mis, _, _ => mis
  | k + 1, i, j, mis, hx, hy =>
    diagMis3 xa ya k (i + 1) (j + 1)
      (if xa[i]'(by omega) = ya[j]'(by omega) then mis else mis + 1)
      (by omega) (by omega)

@[inline] def diagRunScore3 (sc : Scoring) (k mis : Nat) : Int :=
  ((k : Int) - mis) * sc.matchScore + (mis : Int) * sc.mismatchScore

theorem two_pow_32_le_usize3 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  exact this

/-- `USize` inner loop for a diagonal run: positions `p`, `q`, remaining
`k`, mismatch accumulator `mis`.  All arithmetic is unboxed machine
arithmetic; the bounds and the `< 2^32` guards make every `toNat` exact. -/
def diagMisU3 (xa ya : Array Char) (p q k mis : USize)
    (hp : p.toNat + k.toNat ≤ xa.size) (hq : q.toNat + k.toNat ≤ ya.size)
    (hm : mis.toNat + k.toNat ≤ xa.size) (hs : xa.size < 2 ^ 32) (hs2 : ya.size < 2 ^ 32) : USize :=
  if hk : k = 0 then mis else
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h | h
      · exact absurd (USize.toNat_inj.mp (h.trans USize.toNat_zero.symm)) hk
      · exact h
    have hb := two_pow_32_le_usize3
    have hp1 : (p + 1).toNat = p.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have hk1' : (k - 1).toNat = k.toNat - 1 := by
      rw [USize.toNat_sub_of_le]; · rw [USize.toNat_one]
      rw [USize.le_iff_toNat_le, USize.toNat_one]; exact hk1
    have hm1 : (mis + 1).toNat = mis.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    let c := if xa.uget p (by omega) = ya.uget q (by omega) then mis else mis + 1
    have hc : c.toNat + (k - 1).toNat ≤ xa.size := by
      simp only [c]; split
      · omega
      · rw [hm1]; omega
    diagMisU3 xa ya (p + 1) (q + 1) (k - 1) c (by omega) (by omega) hc hs hs2
termination_by k.toNat
decreasing_by
  rw [USize.toNat_sub_of_le]
  · rw [USize.toNat_one]; omega
  · rw [USize.le_iff_toNat_le, USize.toNat_one]; exact hk1

theorem diagMis3_succ (xa ya : Array Char) (k i j mis : Nat) (hk : 0 < k) hx hy :
    diagMis3 xa ya k i j mis hx hy =
      diagMis3 xa ya (k - 1) (i + 1) (j + 1)
        (if xa[i]'(by omega) = ya[j]'(by omega) then mis else mis + 1) (by omega) (by omega) := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem diagMis3_congr (xa ya : Array Char) {k k' i i' j j' mis mis' : Nat}
    (hk : k = k') (hi : i = i') (hj : j = j') (hm : mis = mis') hx hy hx' hy' :
    diagMis3 xa ya k i j mis hx hy = diagMis3 xa ya k' i' j' mis' hx' hy' := by
  subst hk hi hj hm; rfl

theorem diagMisU3_toNat (xa ya : Array Char) (n : Nat) :
    ∀ (p q k mis : USize) hp hq hm hs hs2, k.toNat = n →
      (diagMisU3 xa ya p q k mis hp hq hm hs hs2).toNat =
        diagMis3 xa ya k.toNat p.toNat q.toNat mis.toNat hp hq := by
  induction n with
  | zero =>
    intro p q k mis hp hq hm hs hs2 hn
    have hk : k = 0 := USize.toNat_inj.mp (hn.trans USize.toNat_zero.symm)
    subst hk
    rw [diagMisU3]; simp [diagMis3]
  | succ n ih =>
    intro p q k mis hp hq hm hs hs2 hn
    have hk : ¬ k = 0 := by
      intro h; subst h; simp at hn
    rw [diagMisU3, dif_neg hk]
    have hb := two_pow_32_le_usize3
    have hp1 : (p + 1).toNat = p.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    have hk1' : (k - 1).toNat = n := by
      rw [USize.toNat_sub_of_le]; · rw [USize.toNat_one]; omega
      rw [USize.le_iff_toNat_le, USize.toNat_one]; omega
    have hm1 : (mis + 1).toNat = mis.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    rw [ih _ _ _ _ _ _ _ _ _ hk1']
    rw [diagMis3_succ xa ya k.toNat p.toNat q.toNat mis.toNat (by omega)]
    refine diagMis3_congr xa ya (by omega) hp1 hq1 ?_ _ _ _ _
    simp only [Array.uget]
    split <;> simp [hm1]

/-- Mismatch count of a diagonal run of length `k + 1`: the `USize` loop
when both arrays are shorter than `2^32` (always, for pa-bench inputs),
the `Nat` loop otherwise. -/
@[inline] def diagMisFast3 (xa ya : Array Char) (k i j : Nat)
    (h : i + (k + 1) ≤ xa.size ∧ j + (k + 1) ≤ ya.size) : Nat :=
  if hs : xa.size < 2 ^ 32 ∧ ya.size < 2 ^ 32 then
    (diagMisU3 xa ya (USize.ofNat i) (USize.ofNat j) (USize.ofNat (k + 1)) 0
      (by rw [USize.toNat_ofNat_of_lt_32 (by have := h.1; have := hs.1; omega),
              USize.toNat_ofNat_of_lt_32 (by have := h.1; have := hs.1; omega)]; exact h.1)
      (by rw [USize.toNat_ofNat_of_lt_32 (by have := h.2; have := hs.2; omega),
              USize.toNat_ofNat_of_lt_32 (by have := h.1; have := hs.1; omega)]; exact h.2)
      (by rw [USize.toNat_zero, USize.toNat_ofNat_of_lt_32 (by have := h.1; have := hs.1; omega)]
          have := h.1; omega)
      hs.1 hs.2).toNat
  else diagMis3 xa ya (k + 1) i j 0 h.1 h.2

theorem diagMisFast3_eq (xa ya : Array Char) (k i j : Nat)
    (h : i + (k + 1) ≤ xa.size ∧ j + (k + 1) ≤ ya.size) :
    diagMisFast3 xa ya k i j h = diagMis3 xa ya (k + 1) i j 0 h.1 h.2 := by
  unfold diagMisFast3
  split
  · rename_i hs
    have h1 := h.1
    have hs1 := hs.1
    rw [diagMisU3_toNat xa ya (k + 1)]
    · exact diagMis3_congr xa ya (USize.toNat_ofNat_of_lt_32 (by omega))
        (USize.toNat_ofNat_of_lt_32 (by omega)) (USize.toNat_ofNat_of_lt_32 (by omega))
        USize.toNat_zero _ _ _ _
    · exact USize.toNat_ofNat_of_lt_32 (by omega)
  · rfl

theorem diagMis3_acc (xa ya : Array Char) (k : Nat) :
    ∀ i j mis hx hy, diagMis3 xa ya k i j mis hx hy = mis + diagMis3 xa ya k i j 0 hx hy := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro i j mis hx hy
    simp only [diagMis3]
    rw [ih (i + 1) (j + 1) (if xa[i] = ya[j] then mis else mis + 1),
        ih (i + 1) (j + 1) (if xa[i] = ya[j] then 0 else 1)]
    split <;> omega

theorem checkRepeatFast_diag3 (sc : Scoring) (xa ya : Array Char) (k : Nat) :
    ∀ i j prev acc, checkRepeatFast sc xa ya .diag (k + 1) i j prev acc =
      if h : i + (k + 1) ≤ xa.size ∧ j + (k + 1) ≤ ya.size then
        some ⟨i + (k + 1), j + (k + 1), some .diag,
              acc + diagRunScore3 sc (k + 1) (diagMis3 xa ya (k + 1) i j 0 h.1 h.2)⟩
      else none := by
  induction k with
  | zero =>
    intro i j prev acc
    by_cases hb : i + (0 + 1) ≤ xa.size ∧ j + (0 + 1) ≤ ya.size
    · have hi : i < xa.size := by omega
      have hj : j < ya.size := by omega
      simp only [checkRepeatFast, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj,
        dif_pos hb, diagMis3, diagRunScore3, diagCost, Option.some.injEq, WalkCursor.mk.injEq,
        true_and]
      split <;> simp <;> omega
    · rw [dif_neg hb]
      simp only [checkRepeatFast]
      cases hx : xa[i]? <;> cases hy : ya[j]? <;> simp
      rw [Array.getElem?_eq_some_iff] at hx hy
      obtain ⟨hi, _⟩ := hx
      obtain ⟨hj, _⟩ := hy
      omega
  | succ k ih =>
    intro i j prev acc
    rw [checkRepeatFast]
    by_cases hb : i + (k + 1 + 1) ≤ xa.size ∧ j + (k + 1 + 1) ≤ ya.size
    · have hi : i < xa.size := by omega
      have hj : j < ya.size := by omega
      have hb' : i + 1 + (k + 1) ≤ xa.size ∧ j + 1 + (k + 1) ≤ ya.size := by omega
      rw [dif_pos hb]
      simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj]
      rw [ih, dif_pos hb']
      simp only [Option.some.injEq, WalkCursor.mk.injEq, true_and]
      refine ⟨by omega, by omega, ?_⟩
      rw [show diagMis3 xa ya (k + 1 + 1) i j 0 hb.1 hb.2 =
          diagMis3 xa ya (k + 1) (i + 1) (j + 1) (if xa[i] = ya[j] then 0 else 0 + 1)
            (by omega) (by omega) from rfl]
      rw [diagMis3_acc xa ya (k + 1) (i + 1) (j + 1) (if xa[i] = ya[j] then 0 else 0 + 1)]
      generalize diagMis3 xa ya (k + 1) (i + 1) (j + 1) 0 _ _ = r
      simp only [diagRunScore3, diagCost]
      split
      · simp only [Nat.zero_add]
        push_cast
        simp only [Int.add_mul, Int.sub_mul, Int.one_mul]
        omega
      · push_cast
        simp only [Int.add_mul, Int.sub_mul, Int.one_mul]
        omega
    · rw [dif_neg hb]
      cases hx : xa[i]? <;> cases hy : ya[j]? <;> simp only []
      rw [Array.getElem?_eq_some_iff] at hx hy
      obtain ⟨hi, _⟩ := hx
      obtain ⟨hj, _⟩ := hy
      rw [ih]
      have : ¬ (i + 1 + (k + 1) ≤ xa.size ∧ j + 1 + (k + 1) ≤ ya.size) := by omega
      rw [dif_neg this]

theorem checkRepeatFast_gapX3 (sc : Scoring) (xa ya : Array Char) (k : Nat) :
    ∀ i j prev acc, checkRepeatFast sc xa ya .gapX (k + 1) i j prev acc =
      if j + (k + 1) ≤ ya.size then
        some ⟨i, j + (k + 1), some .gapX, acc + gapXCost sc prev + (k : Int) * sc.gapExtend⟩
      else none := by
  induction k with
  | zero =>
    intro i j prev acc
    simp only [checkRepeatFast]
    cases hy : ya[j]? <;> simp
    · rw [Array.getElem?_eq_none_iff] at hy; omega
    · rw [Array.getElem?_eq_some_iff] at hy; obtain ⟨hj, -⟩ := hy; omega
  | succ k ih =>
    intro i j prev acc
    rw [checkRepeatFast]
    cases hy : ya[j]? <;> simp only []
    · rw [Array.getElem?_eq_none_iff] at hy
      have : ¬ j + (k + 1 + 1) ≤ ya.size := by omega
      rw [if_neg this]
    · rw [Array.getElem?_eq_some_iff] at hy
      obtain ⟨hj, -⟩ := hy
      rw [ih]
      by_cases hb : j + (k + 1 + 1) ≤ ya.size
      · have hb' : j + 1 + (k + 1) ≤ ya.size := by omega
        simp only [if_pos hb, if_pos hb', Option.some.injEq, WalkCursor.mk.injEq, true_and]
        refine ⟨by omega, ?_⟩
        simp only [gapXCost]
        push_cast
        simp only [Int.add_mul, Int.one_mul]
        split <;> omega
      · have hb' : ¬ j + 1 + (k + 1) ≤ ya.size := by omega
        simp only [if_neg hb, if_neg hb']


theorem checkRepeatFast_gapY3 (sc : Scoring) (xa ya : Array Char) (k : Nat) :
    ∀ i j prev acc, checkRepeatFast sc xa ya .gapY (k + 1) i j prev acc =
      if i + (k + 1) ≤ xa.size then
        some ⟨i + (k + 1), j, some .gapY, acc + gapYCost sc prev + (k : Int) * sc.gapExtend⟩
      else none := by
  induction k with
  | zero =>
    intro i j prev acc
    simp only [checkRepeatFast]
    cases hx : xa[i]? <;> simp
    · rw [Array.getElem?_eq_none_iff] at hx; omega
    · rw [Array.getElem?_eq_some_iff] at hx; obtain ⟨hi, -⟩ := hx; omega
  | succ k ih =>
    intro i j prev acc
    rw [checkRepeatFast]
    cases hx : xa[i]? <;> simp only []
    · rw [Array.getElem?_eq_none_iff] at hx
      have : ¬ i + (k + 1 + 1) ≤ xa.size := by omega
      rw [if_neg this]
    · rw [Array.getElem?_eq_some_iff] at hx
      obtain ⟨hi, -⟩ := hx
      rw [ih]
      by_cases hb : i + (k + 1 + 1) ≤ xa.size
      · have hb' : i + 1 + (k + 1) ≤ xa.size := by omega
        simp only [if_pos hb, if_pos hb', Option.some.injEq, WalkCursor.mk.injEq, true_and]
        refine ⟨by omega, ?_⟩
        simp only [gapYCost]
        push_cast
        simp only [Int.add_mul, Int.one_mul]
        split <;> omega
      · have hb' : ¬ i + 1 + (k + 1) ≤ xa.size := by omega
        simp only [if_neg hb, if_neg hb']

def checkRunsFast3Go (sc : Scoring) (xa ya : Array Char) :
    List (Step × Nat) → Nat → Nat → Option Step → Int → Option Int
  | [], i, j, _, acc => if xa.size ≤ i ∧ ya.size ≤ j then some acc else none
  | (_, 0) :: rest, i, j, prev, acc => checkRunsFast3Go sc xa ya rest i j prev acc
  | (.diag, k + 1) :: rest, i, j, _, acc =>
    if h : i + (k + 1) ≤ xa.size ∧ j + (k + 1) ≤ ya.size then
      let mis := diagMisFast3 xa ya k i j h
      checkRunsFast3Go sc xa ya rest (i + (k + 1)) (j + (k + 1)) (some .diag)
        (acc + diagRunScore3 sc (k + 1) mis)
    else none
  | (.gapX, k + 1) :: rest, i, j, prev, acc =>
    if j + (k + 1) ≤ ya.size then
      checkRunsFast3Go sc xa ya rest i (j + (k + 1)) (some .gapX)
        (acc + gapXCost sc prev + (k : Int) * sc.gapExtend)
    else none
  | (.gapY, k + 1) :: rest, i, j, prev, acc =>
    if i + (k + 1) ≤ xa.size then
      checkRunsFast3Go sc xa ya rest (i + (k + 1)) j (some .gapY)
        (acc + gapYCost sc prev + (k : Int) * sc.gapExtend)
    else none

def checkRunsFast3 (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat))
    (st : WalkCursor) : Option Int :=
  checkRunsFast3Go sc xa ya runs st.i st.j st.prev st.score

theorem checkRunsFast3Go_eq (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat)) :
    ∀ i j prev acc, checkRunsFast3Go sc xa ya runs i j prev acc =
      checkRuns sc xa ya runs ⟨i, j, prev, acc⟩ := by
  induction runs with
  | nil =>
    intro i j prev acc
    simp only [checkRunsFast3Go, checkRuns, walkCheckA]
    cases hx : xa[i]? <;> cases hy : ya[j]? <;>
      simp only [Array.getElem?_eq_none_iff, Array.getElem?_eq_some_iff] at hx hy
    · split <;> first | rfl | omega
    · obtain ⟨hj, -⟩ := hy; split <;> first | rfl | omega
    · obtain ⟨hi, -⟩ := hx; split <;> first | rfl | omega
    · obtain ⟨hi, -⟩ := hx; obtain ⟨hj, -⟩ := hy; split <;> first | rfl | omega
  | cons sn rest ih =>
    intro i j prev acc
    obtain ⟨s, n⟩ := sn
    cases n with
    | zero => cases s <;> simp only [checkRunsFast3Go, checkRuns, checkRepeatFast, Option.bind, ih]
    | succ k =>
      cases s
      · simp only [checkRunsFast3Go, checkRuns, checkRepeatFast_diag3, diagMisFast3_eq]
        split <;> simp only [Option.bind, ih]
      · simp only [checkRunsFast3Go, checkRuns, checkRepeatFast_gapX3]
        split <;> simp only [Option.bind, ih]
      · simp only [checkRunsFast3Go, checkRuns, checkRepeatFast_gapY3]
        split <;> simp only [Option.bind, ih]

theorem checkRunsFast3_eq (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat))
    (st : WalkCursor) : checkRunsFast3 sc xa ya runs st = checkRuns sc xa ya runs st :=
  checkRunsFast3Go_eq sc xa ya runs st.i st.j st.prev st.score

theorem checkRunsFast3_sound (sc : Scoring) (xa ya : Array Char) (runs : List (Step × Nat))
    (score : Int) (h : checkRunsFast3 sc xa ya runs ⟨0,0,none,0⟩ = some score) :
    IsMonotoneWalk (expandCigar runs.toArray) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar runs.toArray) = score :=
  checkRuns_sound sc xa ya runs score (checkRunsFast3_eq sc xa ya runs _ ▸ h)

end AlignmentSpec
#print axioms AlignmentSpec.checkRunsFast3_eq
#print axioms AlignmentSpec.checkRunsFast3_sound
