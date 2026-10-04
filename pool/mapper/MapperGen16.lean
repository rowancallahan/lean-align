import MapperGenScore

/-!
Penalty exactly `16` (scoring `(0, −4, −6, −2)`).

A walk scoring `≥ −16` is gapless, one gap run of length `≤ 5`, or has exactly two
gap columns and no mismatch (`shape16`).  The last case is `TwoGap`: the read
splits into a prefix on the start diagonal, a middle one diagonal off, and a
suffix on the end diagonal, all exact.
-/

namespace MapSpec

open AlignmentSpec

/-- Two gap columns (`x1`, `x2`: does the column take a window letter), no mismatch. -/
def TwoGap (xs ys : List Char) : Prop :=
  ∃ i j k x1 x2 : Nat, ∃ (hx : i + (1 - x1) + j + (1 - x2) + k = xs.length)
    (hy : i + x1 + j + x2 + k = ys.length), x1 ≤ 1 ∧ x2 ≤ 1 ∧
    (∀ t (h : t < i), xs[t]'(by omega) = ys[t]'(by omega)) ∧
    (∀ t (h : t < j), xs[i + (1 - x1) + t]'(by omega) = ys[i + x1 + t]'(by omega)) ∧
    (∀ t (h : t < k), xs[i + (1 - x1) + j + (1 - x2) + t]'(by omega) = ys[i + x1 + j + x2 + t]'(by omega))

theorem mism_diags (i : Nat) (rest : List Step) (xs ys : List Char) (hx : i ≤ xs.length) (hy : i ≤ ys.length)
    (h : mism (List.replicate i .diag ++ rest) xs ys = 0) :
    (∀ t (h1 : t < i), xs[t]'(by omega) = ys[t]'(by omega)) ∧ mism rest (xs.drop i) (ys.drop i) = 0 := by
  induction i generalizing xs ys with
  | zero => simpa using h
  | succ i ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        simp only [List.replicate_succ, List.cons_append, mism] at h
        simp only [List.length_cons] at hx hy
        by_cases hxy : x = y
        · rw [if_pos hxy, Nat.zero_add] at h
          obtain ⟨a, b⟩ := ih xs ys (by omega) (by omega) h
          refine ⟨fun t ht => ?_, by simpa using b⟩
          cases t with
          | zero => simpa using hxy
          | succ t => simpa using a t (by omega)
        · rw [if_neg hxy] at h; omega

theorem mism_gap (g : Step) (hg : g ≠ .diag) (rest : List Step) (xs ys : List Char)
    (hx : xConsumed g ≤ xs.length) (hy : yConsumed g ≤ ys.length) :
    mism (g :: rest) xs ys = mism rest (xs.drop (xConsumed g)) (ys.drop (yConsumed g)) := by
  cases g with
  | diag => exact absurd rfl hg
  | gapX =>
    cases ys with
    | nil => simp [yConsumed] at hy
    | cons y ys => cases xs <;> simp [mism, xConsumed, yConsumed]
  | gapY =>
    cases xs with
    | nil => simp [xConsumed] at hx
    | cons x xs => cases ys <;> simp [mism, xConsumed, yConsumed]

theorem split_gap (path : List Step) (h : 0 < cnt .gapX path + cnt .gapY path) :
    ∃ i g rest, g ≠ .diag ∧ path = List.replicate i .diag ++ g :: rest ∧
      cnt .gapX rest + cnt .gapY rest + 1 = cnt .gapX path + cnt .gapY path := by
  induction path with
  | nil => simp [cnt] at h
  | cons s rest ih =>
    cases s with
    | diag =>
      simp only [cnt, reduceCtorEq, if_false, Nat.zero_add] at h ⊢
      obtain ⟨i, g, r, hg, he, hc⟩ := ih h
      exact ⟨i + 1, g, r, hg, by rw [he]; simp [List.replicate_succ], hc⟩
    | gapX => exact ⟨0, .gapX, rest, by decide, by simp, by simp [cnt]; omega⟩
    | gapY => exact ⟨0, .gapY, rest, by decide, by simp, by simp [cnt]; omega⟩

theorem no_gap (path : List Step) (h : cnt .gapX path + cnt .gapY path = 0) :
    path = List.replicate path.length .diag := by
  apply List.eq_replicate_of_mem
  intro x hx
  cases x with
  | diag => rfl
  | gapX => exact absurd hx (cnt_eq_zero _ _ (by omega))
  | gapY => exact absurd hx (cnt_eq_zero _ _ (by omega))

theorem consumed_gap (g : Step) (hg : g ≠ .diag) : xConsumed g = 1 - yConsumed g ∧ yConsumed g ≤ 1 := by
  cases g <;> simp_all [xConsumed, yConsumed]

theorem sum_reps (i : Nat) (f : Step → Nat) (hf : f .diag = 1) : ((List.replicate i Step.diag).map f).sum = i := by
  induction i with
  | zero => simp
  | succ i ih => simp [List.replicate_succ, hf] at ih ⊢; omega

/-- A walk with no mismatch and two gap columns. -/
theorem twoGap_of (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hm : mism path xs ys = 0) (hc : cnt .gapX path + cnt .gapY path = 2) : TwoGap xs ys := by
  obtain ⟨i, g1, r1, hg1, he1, hc1⟩ := split_gap path (by omega)
  obtain ⟨j, g2, r2, hg2, he2, hc2⟩ := split_gap r1 (by omega)
  have hk := no_gap r2 (by omega)
  generalize r2.length = k at hk
  subst he1 he2 hk
  obtain ⟨hwx, hwy⟩ := hw
  obtain ⟨c1, d1⟩ := consumed_gap g1 hg1
  obtain ⟨c2, d2⟩ := consumed_gap g2 hg2
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
    sum_reps _ xConsumed rfl, sum_reps _ yConsumed rfl] at hwx hwy
  rw [c1] at hwx; rw [c2] at hwx
  obtain ⟨p1, m1⟩ := mism_diags i _ xs ys (by omega) (by omega) hm
  rw [mism_gap g1 hg1 _ _ _ (by simp; omega) (by simp; omega)] at m1
  obtain ⟨p2, m2⟩ := mism_diags j _ _ _ (by simp; omega) (by simp; omega) m1
  rw [mism_gap g2 hg2 _ _ _ (by simp; omega) (by simp; omega)] at m2
  rw [← List.append_nil (List.replicate k Step.diag)] at m2
  obtain ⟨p3, -⟩ := mism_diags k [] _ _ (by simp; omega) (by simp; omega) m2
  refine ⟨i, j, k, yConsumed g1, yConsumed g2, by omega, by omega, d1, d2, p1, fun t ht => ?_, fun t ht => ?_⟩
  · have := p2 t ht
    simp only [List.getElem_drop, c1, Nat.add_assoc] at this ⊢
    exact this
  · have := p3 t ht
    simp only [List.getElem_drop, c1, c2, Nat.add_assoc] at this ⊢
    exact this

/-- Mismatches, runs and columns of a walk scoring `≥ −16`. -/
theorem counts16 (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -16 ≤ walkScore sc0 xs ys path) :
    4 * mism path xs ys + 6 * runs .gapX path none + 6 * runs .gapY path none +
      2 * cnt .gapX path + 2 * cnt .gapY path ≤ 16 ∧
    (0 < cnt .gapX path → 0 < runs .gapX path none) ∧
    (0 < cnt .gapY path → 0 < runs .gapY path none) ∧
    runs .gapX path none ≤ cnt .gapX path ∧ runs .gapY path none ≤ cnt .gapY path := by
  obtain ⟨hx, hy⟩ := hw
  have h := scoreWalk_le_counts sc0 valid_sc0 path xs ys none hx hy
  unfold walkScore at hs
  simp only [sc0] at h hs
  exact ⟨by omega, runs_pos _ _ _ (by simp), runs_pos _ _ _ (by simp), runs_le_cnt _ _ _, runs_le_cnt _ _ _⟩

/-- A walk scoring `≥ −16`: gapless, one gap run of length `≤ 5`, or two gap columns
and no mismatch. -/
theorem shape16 (path : List Step) (xs ys : List Char) (hw : IsMonotoneWalk path xs ys)
    (hs : -16 ≤ walkScore sc0 xs ys path) :
    path = List.replicate xs.length .diag ∨
    (∃ i L j, 0 < L ∧ L ≤ 5 ∧ path = List.replicate i .diag ++ List.replicate L .gapX ++ List.replicate j .diag) ∨
    (∃ i L j, 0 < L ∧ L ≤ 5 ∧ path = List.replicate i .diag ++ List.replicate L .gapY ++ List.replicate j .diag) ∨
    TwoGap xs ys := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := counts16 path xs ys hw hs
  by_cases h2g : runs .gapX path none + runs .gapY path none ≥ 2
  · right; right; right
    exact twoGap_of path xs ys hw (by omega) (by omega)
  by_cases hX : cnt .gapX path = 0
  · by_cases hY : cnt .gapY path = 0
    · left
      exact (eq_diags_of_no_gap path xs ys hw (by
        intro h; rcases h with h | h
        · exact cnt_eq_zero _ _ hX h
        · exact cnt_eq_zero _ _ hY h)).2
    · right; right; left
      obtain ⟨i, l, j, hl, he⟩ := shape_one_run .gapY (by decide) path none (by simp)
        (not_mem_iff_all' path (cnt_eq_zero _ _ hX)) (by have := h3 (by omega); omega)
      refine ⟨i, l, j, hl, ?_, he⟩
      have : cnt .gapY path = l := by rw [he, cnt_shape _ _ (by decide)]; simp
      omega
  · right; left
    have hY : cnt .gapY path = 0 := by
      have := h2 (by omega)
      by_cases hY : cnt .gapY path = 0
      · exact hY
      · have := h3 (by omega); omega
    obtain ⟨i, l, j, hl, he⟩ := shape_one_run .gapX (by decide) path none (by simp)
      (not_mem_iff_all path (cnt_eq_zero _ _ hY)) (by have := h2 (by omega); omega)
    refine ⟨i, l, j, hl, ?_, he⟩
    have : cnt .gapX path = l := by rw [he, cnt_shape _ _ (by decide)]; simp
    omega

/-- Each column costs at most `8` (a mismatch `4`). -/
theorem score_lb (path : List Step) (xs ys : List Char) (prev : Option Step) :
    -4 * (mism path xs ys : Int) - 8 * ((cnt .gapX path + cnt .gapY path : Nat) : Int) ≤
      scoreWalk sc0 path xs ys prev := by
  induction path generalizing xs ys prev with
  | nil => simp [scoreWalk, mism, cnt]
  | cons s rest ih =>
    cases s with
    | diag =>
      cases xs with
      | nil => simp [scoreWalk, mism, cnt]; omega
      | cons x xs =>
        cases ys with
        | nil => simp [scoreWalk, mism, cnt]; omega
        | cons y ys =>
          have := ih xs ys (some .diag)
          simp only [sc0] at this
          by_cases hxy : x = y <;> simp [scoreWalk, mism, cnt, hxy, sc0] <;> omega
    | gapX =>
      cases ys with
      | nil => cases xs <;> simp [scoreWalk, mism, cnt] <;> omega
      | cons y ys =>
        have := ih xs ys (some .gapX)
        simp only [sc0] at this
        by_cases hp : prev = some .gapX <;> cases xs <;> simp [scoreWalk, mism, cnt, hp, sc0] <;> omega
    | gapY =>
      cases xs with
      | nil => cases ys <;> simp [scoreWalk, mism, cnt] <;> omega
      | cons x xs =>
        have := ih xs ys (some .gapY)
        simp only [sc0] at this
        by_cases hp : prev = some .gapY <;> cases ys <;> simp [scoreWalk, mism, cnt, hp, sc0] <;> omega

theorem mism_diags_of (i : Nat) (rest : List Step) (xs ys : List Char) (hx : i ≤ xs.length) (hy : i ≤ ys.length)
    (h : ∀ t (h1 : t < i), xs[t]'(by omega) = ys[t]'(by omega)) :
    mism (List.replicate i .diag ++ rest) xs ys = mism rest (xs.drop i) (ys.drop i) := by
  induction i generalizing xs ys with
  | zero => simp
  | succ i ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        simp only [List.length_cons] at hx hy
        have h0 : x = y := by simpa using h 0 (by omega)
        simp only [List.replicate_succ, List.cons_append, mism, if_pos h0, Nat.zero_add, List.drop_succ_cons]
        exact ih xs ys (by omega) (by omega) (fun t ht => by simpa using h (t + 1) (by omega))

/-- **A two-gap walk with no mismatch scores `≥ −16`.** -/
theorem walk2_score (xs ys : List Char) (g1 g2 : Step) (hg1 : g1 ≠ .diag) (hg2 : g2 ≠ .diag) (i j k : Nat)
    (hx : i + xConsumed g1 + j + xConsumed g2 + k = xs.length)
    (hy : i + yConsumed g1 + j + yConsumed g2 + k = ys.length)
    (p1 : ∀ t (h : t < i), xs[t]'(by omega) = ys[t]'(by omega))
    (p2 : ∀ t (h : t < j), xs[i + xConsumed g1 + t]'(by omega) = ys[i + yConsumed g1 + t]'(by omega))
    (p3 : ∀ t (h : t < k), xs[i + xConsumed g1 + j + xConsumed g2 + t]'(by omega) =
      ys[i + yConsumed g1 + j + yConsumed g2 + t]'(by omega)) :
    ∃ path, IsMonotoneWalk path xs ys ∧ -16 ≤ walkScore sc0 xs ys path := by
  refine ⟨List.replicate i .diag ++ g1 :: (List.replicate j .diag ++ g2 :: List.replicate k .diag), ?_, ?_⟩
  · constructor <;> simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      sum_reps _ xConsumed rfl, sum_reps _ yConsumed rfl] <;> omega
  · have hm : mism (List.replicate i .diag ++ g1 :: (List.replicate j .diag ++ g2 :: List.replicate k .diag)) xs ys = 0 := by
      rw [mism_diags_of i _ xs ys (by omega) (by omega) p1,
        mism_gap g1 hg1 _ _ _ (by simp; omega) (by simp; omega),
        mism_diags_of j _ _ _ (by simp; omega) (by simp; omega) (fun t ht => by
          simp only [List.getElem_drop, Nat.add_assoc]; have := p2 t ht; simpa [Nat.add_assoc] using this),
        mism_gap g2 hg2 _ _ _ (by simp; omega) (by simp; omega),
        ← List.append_nil (List.replicate k Step.diag),
        mism_diags_of k [] _ _ (by simp; omega) (by simp; omega) (fun t ht => by
          simp only [List.getElem_drop, Nat.add_assoc]; have := p3 t ht; simpa [Nat.add_assoc] using this)]
      simp [mism]
    have hc : cnt .gapX (List.replicate i .diag ++ g1 :: (List.replicate j .diag ++ g2 :: List.replicate k .diag)) +
        cnt .gapY (List.replicate i .diag ++ g1 :: (List.replicate j .diag ++ g2 :: List.replicate k .diag)) = 2 := by
      simp only [cnt_append, cnt, cnt_replicate]
      cases g1 <;> cases g2 <;> simp_all
    have := score_lb (List.replicate i .diag ++ g1 :: (List.replicate j .diag ++ g2 :: List.replicate k .diag)) xs ys none
    rw [hm, hc] at this
    unfold walkScore; omega

/-- **Penalty `16`**: the cases. -/
theorem penQ16 (Q : Nat) (hQ : 16 ≤ Q) (xs ys : List Char) (h : penQ Q xs ys = 16) :
    (xs.length = ys.length ∧ hamming xs ys = 4) ∨
    (∃ L i, ys.length = xs.length + L ∧ 1 ≤ L ∧ L ≤ 5 ∧ i ≤ xs.length ∧ 6 + 2 * L + 4 * misIns xs ys L i = 16) ∨
    (∃ L i, xs.length = ys.length + L ∧ 1 ≤ L ∧ L ≤ 5 ∧ i ≤ ys.length ∧ 6 + 2 * L + 4 * misDel xs ys L i = 16) ∨
    TwoGap xs ys := by
  obtain ⟨path, bs, hb, hw, hs, -⟩ := best_facts xs ys
  rw [penQ_of Q xs ys path bs hb] at h
  have hbs : bs = -16 := by split at h <;> omega
  subst hbs
  rcases shape16 path xs ys hw (by omega) with he | ⟨i, L, j, hL, hL5, he⟩ | ⟨i, L, j, hL, hL5, he⟩ | ht
  · left
    have hl := length_of_diags hw he
    rw [he, walkScore, score_diags_all xs ys none hl _ rfl] at hs
    exact ⟨hl, by omega⟩
  · right; left
    have hlen := lengths_ins (he ▸ hw)
    rw [he, score_ins xs ys i L j hL hlen.1 hlen.2] at hs
    exact ⟨L, i, by omega, hL, hL5, by omega, by omega⟩
  · right; right; left
    have hlen := lengths_del (he ▸ hw)
    rw [he, score_del xs ys i L j hL hlen.1 hlen.2] at hs
    exact ⟨L, i, by omega, hL, hL5, by omega, by omega⟩
  · right; right; right; exact ht

end MapSpec

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- A necessary condition for penalty `16` when the formula `fB` is `≥ 16`: four
mismatches (same length), at most two mismatches around one gap of length `≤ 5`,
or an exact two-gap split (prefix ≤ first mismatch, suffix ≥ last mismatch of the
end diagonal, middle exact one diagonal off). -/
def filt16 (R G : ByteArray) (st len : Nat) : Bool :=
  let n := R.size
  let s := skipOf n len
  let A := fwdMis R G st n 0 1
  let B := bwdMis R G st len 0 n 1
  (len == n && hamming R G st 4 0 n 0 == 4) ||
  (len != n && decide (gapLen n len ≤ 5) && decide (bwdMis R G st len s n 3 - s ≤ fwdMis R G st (n - s) 0 3)) ||
  ((len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0))

theorem filt16_iff (R G : ByteArray) (st len : Nat) : filt16 R G st len = true ↔
    (len = R.size ∧ hamming R G st 4 0 R.size 0 = 4) ∨
    (len ≠ R.size ∧ gapLen R.size len ≤ 5 ∧
      bwdMis R G st len (skipOf R.size len) R.size 3 - skipOf R.size len ≤
        fwdMis R G st (R.size - skipOf R.size len) 0 3) ∨
    ((len = R.size ∨ len = R.size + 2 ∨ len + 2 = R.size) ∧
      (hamming R G (st + 1) 0 (fwdMis R G st R.size 0 1 + 1) (bwdMis R G st len 0 R.size 1 - 1) 0 = 0 ∨ st = 0 ∨
        hamming R G (st - 1) 0 (fwdMis R G st R.size 0 1 + 1) (bwdMis R G st len 0 R.size 1 - 1) 0 = 0)) := by
  simp only [filt16, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, or_assoc, and_assoc]

/-- A sufficient test for an exact two-gap walk (`x1`, `x2`: does the gap column
take a window letter; `A`, `B`: first mismatch of the start diagonal, one past the
last of the end diagonal): the longest exact prefix and suffix leave a middle that
is exact one diagonal off. -/
def twoGapAt (R G : ByteArray) (st len x1 x2 A B : Nat) : Bool :=
  let n := R.size
  let M := n - (1 - x1) - (1 - x2)
  let i := min A M
  let k := min (n - B) (M - i)
  let j := M - i - k
  decide (x1 ≤ 1 ∧ x2 ≤ 1 ∧ (1 - x1) + (1 - x2) ≤ n ∧ len + (1 - x1) + (1 - x2) = n + x1 + x2) &&
  (j == 0 || if x1 = 1 then hamming R G (st + 1) 0 i (i + j) 0 == 0
             else (decide (1 ≤ st) && hamming R G (st - 1) 0 (i + 1) (i + 1 + j) 0 == 0))

/-- The two-gap test for the gap kinds the lengths allow. -/
def twoGapB (R G : ByteArray) (st len : Nat) : Bool :=
  let A := fwdMis R G st R.size 0 1
  let B := bwdMis R G st len 0 R.size 1
  if len = R.size + 2 then twoGapAt R G st len 1 1 A B
  else if len + 2 = R.size then twoGapAt R G st len 0 0 A B
  else if len = R.size then twoGapAt R G st len 1 0 A B || twoGapAt R G st len 0 1 A B
  else false

section
variable {R G : ByteArray} {xs seq : List Char} (hr : Encodes R xs) (hg : Encodes G seq)
include hr hg

theorem clean_of (u p : Nat) (hu : u < xs.length) (hp : p < seq.length) (h : xs[u] = seq[p]) :
    (R.get! u != G.get! p) = false := by
  rw [neq_bytes hr hg u p hu hp]; simp [h]

theorem ham_take_bytes (st len : Nat) (hfit : st + len ≤ seq.length) (i : Nat) (h1 : i ≤ xs.length) (h2 : i ≤ len) :
    MapSpec.hamming (xs.take i) (((seq.drop st).take len).take i) = preB R G st i := by
  have hn : R.size = xs.length := hr.1
  unfold preB
  rw [hamming_cnt _ _ (fun k => R.get! k != G.get! (st + k)) (fun k h1' h2' => by
    simp only [List.getElem_take, List.getElem_drop]
    rw [neq_bytes hr hg k (st + k) (by simp at h1'; omega) (by simp at h2'; omega)])]
  congr 1; simp; omega

/-- Same length, four mismatches: penalty at most `16`. -/
theorem pen_le_ham4 (Q : Nat) (hQ : 16 ≤ Q) (st : Nat) (hfit : st + R.size ≤ seq.length)
    (h4 : preB R G st R.size = 4) : penQ Q xs ((seq.drop st).take R.size) ≤ 16 := by
  have hn : R.size = xs.length := hr.1
  have := ham_take_bytes hr hg st R.size hfit xs.length (by omega) (by omega)
  rw [List.take_length, List.take_of_length_le (by simp; omega)] at this
  have hl : xs.length = ((seq.drop st).take R.size).length := by simp; omega
  rw [hn] at h4
  have := (penQ_same Q xs _ hl).1 (by omega)
  omega

/-- **Penalty `16` passes the filter.** -/
theorem filt16_of (Q : Nat) (hQ : 16 ≤ Q) (st len : Nat) (hfit : st + len ≤ seq.length)
    (h : penQ Q xs ((seq.drop st).take len) = 16) : filt16 R G st len = true := by
  have hn : R.size = xs.length := hr.1
  generalize hys : (seq.drop st).take len = ys at h
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  have hpre : ∀ i, i ≤ xs.length → i ≤ len →
      MapSpec.hamming (xs.take i) (ys.take i) = preB R G st i := by
    intro i h1 h2; rw [← hys]; exact ham_take_bytes hr hg st len hfit i h1 h2
  rw [filt16_iff]
  rcases penQ16 Q hQ xs ys h with ⟨hl, hh⟩ | ⟨L, i, hl, hL1, hL5, hi, hm⟩ | ⟨L, i, hl, hL1, hL5, hi, hm⟩ |
      ⟨i, j, k, x1, x2, hx, hy, d1, d2, p1, p2, p3⟩
  · -- four mismatches
    left
    refine ⟨by omega, ?_⟩
    have := hpre xs.length (Nat.le_refl _) (by omega)
    rw [List.take_length, List.take_of_length_le (by omega)] at this
    rw [hamming_spec R G st 4 R.size _ 0 0 rfl (Nat.zero_le _)]
    unfold preB at this
    rw [Nat.sub_zero, hn, ← this, hh]; rfl
  · -- insertion
    right; left
    have hmis : misIns xs ys L i = misB R G st len 0 i := by
      unfold misIns misB
      rw [hpre i hi (by omega), Nat.add_zero]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + k) != G.get! (st + len + (i + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg (i + k) (st + len + (i + k) - R.size) (by omega) (by omega),
          hyk _ (by omega)]
        have e : st + (i + L + k) = st + len + (i + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) i 0]
      congr 1 <;> simp <;> omega
    have hsk : skipOf R.size len = 0 := by unfold skipOf; split <;> omega
    have hgl : gapLen R.size len = L := by unfold gapLen; split <;> omega
    rw [hsk, hgl]
    refine ⟨by omega, hL5, ?_⟩
    unfold misB preB sufB at hmis
    obtain ⟨-, -, f3⟩ := fwdMis_spec R G st (R.size - 0) _ 0 3 rfl (Nat.zero_le _) (by omega)
    obtain ⟨-, -, e3⟩ := bwdMis_spec R G st len 0 _ R.size 3 rfl (Nat.zero_le _) (by omega)
    have a := (f3 i (Nat.zero_le _) (by omega)).1 (by rw [Nat.sub_zero]; omega)
    have b := (e3 (i + 0) (Nat.zero_le _) (by omega)).1 (by omega)
    omega
  · -- deletion
    right; left
    have hmis : misDel xs ys L i = misB R G st len L i := by
      unfold misDel misB
      rw [hpre i (by omega) (by omega)]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + L + k) !=
          G.get! (st + len + (i + L + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg _ _ (by omega) (by omega), hyk (i + k) (by omega)]
        have e : st + (i + k) = st + len + (i + L + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + L) 0]
      congr 1 <;> simp <;> omega
    have hsk : skipOf R.size len = L := by unfold skipOf; split <;> omega
    have hgl : gapLen R.size len = L := by unfold gapLen; split <;> omega
    rw [hsk, hgl]
    refine ⟨by omega, hL5, ?_⟩
    unfold misB preB sufB at hmis
    obtain ⟨-, -, f3⟩ := fwdMis_spec R G st (R.size - L) _ 0 3 rfl (Nat.zero_le _) (by omega)
    obtain ⟨-, -, e3⟩ := bwdMis_spec R G st len L _ R.size 3 rfl (by omega) (by omega)
    have a := (f3 i (Nat.zero_le _) (by omega)).1 (by rw [Nat.sub_zero]; omega)
    have b := (e3 (i + L) (by omega) (by omega)).1 (by omega)
    omega
  · -- two gaps
    right; right
    refine ⟨by omega, ?_⟩
    obtain ⟨-, -, f1⟩ := fwdMis_spec R G st R.size _ 0 1 rfl (Nat.zero_le _) (Nat.le_refl _)
    obtain ⟨-, -, e1⟩ := bwdMis_spec R G st len 0 _ R.size 1 rfl (Nat.zero_le _) (Nat.le_refl _)
    have hA : i ≤ fwdMis R G st R.size 0 1 := by
      apply (f1 i (Nat.zero_le _) (by omega)).1
      rw [cntP_zero_of _ _ _ (fun u _ hu => clean_of hr hg u (st + u) (by omega) (by omega) (by
        rw [p1 u (by omega), hyk u (by omega)]))]
      omega
    have hB : bwdMis R G st len 0 R.size 1 ≤ R.size - k := by
      apply (e1 (R.size - k) (Nat.zero_le _) (by omega)).1
      rw [cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st + len + u - R.size) (by omega) (by omega) (by
        have := p3 (u - (R.size - k)) (by omega)
        have e1 : i + (1 - x1) + j + (1 - x2) + (u - (R.size - k)) = u := by omega
        have e2 : i + x1 + j + x2 + (u - (R.size - k)) = st + len + u - R.size - st := by omega
        simp only [e1, e2] at this
        rw [this, hyk _ (by omega)]
        congr 1; omega))]
      omega
    generalize fwdMis R G st R.size 0 1 = A at *
    generalize bwdMis R G st len 0 R.size 1 = B at *
    by_cases hx1 : x1 = 1
    · left
      subst hx1
      rw [hamming_spec R G (st + 1) 0 (B - 1) _ (A + 1) 0 rfl (Nat.le_refl _),
        cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st + 1 + u) (by omega) (by omega) (by
          have := p2 (u - i) (by omega)
          have e1 : i + (1 - 1) + (u - i) = u := by omega
          have e2 : i + 1 + (u - i) = st + 1 + u - st := by omega
          simp only [e1, e2] at this
          rw [this, hyk _ (by omega)]
          congr 1; omega))]
      rfl
    · right
      by_cases hst : st = 0
      · left; exact hst
      right
      rw [hamming_spec R G (st - 1) 0 (B - 1) _ (A + 1) 0 rfl (Nat.le_refl _),
        cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st - 1 + u) (by omega) (by omega) (by
          have := p2 (u - (i + 1)) (by omega)
          have e1 : i + (1 - x1) + (u - (i + 1)) = u := by omega
          have e2 : i + x1 + (u - (i + 1)) = st - 1 + u - st := by omega
          simp only [e1, e2] at this
          rw [this, hyk _ (by omega)]
          congr 1; omega))]
      rfl


theorem eq_of_clean (u p : Nat) (hu : u < xs.length) (hp : p < seq.length) (h : (R.get! u != G.get! p) = false) :
    xs[u] = seq[p] := by
  rw [neq_bytes hr hg u p hu hp] at h; simpa using h

/-- **The two-gap test is sound**: penalty at most `16`. -/
theorem twoGapAt_pen (Q : Nat) (hQ : 16 ≤ Q) (st len x1 x2 : Nat) (hfit : st + len ≤ seq.length)
    (h : twoGapAt R G st len x1 x2 (fwdMis R G st R.size 0 1) (bwdMis R G st len 0 R.size 1) = true) :
    penQ Q xs ((seq.drop st).take len) ≤ 16 := by
  have hn : R.size = xs.length := hr.1
  generalize hys : (seq.drop st).take len = ys
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  obtain ⟨-, -, f1⟩ := fwdMis_spec R G st R.size _ 0 1 rfl (Nat.zero_le _) (Nat.le_refl _)
  obtain ⟨-, hBn, e1⟩ := bwdMis_spec R G st len 0 _ R.size 1 rfl (Nat.zero_le _) (Nat.le_refl _)
  unfold twoGapAt at h
  generalize fwdMis R G st R.size 0 1 = A at *
  generalize bwdMis R G st len 0 R.size 1 = B at *
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hx1, hx2, hr12, hlen⟩, hmid⟩ := h
  generalize hM : R.size - (1 - x1) - (1 - x2) = M at hmid
  generalize hi : min A M = i at hmid
  generalize hk : min (R.size - B) (M - i) = k at hmid
  obtain ⟨g1, hg1, e1', f1'⟩ : ∃ g, g ≠ Step.diag ∧ yConsumed g = x1 ∧ xConsumed g = 1 - x1 := by
    rcases (by omega : x1 = 0 ∨ x1 = 1) with rfl | rfl
    · exact ⟨.gapY, by decide, rfl, rfl⟩
    · exact ⟨.gapX, by decide, rfl, rfl⟩
  obtain ⟨g2, hg2, e2', f2'⟩ : ∃ g, g ≠ Step.diag ∧ yConsumed g = x2 ∧ xConsumed g = 1 - x2 := by
    rcases (by omega : x2 = 0 ∨ x2 = 1) with rfl | rfl
    · exact ⟨.gapY, by decide, rfl, rfl⟩
    · exact ⟨.gapX, by decide, rfl, rfl⟩
  -- prefix and suffix clean
  have hpre : cntP (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) = 0 := by
    have := (f1 i (Nat.zero_le _) (by omega)).2 (by omega); omega
  have hsuf : cntP (fun x => R.get! x != G.get! (st + len + x - R.size)) (R.size - k) (R.size - (R.size - k)) = 0 := by
    have := (e1 (R.size - k) (Nat.zero_le _) (by omega)).2 (by omega); omega
  obtain ⟨path, hw, hs⟩ := walk2_score xs ys g1 g2 hg1 hg2 i (M - i - k) k (by omega) (by omega)
    (fun t ht => by
      rw [hyk t (by omega)]
      exact eq_of_clean hr hg t (st + t) (by omega) (by omega)
        (cntP_eq_zero _ _ _ hpre t (by omega) (by omega)))
    (fun t ht => by
      rcases hmid with hj | hmid
      · omega
      by_cases h1 : x1 = 1
      · rw [if_pos h1] at hmid
        simp only [beq_iff_eq] at hmid
        rw [hamming_spec R G (st + 1) 0 (i + (M - i - k)) _ i 0 rfl (Nat.le_refl _)] at hmid
        have hc : cntP (fun k => R.get! k != G.get! (st + 1 + k)) i (i + (M - i - k) - i) = 0 := by omega
        have := eq_of_clean hr hg (i + t) (st + 1 + (i + t)) (by omega) (by omega)
          (cntP_eq_zero _ _ _ hc (i + t) (by omega) (by omega))
        simp only [f1', e1', h1]
        rw [hyk _ (by omega)]
        simp only [Nat.sub_self, Nat.add_zero] at this ⊢
        rw [this]; congr 1; omega
      · rw [if_neg h1] at hmid
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmid
        obtain ⟨hst, hmid⟩ := hmid
        rw [hamming_spec R G (st - 1) 0 (i + 1 + (M - i - k)) _ (i + 1) 0 rfl (Nat.le_refl _)] at hmid
        have hc : cntP (fun k => R.get! k != G.get! (st - 1 + k)) (i + 1) (i + 1 + (M - i - k) - (i + 1)) = 0 := by
          omega
        have hx0 : x1 = 0 := by omega
        have := eq_of_clean hr hg (i + 1 + t) (st - 1 + (i + 1 + t)) (by omega) (by omega)
          (cntP_eq_zero _ _ _ hc (i + 1 + t) (by omega) (by omega))
        simp only [f1', e1', hx0]
        rw [hyk _ (by omega)]
        simp only [Nat.sub_zero] at this ⊢
        rw [this]; congr 1; omega)
    (fun t ht => by
      rw [hyk _ (by omega)]
      have := eq_of_clean hr hg _ (st + len + (R.size - k + t) - R.size) (by omega) (by omega)
        (cntP_eq_zero _ _ _ hsuf (R.size - k + t) (by omega) (by omega))
      simp only [f1', e1', f2', e2']
      have ea : i + (1 - x1) + (M - i - k) + (1 - x2) + t = R.size - k + t := by omega
      simp only [ea]
      rw [this]; congr 1; omega)
  obtain ⟨p0, bs, hb, -, -, hmax⟩ := best_facts xs ys
  rw [penQ_of Q xs ys p0 bs hb]
  have := hmax path hw
  split <;> omega


theorem twoGapB_pen (Q : Nat) (hQ : 16 ≤ Q) (st len : Nat) (hfit : st + len ≤ seq.length)
    (h : twoGapB R G st len = true) : penQ Q xs ((seq.drop st).take len) ≤ 16 := by
  unfold twoGapB at h
  dsimp only at h
  split at h
  · exact twoGapAt_pen hr hg Q hQ st len 1 1 hfit h
  split at h
  · exact twoGapAt_pen hr hg Q hQ st len 0 0 hfit h
  split at h
  · rcases Bool.or_eq_true _ _ ▸ h with h | h
    · exact twoGapAt_pen hr hg Q hQ st len 1 0 hfit h
    · exact twoGapAt_pen hr hg Q hQ st len 0 1 hfit h
  · cases h

end

end MapSpec.Fast
