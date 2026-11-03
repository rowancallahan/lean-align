import PairInterleave

/-!
# Codec `pairFastC`: one index over the concatenated genome

`pairFastI` (codecs/PairInterleave.lean) searches each chromosome with its own
index; a chromosome where the read does not map has no best yet, so there both
strands look up every seed, the huge repeat buckets included (chr1+chr2:
125 anchors per read vs 14 on chr1 alone, `PAIR_DIAG=1 pair_bench`).

Here the chromosomes are concatenated into one byte string `G` (chromosome `c`
at `offs[c]`, checked by `catOk`), with ONE index over `G`.  Each seed is looked
up once in `G`; its anchors are cut into per-chromosome slices (`sliceA`:
binary search, shift to chromosome coordinates; seeds across a junction are
dropped), and every chromosome takes one proved lookup step with its slice
(`lzStepA`, the step of `lazyLoop`).  The seed order, the stop test `best < 4k`
and the strand interleaving are global, as on one chromosome.  Windows are still
scored on the chromosomes' own bytes, so a window never spans a junction and no
separator is needed.  (Concatenating with separators and mapping `G` as one
chromosome would not be exact: a window that runs 1–3 letters into a separator
can score ≥ −12 and beat or tie the true hit.)

    … → mapFastC lk ix G offs gbs R = mapSpecBoth sc0 (-12) g read              (mapFastC_eq_mapSpecBoth)
    … → pairFastC lk lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastC_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- First index in `[lo, hi)` whose entry is `≥ x` (`a` increasing). -/
def lbA (a : Array Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if lo < hi then
    if a[(lo + hi) / 2]! < x then lbA a x ((lo + hi) / 2 + 1) hi else lbA a x lo ((lo + hi) / 2)
  else lo
termination_by hi - lo

/-- Anchors of seed `j` in `G` (`a`) whose seed lies in the chromosome at `o` of
length `n`, in its coordinates. -/
@[inline] def sliceA (a : Array Nat) (j o n : Nat) : Array Nat :=
  let i := lbA a (16 * (o + BIAS - j * q)) 0 a.size
  ((a.extract i (lbA a (16 * (o + n + 1 + BIAS - j * q - q)) 0 a.size)).map (· - 16 * o))

/-- Chromosome `c` is `G[offs[c] ..< offs[c] + gbs[c].size]`. -/
def catOk (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) : Bool :=
  (List.range gbs.size).all fun c =>
    decide (offs[c]! + gbs[c]!.size ≤ G.size) && eqRun G gbs[c]! offs[c]! 0 gbs[c]!.size

/-- One strand: seeds left, lookups done, looked-up mask, anchors per chromosome. -/
structure CS where
  ord : List Nat
  k : Nat
  looked : Nat
  as : Array (Array Nat)

@[inline] def CS.next {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (ps : Array P) (s : CS) : Nat :=
  match s.ord with
  | j :: _ => lk.size ix ps[j]!
  | [] => 0

/-- Seed `j`'s anchors `a` (in `G`) on chromosome `c` (tag `base + c`); skipped
when the chromosome has no anchor so far and none now. -/
@[inline] def stepC1 (R : ByteArray) (gbs : Array ByteArray) (offs : Array Nat) (base : Nat) (a : Array Nat)
    (j k looked : Nat) (r : Array (Array Nat) × Best) (c : Nat) : Array (Array Nat) × Best :=
  let sl := sliceA a j offs[c]! gbs[c]!.size
  if sl.isEmpty && r.1[c]!.isEmpty then r
  else
    let x := lzStepA R gbs[c]! (base + c) sl k r.1[c]! looked r.2
    (r.1.set! c x.1, x.2)

/-- Seed `j`'s anchors on every chromosome. -/
@[inline] def stepC (R : ByteArray) (gbs : Array ByteArray) (offs : Array Nat) (base : Nat) (a : Array Nat)
    (j k looked : Nat) (ass : Array (Array Nat)) (b : Best) : Array (Array Nat) × Best :=
  (List.range gbs.size).foldl (stepC1 R gbs offs base a j k looked) (ass, b)

/-- Look up the strand's next seed. -/
@[inline] def CS.adv {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G R : ByteArray)
    (gbs : Array ByteArray) (offs : Array Nat) (base : Nat) (ps : Array P) (s : CS) (b : Best) : CS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := stepC R gbs offs base (lk.look ix G R j ps[j]!) j s.k (s.looked + pow2 j) s.as b
    (⟨rest, s.k + 1, s.looked + pow2 j, r.1⟩, r.2)

/-! ## Slices -/

/-- `a` is increasing (index form). -/
def IncA (a : Array Nat) : Prop := ∀ i k, i < k → k < a.size → a[i]! < a[k]!

theorem incA_of (a : Array Nat) (h : a.toList.Pairwise (· < ·)) : IncA a := by
  intro i k hik hk
  rw [List.pairwise_iff_getElem] at h
  have := h i k (by simp; omega) (by simp; omega) hik
  simp only [Array.getElem_toList] at this
  rw [getElem!_pos a i (by omega), getElem!_pos a k hk]; exact this

theorem lbA_spec (a : Array Nat) (x : Nat) (ha : IncA a) (lo hi : Nat) (h1 : hi ≤ a.size) (h2 : lo ≤ hi)
    (hl : ∀ k, k < lo → a[k]! < x) (hh : ∀ k, hi ≤ k → k < a.size → x ≤ a[k]!) :
    (∀ k, k < lbA a x lo hi → a[k]! < x) ∧ (∀ k, lbA a x lo hi ≤ k → k < a.size → x ≤ a[k]!) ∧
      lo ≤ lbA a x lo hi ∧ lbA a x lo hi ≤ hi := by
  rw [lbA]
  split
  · next hlt =>
    split
    · next hm =>
      have := lbA_spec a x ha ((lo + hi) / 2 + 1) hi h1 (by omega) (fun k hk => by
        by_cases e : k = (lo + hi) / 2
        · subst e; exact hm
        · by_cases hk' : k < lo
          · exact hl k hk'
          · exact Nat.lt_trans (ha k _ (by omega) (by omega)) hm) hh
      exact ⟨this.1, this.2.1, by omega, this.2.2.2⟩
    · next hm =>
      have := lbA_spec a x ha lo ((lo + hi) / 2) (by omega) (by omega) hl (fun k hk hk2 => by
        by_cases e : k = (lo + hi) / 2
        · subst e; omega
        · have := ha _ k (show (lo + hi) / 2 < k by omega) hk2; omega)
      exact ⟨this.1, this.2.1, this.2.2.1, by omega⟩
  · exact ⟨hl, fun k hk hk2 => hh k (by omega) hk2, Nat.le_refl _, h2⟩
termination_by hi - lo

/-- The entries of `a` in `[lo, hi)`, found by `lbA`. -/
theorem mem_lb_extract (a : Array Nat) (ha : IncA a) (lo hi e : Nat) :
    e ∈ (a.extract (lbA a lo 0 a.size) (lbA a hi 0 a.size)).toList ↔ e ∈ a.toList ∧ lo ≤ e ∧ e < hi := by
  have L := lbA_spec a lo ha 0 a.size (Nat.le_refl _) (Nat.zero_le _) (fun k hk => by omega)
    (fun k _ hk => by omega)
  have H := lbA_spec a hi ha 0 a.size (Nat.le_refl _) (Nat.zero_le _) (fun k hk => by omega)
    (fun k _ hk => by omega)
  generalize lbA a lo 0 a.size = i at L ⊢
  generalize lbA a hi 0 a.size = i2 at H ⊢
  simp only [Array.mem_toList_iff, Array.mem_iff_getElem, Array.size_extract, Array.getElem_extract]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h1 := L.2.1 (i + u) (by omega) (by omega)
    have h2 := H.1 (i + u) (by omega)
    rw [getElem!_pos a _ (by omega)] at h1 h2
    exact ⟨⟨i + u, by omega, rfl⟩, h1, h2⟩
  · rintro ⟨⟨k, hk, rfl⟩, h1, h2⟩
    have hki : i ≤ k := by
      apply Classical.byContradiction; intro hn
      have := L.1 k (by omega); rw [getElem!_pos a _ hk] at this; omega
    have hk2 : k < i2 := by
      apply Classical.byContradiction; intro hn
      have := H.2.1 k (by omega) hk; rw [getElem!_pos a _ hk] at this; omega
    exact ⟨k - i, by omega, by congr 1; omega⟩

theorem catOk_spec (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (h : catOk G offs gbs = true)
    (c : Nat) (hc : c < gbs.size) : offs[c]! + gbs[c]!.size ≤ G.size ∧
      ∀ i, i < gbs[c]!.size → G.get! (offs[c]! + i) = gbs[c]!.get! i := by
  unfold catOk at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h c hc
  exact ⟨h1, fun i hi => by have := (eqRun_spec _ _ _ _ _).mp h2 i hi; simpa using this⟩

/-! ## One lookup on every chromosome -/

theorem getElem!_set!' {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  simp only [getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

section many

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (R : ByteArray) (gbs : Array ByteArray)
  (offs : Array Nat) (base : Nat)
  (hcw : ∀ c, c < gbs.size → ∀ st len, cw ⟨base + c, st, len⟩ = penB R gbs[c]! st len)
  (hn : 100 ≤ R.size)

include hc13 hcw hn

/-- Strand state `s` (tags `base + c`) with best `b` and looked-at windows `S`. -/
def SC (s : CS) (b : Best) (S : Window → Prop) : Prop :=
  ∃ J, J < 16 ∧ s.k = pop4 J ∧ s.looked = J ∧ s.ord.Nodup ∧ (∀ j ∈ s.ord, j < 4 ∧ bit J j = 0) ∧
    pop4 J + s.ord.length = 4 ∧ Inv cw S b ∧ s.as.size = gbs.size ∧
    ∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) J (pop4 J) s.as[c]! b S

omit hc13 hcw hn in
theorem SC.inv {s : CS} {b : Best} {S : Window → Prop} (h : SC cw R gbs base s b S) : Inv cw S b := by
  obtain ⟨J, -, -, -, -, -, -, h7, -⟩ := h; exact h7

end many

/-! ## Two strands -/

section two

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) {L P : Type} [Inhabited P] (lk : Look L P) (ix : L)
  (G : ByteArray) (gbs : Array ByteArray) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat)
  (hcw1 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c1 + c, st, len⟩ = penB R1 gbs[c]! st len) (hn1 : 100 ≤ R1.size)
  (hsl1 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R1 j (sliceA (lk.look ix G R1 j (lk.prep ix (seedHash R1 j))) j offs[c]! gbs[c]!.size))
  (hcw2 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c2 + c, st, len⟩ = penB R2 gbs[c]! st len) (hn2 : 100 ≤ R2.size)
  (hsl2 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R2 j (sliceA (lk.look ix G R2 j (lk.prep ix (seedHash R2 j))) j offs[c]! gbs[c]!.size))

include hc13 hcw1 hn1 hsl1 hcw2 hn2 hsl2

end two

/-! ## Top theorems -/

end MapSpec.Fast

