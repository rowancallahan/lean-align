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

@[inline] def CS.init {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (ps : Array P) (n : Nat) : CS :=
  ⟨seedOrder lk ix ps, 0, 0, Array.replicate n #[]⟩

@[inline] def CS.live (s : CS) (b : Best) : Bool := !s.ord.isEmpty && decide (4 * s.k ≤ b.pen)

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

/-- Two strands, one lookup at a time, as `ilLoop`. -/
@[specialize] def ilC {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (gbs : Array ByteArray) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) :
    Nat → CS → CS → Best → Best
  | 0, _, _, b => b
  | f + 1, s1, s2, b =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := s1.adv lk ix G R1 gbs offs c1 ps1 b
      ilC lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.adv lk ix G R2 gbs offs c2 ps2 b
      ilC lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2
    else b

/-- The read (tags `c`) and its reverse complement (tags `n + c`); `rf`: the
reverse strand takes ties. -/
@[specialize] def mapChromsC {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) (rf : Bool := false) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let ps := prepAll lk ix (seedHashes R)
  let pr := prepAll lk ix (seedHashes Rr)
  if rf then ilC lk ix G gbs offs Rr R n 0 pr ps 8 (CS.init lk ix pr n) (CS.init lk ix ps n) {}
  else ilC lk ix G gbs offs R Rr 0 n ps pr 8 (CS.init lk ix ps n) (CS.init lk ix pr n) {}

def mapFastC {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (rf : Bool := false) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsC lk ix G offs gbs R rf)

def pairFastC {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastC lk ix G offs gbs R1 false with
  | none => none
  | some a =>
    match mapFastC lk ix G offs gbs R2 (a.1.2 == Strand.fwd) with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

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

theorem extract_inc (a : Array Nat) (ha : IncA a) (i i2 : Nat) : IncA (a.extract i i2) := by
  intro u v huv hv
  simp only [Array.size_extract] at hv
  rw [getElem!_pos _ u (by simp; omega), getElem!_pos _ v (by simp; omega)]
  simp only [Array.getElem_extract]
  have := ha (i + u) (i + v) (by omega) (by omega)
  rwa [getElem!_pos a _ (by omega), getElem!_pos a _ (by omega)] at this

/-- **A slice of a lookup in `G` is a lookup in the chromosome.** -/
theorem sliceA_ok (G Gc R : ByteArray) (o j : Nat) (hj : j < 4) (a : Array Nat) (hl : LookOk G R j a)
    (hfit : o + Gc.size ≤ G.size) (heq : ∀ i, i < Gc.size → G.get! (o + i) = Gc.get! i) :
    LookOk Gc R j (sliceA a j o Gc.size) := by
  have ha := incA_of a hl.1
  have hw : 1 ≤ 2 ^ j ∧ 2 ^ j < 16 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have hjq : j * q ≤ 75 := by unfold q; omega
  unfold sliceA
  simp only []
  have mem := mem_lb_extract a ha (16 * (o + BIAS - j * q)) (16 * (o + Gc.size + 1 + BIAS - j * q - q))
  have hpw : ∀ s t, (a.extract s t).toList.Pairwise (· < ·) := fun s t => by
    rw [Array.toList_extract, List.extract_eq_take_drop]
    exact hl.1.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  generalize hx : a.extract _ _ = x at mem
  have hpx : x.toList.Pairwise (· < ·) := by rw [← hx]; exact hpw _ _
  -- every entry of `x` is `anchorOf j P` for a place `P` of the chromosome
  have key : ∀ e, e ∈ x.toList ↔ ∃ p, MatchAt Gc p R (j * q) ∧ e = anchorOf j (o + p) := by
    intro e
    rw [mem]
    constructor
    · rintro ⟨he, h1, h2⟩
      obtain ⟨P, hP, rfl⟩ := (hl.2 e).mp he
      unfold anchorOf at h1 h2
      simp only [BIAS, q] at h1 h2 hjq hP ⊢
      generalize 2 ^ j = w at hw h1 h2
      refine ⟨P - o, ⟨by unfold MatchAt at hP; simp only [q] at hP ⊢; omega, fun k hk => ?_⟩, by
        unfold anchorOf; congr 3; omega⟩
      rw [← heq _ (by simp only [q] at hk; omega), ← hP.2 k hk]; congr 1; omega
    · rintro ⟨p, hp, rfl⟩
      have hm : MatchAt G (o + p) R (j * q) := ⟨by have := hp.1; omega, fun k hk => by
        rw [Nat.add_assoc, heq _ (by have := hp.1; omega)]; exact hp.2 k hk⟩
      refine ⟨(hl.2 _).mpr ⟨_, hm, rfl⟩, ?_⟩
      have := hp.1
      unfold anchorOf
      simp only [BIAS, q] at hjq this ⊢
      generalize 2 ^ j = w at hw
      constructor <;> omega
  refine ⟨?_, fun e' => ?_⟩
  · rw [Array.toList_map, List.pairwise_map]
    refine hpx.imp_of_mem (fun {e1 e2} h1 h2 hlt => ?_)
    obtain ⟨p1, -, rfl⟩ := (key e1).mp h1
    obtain ⟨p2, -, rfl⟩ := (key e2).mp h2
    unfold anchorOf at hlt ⊢
    simp only [BIAS, q] at hjq hlt ⊢
    generalize 2 ^ j = w at hw hlt ⊢
    omega
  · rw [Array.toList_map, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨p, hp, rfl⟩ := (key e).mp he
      refine ⟨p, hp, ?_⟩
      unfold anchorOf; simp only [BIAS, q] at hjq ⊢
      generalize 2 ^ j = w at hw ⊢
      omega
    · rintro ⟨p, hp, rfl⟩
      refine ⟨_, (key _).mpr ⟨p, hp, rfl⟩, ?_⟩
      unfold anchorOf; simp only [BIAS, q] at hjq ⊢
      generalize 2 ^ j = w at hw ⊢
      omega

theorem catOk_spec (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (h : catOk G offs gbs = true)
    (c : Nat) (hc : c < gbs.size) : offs[c]! + gbs[c]!.size ≤ G.size ∧
      ∀ i, i < gbs[c]!.size → G.get! (offs[c]! + i) = gbs[c]!.get! i := by
  unfold catOk at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h c hc
  exact ⟨h1, fun i hi => by have := (eqRun_spec _ _ _ _ _).mp h2 i hi; simpa using this⟩

/-! ## One lookup on every chromosome -/

theorem lzStepA_empty (R G : ByteArray) (c k looked : Nat) (b : Best) :
    lzStepA R G c #[] k #[] looked b = (#[], b) := by
  have h1 : newOnly #[] #[] 0 0 #[] = #[] := by rw [newOnly]; simp
  have h2 : merge #[] #[] 0 0 #[] = #[] := by rw [merge]; simp
  unfold lzStepA
  simp only [h1, h2, Array.size_empty]
  split <;> rfl

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

theorem stepC_fold (a : Array Nat) (j J : Nat) (hj4 : j < 4) (hj0 : bit J j = 0)
    (hsl : ∀ c, c < gbs.size → LookOk gbs[c]! R j (sliceA a j offs[c]! gbs[c]!.size)) :
    ∀ (l : List Nat) (r : Array (Array Nat) × Best) (S : Window → Prop), l.Nodup → (∀ c ∈ l, c < gbs.size) →
      Inv cw S r.2 → r.1.size = gbs.size →
      (∀ c, c < gbs.size → c ∈ l → LoopState cw R gbs[c]! (base + c) J (pop4 J) r.1[c]! r.2 S) →
      (∀ c, c < gbs.size → c ∉ l →
        LoopState cw R gbs[c]! (base + c) (J + 2 ^ j) (pop4 J + 1) r.1[c]! r.2 S) →
      ∃ S', Inv cw S' (l.foldl (stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j)) r).2 ∧
        (∀ w, S w → S' w) ∧ (l.foldl (stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j)) r).2.pen ≤ r.2.pen ∧
        (l.foldl (stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j)) r).1.size = gbs.size ∧
        ∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) (J + 2 ^ j) (pop4 J + 1)
          (l.foldl (stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j)) r).1[c]!
          (l.foldl (stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j)) r).2 S' := by
  intro l
  induction l with
  | nil =>
    intro r S _ _ hi hsz _ hnew
    exact ⟨S, hi, fun w hw => hw, Nat.le_refl _, hsz, fun c hc => hnew c hc (by simp)⟩
  | cons c l ih =>
    intro r S hnd hl hi hsz hold hnew
    have hnd' := List.nodup_cons.mp hnd
    rw [List.foldl_cons]
    have hc : c < gbs.size := hl c List.mem_cons_self
    · -- the step on chromosome `c`
      obtain ⟨S2, hst, hS2⟩ := lzStepA_inv cw hc13 R gbs[c]! (base + c) (hcw c hc) hn j J _ (hsl c hc)
        r.1[c]! r.2 S (hold c hc List.mem_cons_self) hj4 hj0
      have hle := lzStepA_le R gbs[c]! (base + c) (sliceA a j offs[c]! gbs[c]!.size) (pop4 J) r.1[c]!
        (J + 2 ^ j) r.2
      have key : ∃ r' : Array (Array Nat) × Best, stepC1 R gbs offs base a j (pop4 J) (J + 2 ^ j) r c = r' ∧
          r'.2 = (lzStepA R gbs[c]! (base + c) (sliceA a j offs[c]! gbs[c]!.size) (pop4 J) r.1[c]!
            (J + 2 ^ j) r.2).2 ∧ r'.1.size = gbs.size ∧
          r'.1[c]! = (lzStepA R gbs[c]! (base + c) (sliceA a j offs[c]! gbs[c]!.size) (pop4 J) r.1[c]!
            (J + 2 ^ j) r.2).1 ∧ ∀ c', c' ≠ c → r'.1[c']! = r.1[c']! := by
        unfold stepC1
        simp only []
        split
        · next he =>
          simp only [Bool.and_eq_true, Array.isEmpty_iff] at he
          rw [he.1, he.2, lzStepA_empty]
          exact ⟨r, rfl, rfl, hsz, he.2, fun _ _ => rfl⟩
        · refine ⟨_, rfl, rfl, by simp [hsz], by rw [getElem!_set!']; simp [hsz, hc], fun c' hne => ?_⟩
          rw [getElem!_set!']; simp [Ne.symm hne]
      obtain ⟨r', hr', e2, esz, ec, eo⟩ := key
      rw [hr']
      rw [← e2] at hst hle
      rw [← ec] at hst
      obtain ⟨S', i', s', p', z', st'⟩ := ih r' S2 hnd'.2 (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) hst.inv esz
        (fun c' hc' hm => by
          have hne : c' ≠ c := fun e => hnd'.1 (e ▸ hm)
          rw [eo c' hne]; exact (hold c' hc' (List.mem_cons_of_mem _ hm)).mono hst.inv hS2 hle)
        (fun c' hc' hm => by
          by_cases e : c' = c
          · subst e; exact hst
          · rw [eo c' e]
            exact (hnew c' hc' (by simp [e, hm])).mono hst.inv hS2 hle)
      exact ⟨S', i', fun w hw => s' w (hS2 w hw), Nat.le_trans p' hle, z', st'⟩

/-- `stepC` takes every chromosome one lookup further. -/
theorem stepC_inv (a : Array Nat) (j J : Nat) (hj4 : j < 4) (hj0 : bit J j = 0)
    (hsl : ∀ c, c < gbs.size → LookOk gbs[c]! R j (sliceA a j offs[c]! gbs[c]!.size))
    (ass : Array (Array Nat)) (b : Best) (S : Window → Prop) (hi : Inv cw S b) (hsz : ass.size = gbs.size)
    (hs : ∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) J (pop4 J) ass[c]! b S) :
    ∃ S', Inv cw S' (stepC R gbs offs base a j (pop4 J) (J + 2 ^ j) ass b).2 ∧ (∀ w, S w → S' w) ∧
      (stepC R gbs offs base a j (pop4 J) (J + 2 ^ j) ass b).2.pen ≤ b.pen ∧
      (stepC R gbs offs base a j (pop4 J) (J + 2 ^ j) ass b).1.size = gbs.size ∧
      ∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) (J + 2 ^ j) (pop4 J + 1)
        (stepC R gbs offs base a j (pop4 J) (J + 2 ^ j) ass b).1[c]!
        (stepC R gbs offs base a j (pop4 J) (J + 2 ^ j) ass b).2 S' :=
  stepC_fold cw hc13 R gbs offs base hcw hn a j J hj4 hj0 hsl _ (ass, b) S List.nodup_range
    (fun _ h => List.mem_range.mp h) hi hsz (fun c hc _ => hs c hc)
    (fun _ hc h => absurd (List.mem_range.mpr hc) h)

/-- Strand state `s` (tags `base + c`) with best `b` and looked-at windows `S`. -/
def SC (s : CS) (b : Best) (S : Window → Prop) : Prop :=
  ∃ J, J < 16 ∧ s.k = pop4 J ∧ s.looked = J ∧ s.ord.Nodup ∧ (∀ j ∈ s.ord, j < 4 ∧ bit J j = 0) ∧
    pop4 J + s.ord.length = 4 ∧ Inv cw S b ∧ s.as.size = gbs.size ∧
    ∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) J (pop4 J) s.as[c]! b S

omit hc13 hcw hn in
theorem SC.mono {s : CS} {b b' : Best} {S S' : Window → Prop} (h : SC cw R gbs base s b S)
    (hi : Inv cw S' b') (hS : ∀ w, S w → S' w) (hb : b'.pen ≤ b.pen) : SC cw R gbs base s b' S' := by
  obtain ⟨J, h1, h2, h3, h4, h5, h6, -, h8, h9⟩ := h
  exact ⟨J, h1, h2, h3, h4, h5, h6, hi, h8, fun c hc => (h9 c hc).mono hi hS hb⟩

omit hc13 hcw hn in
theorem SC.inv {s : CS} {b : Best} {S : Window → Prop} (h : SC cw R gbs base s b S) : Inv cw S b := by
  obtain ⟨J, -, -, -, -, -, -, h7, -⟩ := h; exact h7

omit hc13 hcw hn in
theorem initC_ok {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (b : Best) (S : Window → Prop)
    (h : Inv cw S b) : SC cw R gbs base (CS.init lk ix (prepAll lk ix (seedHashes R)) gbs.size) b S := by
  obtain ⟨hnd, hlt, hl⟩ := seedOrder_spec lk ix (prepAll lk ix (seedHashes R))
  refine ⟨0, by decide, rfl, rfl, hnd, fun j hj => ⟨hlt j hj, by simp [bit]⟩, by simp [CS.init, hl, pop4], h,
    by simp [CS.init], fun c hc => ?_⟩
  have : (CS.init lk ix (prepAll lk ix (seedHashes R)) gbs.size).as[c]! = #[] := by
    simp only [CS.init]; rw [getElem!_pos _ c (by simp; exact hc)]; simp
  rw [this]
  exact ⟨h, anchorsM_init _ R, by omega, rfl, fun st hm => by simp [maskJ] at hm, fun h3 => by simp [pop4] at h3⟩

omit hc13 hcw hn in
theorem look_eq' {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (j : Nat) (hj : j < 4) :
    lk.look ix G R j (prepAll lk ix (seedHashes R))[j]! = lk.look ix G R j (lk.prep ix (seedHash R j)) := by
  rw [← seedHashes_get R j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- A lookup keeps the strand state. -/
theorem advC_ok {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (hsl : ∀ j, j < 4 → ∀ c, c < gbs.size →
      LookOk gbs[c]! R j (sliceA (lk.look ix G R j (lk.prep ix (seedHash R j))) j offs[c]! gbs[c]!.size))
    (s : CS) (b : Best) (S : Window → Prop) (h : SC cw R gbs base s b S) (hl : s.ord ≠ []) :
    ∃ S2, SC cw R gbs base (s.adv lk ix G R gbs offs base (prepAll lk ix (seedHashes R)) b).1
        (s.adv lk ix G R gbs offs base (prepAll lk ix (seedHashes R)) b).2 S2 ∧ (∀ w, S w → S2 w) ∧
      (s.adv lk ix G R gbs offs base (prepAll lk ix (seedHashes R)) b).2.pen ≤ b.pen ∧
      (s.adv lk ix G R gbs offs base (prepAll lk ix (seedHashes R)) b).1.ord.length + 1 = s.ord.length := by
  obtain ⟨J, hJ, hk, hlo, hnd, hord, hlen, hi, hsz, hs⟩ := h
  rcases s with ⟨_ | ⟨j, rest⟩, k, looked, as⟩
  · exact absurd rfl hl
  simp only at hk hlo hnd hord hlen hs hsz
  subst k looked
  obtain ⟨hj4, hj0⟩ := hord j List.mem_cons_self
  obtain ⟨hpop, hJ'⟩ := pop4_add J hJ j hj4 hj0
  have hnd' := List.nodup_cons.mp hnd
  simp only [CS.adv]
  rw [look_eq' R lk ix G j hj4, pow2_eq j hj4]
  obtain ⟨S2, i2, s2, p2, z2, st2⟩ := stepC_inv cw hc13 R gbs offs base hcw hn _ j J hj4 hj0 (hsl j hj4)
    as b S hi hsz hs
  refine ⟨S2, ⟨J + 2 ^ j, hJ', hpop.symm, rfl, hnd'.2, fun j' hj' => ?_, by simp at hlen ⊢; omega, i2, z2,
    fun c hc => by rw [hpop]; exact st2 c hc⟩, s2, p2, rfl⟩
  obtain ⟨a1, a2⟩ := hord j' (List.mem_cons_of_mem _ hj')
  refine ⟨a1, ?_⟩
  rw [bit_add J j j' hj4 a1 hJ hj0, if_neg (fun e : j' = j => hnd'.1 (e ▸ hj'))]; exact a2

/-- A strand that is not live has looked at every hit of its tags. -/
theorem deadC_cover (s : CS) (b : Best) (S : Window → Prop) (h : SC cw R gbs base s b S)
    (hd : s.live b = false) :
    ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧
      ∀ c, c < gbs.size → ∀ st len, cw ⟨base + c, st, len⟩ ≤ 12 → S' ⟨base + c, st, len⟩ := by
  obtain ⟨J, hJ, hk, -, -, -, hlen, hi, -, hs⟩ := h
  have hstop : b.pen < 4 * pop4 J ∨ J = 15 := by
    unfold CS.live at hd
    cases ho : s.ord with
    | nil => rw [ho] at hlen; exact Or.inr (pop4_full J hJ (by simpa using hlen))
    | cons j rest => rw [ho] at hd; simp at hd; omega
  have go : ∀ (l : List Nat) (S : Window → Prop), (∀ c ∈ l, c < gbs.size) → Inv cw S b →
      (∀ c, c < gbs.size → LoopState cw R gbs[c]! (base + c) J (pop4 J) s.as[c]! b S) →
      ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧
        ∀ c ∈ l, ∀ st len, cw ⟨base + c, st, len⟩ ≤ 12 → S' ⟨base + c, st, len⟩ := by
    intro l
    induction l with
    | nil => intro S _ hi _; exact ⟨S, hi, fun w hw => hw, fun c hc => by simp at hc⟩
    | cons c l ih =>
      intro S hl hi hs
      have hc := hl c List.mem_cons_self
      obtain ⟨S1, i1, s1, v1⟩ := finish cw hc13 R gbs[c]! (base + c) (hcw c hc) hn J _ _ b S (hs c hc) hstop
      obtain ⟨S2, i2, s2, v2⟩ := ih S1 (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) i1
        (fun c' hc' => (hs c' hc').mono i1 s1 (Nat.le_refl _))
      refine ⟨S2, i2, fun w hw => s2 w (s1 w hw), fun c' hc' st len hw => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact s2 _ (v1 st len hw)
      · exact v2 c' hc' st len hw
  obtain ⟨S', i', s', v'⟩ := go (List.range gbs.size) S (fun c h => List.mem_range.mp h) hi hs
  exact ⟨S', i', s', fun c hc => v' c (List.mem_range.mpr hc)⟩

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

omit [Inhabited P] hsl1 hsl2 in
/-- Both strands dead: every hit of all their tags was looked at. -/
theorem bothC_dead (s1 s2 : CS) (b : Best) (S : Window → Prop) (h1 : SC cw R1 gbs c1 s1 b S)
    (h2 : SC cw R2 gbs c2 s2 b S) (d1 : s1.live b = false) (d2 : s2.live b = false) :
    ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧
      (∀ c, c < gbs.size → ∀ st len, cw ⟨c1 + c, st, len⟩ ≤ 12 → S' ⟨c1 + c, st, len⟩) ∧
      (∀ c, c < gbs.size → ∀ st len, cw ⟨c2 + c, st, len⟩ ≤ 12 → S' ⟨c2 + c, st, len⟩) := by
  obtain ⟨S1, i1, s1', v1⟩ := deadC_cover cw hc13 R1 gbs c1 hcw1 hn1 s1 b S h1 d1
  obtain ⟨S2, i2, s2', v2⟩ := deadC_cover cw hc13 R2 gbs c2 hcw2 hn2 s2 b S1
    (h2.mono cw R2 gbs c2 i1 s1' (Nat.le_refl _)) d2
  exact ⟨S2, i2, fun w hw => s2' _ (s1' _ hw), fun c hc st len hw => s2' _ (v1 c hc st len hw), v2⟩

theorem ilC_inv : ∀ (f : Nat) (s1 s2 : CS) (b : Best) (S : Window → Prop),
    SC cw R1 gbs c1 s1 b S → SC cw R2 gbs c2 s2 b S → s1.ord.length + s2.ord.length ≤ f →
    ∃ S', Inv cw S' (ilC lk ix G gbs offs R1 R2 c1 c2 (prepAll lk ix (seedHashes R1))
        (prepAll lk ix (seedHashes R2)) f s1 s2 b) ∧ (∀ w, S w → S' w) ∧
      (∀ c, c < gbs.size → ∀ st len, cw ⟨c1 + c, st, len⟩ ≤ 12 → S' ⟨c1 + c, st, len⟩) ∧
      (∀ c, c < gbs.size → ∀ st len, cw ⟨c2 + c, st, len⟩ ≤ 12 → S' ⟨c2 + c, st, len⟩) := by
  have dead : ∀ (s : CS) b, s.ord.length = 0 → s.live b = false := fun s b h => by
    simp [CS.live, List.length_eq_zero_iff.mp h]
  have ne : ∀ (s : CS) b, s.live b = true → s.ord ≠ [] := fun s b h e => by simp [CS.live, e] at h
  intro f
  induction f with
  | zero =>
    intro s1 s2 b S h1 h2 hf
    exact bothC_dead cw hc13 gbs R1 R2 c1 c2 hcw1 hn1 hcw2 hn2 s1 s2 b S h1 h2
      (dead s1 b (by omega)) (dead s2 b (by omega))
  | succ f ih =>
    intro s1 s2 b S h1 h2 hf
    unfold ilC
    simp only []
    split
    · next hc =>
      have hl1 : s1.live b = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
      obtain ⟨S2, k1, hS, hp, hlen⟩ := advC_ok cw hc13 R1 gbs offs c1 hcw1 hn1 lk ix G hsl1 s1 b S h1
        (ne s1 b hl1)
      obtain ⟨S', i', s', cv⟩ := ih _ s2 _ S2 k1 (h2.mono cw R2 gbs c2 (k1.inv cw R1 gbs c1) hS hp)
        (by omega)
      exact ⟨S', i', fun w hw => s' _ (hS _ hw), cv⟩
    · next hc =>
      split
      · next hl2 =>
        obtain ⟨S2, k2, hS, hp, hlen⟩ := advC_ok cw hc13 R2 gbs offs c2 hcw2 hn2 lk ix G hsl2 s2 b S h2
          (ne s2 b hl2)
        obtain ⟨S', i', s', cv⟩ := ih s1 _ _ S2 (h1.mono cw R1 gbs c1 (k2.inv cw R2 gbs c2) hS hp) k2
          (by omega)
        exact ⟨S', i', fun w hw => s' _ (hS _ hw), cv⟩
      · next hl2 =>
        have hl2' : s2.live b = false := by simpa using hl2
        have hl1 : s1.live b = false := by
          cases e : s1.live b
          · rfl
          · exact absurd (by simp [e, hl2']) hc
        exact bothC_dead cw hc13 gbs R1 R2 c1 c2 hcw1 hn1 hcw2 hn2 s1 s2 b S h1 h2
          hl1 hl2'

end two

/-! ## Top theorems -/

/-- Every chromosome, both strands: the invariant over all virtual windows. -/
theorem mapChromsC_inv {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (rf : Bool) (hn : 100 ≤ R.size) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j)))) :
    ∃ S, Inv (cwJ R gbs) S (mapChromsC lk ix G offs gbs R rf) ∧ ∀ w, cwJ R gbs w ≤ 12 → S w := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have hsl : ∀ R' : ByteArray, ∀ j, j < 4 → ∀ c, c < gbs.size →
      LookOk gbs[c]! R' j (sliceA (lk.look ix G R' j (lk.prep ix (seedHash R' j))) j offs[c]! gbs[c]!.size) :=
    fun R' j hj c hc => sliceA_ok G gbs[c]! R' offs[c]! j hj _ (hlk R' j hj) (catOk_spec G offs gbs hcat c hc).1
      (catOk_spec G offs gbs hcat c hc).2
  have cf : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨0 + c, st, len⟩ = penB R gbs[c]! st len :=
    fun c hc st len => by unfold cwJ cwG; simp [hc]
  have cr : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨gbs.size + c, st, len⟩ = penB (revCompB R) gbs[c]! st len :=
    fun c hc st len => by
      unfold cwJ cwG
      simp [hc, show ¬ gbs.size + c < gbs.size by omega, show gbs.size + c < 2 * gbs.size by omega]
  have i0 := inv_init _ (cwJ_le R gbs)
  have cover : ∀ S : Window → Prop,
      (∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨0 + c, st, len⟩ ≤ 12 → S ⟨0 + c, st, len⟩) →
      (∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨gbs.size + c, st, len⟩ ≤ 12 → S ⟨gbs.size + c, st, len⟩) →
      ∀ w, cwJ R gbs w ≤ 12 → S w := by
    intro S vf vr ⟨c, st, len⟩ hw
    by_cases hc : c < gbs.size
    · have := vf c hc st len; simp only [Nat.zero_add] at this; exact this hw
    · by_cases hc2 : c < 2 * gbs.size
      · have := vr (c - gbs.size) (by omega) st len
        rw [show gbs.size + (c - gbs.size) = c by omega] at this
        exact this hw
      · unfold cwJ at hw; simp [hc, hc2] at hw
  unfold mapChromsC
  cases rf with
  | false =>
    obtain ⟨S, i, -, vf, vr⟩ := ilC_inv (cwJ R gbs) (cwJ_le R gbs) lk ix G gbs offs R (revCompB R) 0 gbs.size
      cf hn (hsl R) cr hrn (hsl _) 8 _ _ {} (fun _ => False)
      (initC_ok (cwJ R gbs) R gbs 0 lk ix {} _ i0) (initC_ok (cwJ R gbs) _ gbs gbs.size lk ix {} _ i0)
      (by simp [CS.init, (seedOrder_spec lk ix (prepAll lk ix (seedHashes R))).2.2,
        (seedOrder_spec lk ix (prepAll lk ix (seedHashes (revCompB R)))).2.2])
    exact ⟨S, i, cover S vf vr⟩
  | true =>
    obtain ⟨S, i, -, vr, vf⟩ := ilC_inv (cwJ R gbs) (cwJ_le R gbs) lk ix G gbs offs (revCompB R) R gbs.size 0
      cr hrn (hsl _) cf hn (hsl R) 8 _ _ {} (fun _ => False)
      (initC_ok (cwJ R gbs) _ gbs gbs.size lk ix {} _ i0) (initC_ok (cwJ R gbs) R gbs 0 lk ix {} _ i0)
      (by simp [CS.init, (seedOrder_spec lk ix (prepAll lk ix (seedHashes R))).2.2,
        (seedOrder_spec lk ix (prepAll lk ix (seedHashes (revCompB R)))).2.2])
    exact ⟨S, i, cover S vf vr⟩

theorem mapFastC_eq_mapSpecBoth {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (offs : Array Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (rf : Bool)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hok : fastOk R = true) : mapFastC lk ix G offs gbs R rf = mapSpecBoth sc0 (-12) g read :=
  decodeJ_eq_mapSpecBoth g read gbs R _ hg hr (mapChromsC_inv lk ix G offs gbs R rf
    (by unfold fastOk q at hok; simp at hok; omega) hcat hlk)

theorem pairFastC_eq_pairSpec {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastC lk lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold pairFastC pairSpec
  rw [mapFastC_eq_mapSpecBoth lk ix G offs g m1 gbs R1 false hg h1 hcat hlk hok1]
  cases mapSpecBoth sc0 (-12) g m1 with
  | none => rfl
  | some a =>
    simp only
    rw [mapFastC_eq_mapSpecBoth lk ix G offs g m2 gbs R2 _ hg h2 hcat hlk hok2]
    cases mapSpecBoth sc0 (-12) g m2 <;> rfl

/-- Through the hashed index over the concatenation, checked at run time. -/
theorem pairFastC_hashed_eq_pairSpec (lo hi : Nat) (ix : HIdx) (G : ByteArray) (offs : Array Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true) (hchk : checkIdx ix G = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastC hLook lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 :=
  pairFastC_eq_pairSpec hLook lo hi ix G offs g m1 m2 gbs R1 R2 hg h1 h2 hcat
    (fun R' j hj => hLook_ok ix G R' j hj hchk) hok1 hok2

/-- Through the minimizer index over the concatenation, checked at run time. -/
theorem pairFastC_mz_eq_pairSpec (lo hi : Nat) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true) (hchk : Mz.check2 ix G = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastC mzL lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 :=
  pairFastC_eq_pairSpec mzL lo hi ix G offs g m1 m2 gbs R1 R2 hg h1 h2 hcat
    (fun R' j hj => mzLook_ok ix G R' j hj (by rw [← Mz.check2_eq]; exact hchk)) hok1 hok2

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastC_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastC_eq_pairSpec
#print axioms MapSpec.Fast.pairFastC_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastC_mz_eq_pairSpec
