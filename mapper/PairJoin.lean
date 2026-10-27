import PairReason

/-!
# Codec `noPairJ`: no proper pair of hits, from the seed anchors of both mates

A pair is reported only when both mates map uniquely **and** form a proper pair, so if no
hit of mate 1 (cap `P1`) and hit of mate 2 (cap `P2`) form a proper pair, the pair is
`none` whatever the mates' own answers (reason `noPair`, `ReasonOk`).

On the fast path (`fastT`) every hit of a read contains a clean seed (`coverLE`, all
seeds looked up), so it lies on the diagonal of one of the read's anchors: with
`x = p + (n - j·Ls)` for an anchor of seed `j` at genome place `p` (global coordinates of
the concatenated genome), the hit's window starts at `x - n - a` with a shape `|a| + |b| ≤
gapBound`.  A proper pair puts the forward mate's window and the reverse mate's window
within the fragment bound `hi`, so their anchors are within
`W = hi + n1 + n2 + 2 gapBound(P1) + 2 gapBound(P2)`.

`noPairJ` merges each strand's anchors (sorted) and checks the two facing strand pairs
(mate 1 forward / mate 2 reverse, mate 1 reverse / mate 2 forward) with a merge join
(`nearAnyF`): no two anchors within `W` → `noPairJ_ok`: no proper pair of hits.  No
alignment is computed; repeat-heavy mates whose anchors never meet are settled from
their lookups alone.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Merge join of two sorted lists -/

/-- Some `x ∈ xs` within `W` of some `y ∈ ys` (both sorted); `true` when out of fuel
(only `false` is used). -/
def nearAnyF (W : Nat) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => true
  | _ + 1, [], _ => false
  | _ + 1, _ :: _, [] => false
  | f + 1, x :: xs, y :: ys =>
    if x + W < y then nearAnyF W f xs (y :: ys)
    else if y + W < x then nearAnyF W f (x :: xs) ys
    else true

theorem nearAnyF_false (W : Nat) : ∀ (f : Nat) (xs ys : List Nat), xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) →
    nearAnyF W f xs ys = false → ∀ x ∈ xs, ∀ y ∈ ys, x + W < y ∨ y + W < x := by
  intro f
  induction f with
  | zero => intro xs ys _ _ h; simp [nearAnyF] at h
  | succ f ih =>
    intro xs ys hx hy h
    match xs, ys with
    | [], _ => intro x hx; cases hx
    | _ :: _, [] => intro x _ y hy; cases hy
    | x0 :: xs, y0 :: ys =>
      unfold nearAnyF at h
      rw [List.pairwise_cons] at hx hy
      by_cases h1 : x0 + W < y0
      · rw [if_pos h1] at h
        have ih' := ih xs (y0 :: ys) hx.2 (List.pairwise_cons.2 hy) h
        intro x hxm y hym
        rcases List.mem_cons.1 hxm with rfl | hxm
        · left
          rcases List.mem_cons.1 hym with rfl | hym
          · exact h1
          · have := hy.1 y hym; omega
        · exact ih' x hxm y hym
      · rw [if_neg h1] at h
        by_cases h2 : y0 + W < x0
        · rw [if_pos h2] at h
          have ih' := ih (x0 :: xs) ys (List.pairwise_cons.2 hx) hy.2 h
          intro x hxm y hym
          rcases List.mem_cons.1 hym with rfl | hym
          · right
            rcases List.mem_cons.1 hxm with rfl | hxm
            · exact h2
            · have := hx.1 x hxm; omega
          · exact ih' x hxm y hym
        · rw [if_neg h2] at h; cases h

/-! ## Anchors of every seed -/

/-- Diagonal ends `p + (n - j·Ls)` of the anchors of every seed `j` of `R` (sorted). -/
def anchAll {L Pp : Type} [LookG L Pp] (ix : L) (G R : ByteArray) : List Nat :=
  let m := R.size / 25
  let Ls := R.size / m
  (List.range m).foldl (fun acc j => List.merge acc
    ((LookG.look ix G R (j * Ls) (R.size - j * Ls) (LookG.prep ix (seedHashAt R (j * Ls)))).toList.map (· / 16))
    (fun a b => decide (a ≤ b))) []

/-- The anchor window bound of a pair: fragment bound, both lengths, both gap bounds. -/
def joinW (P1 P2 hi n1 n2 : Nat) : Nat :=
  hi + n1 + n2 + 2 * gapBound sc0 (-(P1 : Int)) + 2 * gapBound sc0 (-(P2 : Int))

/-- **No proper pair of hits** (both mates on the fast path at their caps): the anchors
of facing strands never come within `joinW`. -/
def noPairJ {L Pp : Type} [LookG L Pp] (P1 P2 hi : Nat) (ix : L) (G R1 R2 : ByteArray) : Bool :=
  fastT P1 R1 && fastT P2 R2 &&
    (let W := joinW P1 P2 hi R1.size R2.size
     let f1 := anchAll ix G R1
     let r2 := anchAll ix G (revCompK R2)
     !nearAnyF W (f1.length + r2.length + 1) f1 r2 &&
       (let r1 := anchAll ix G (revCompK R1)
        let f2 := anchAll ix G R2
        !nearAnyF W (r1.length + f2.length + 1) r1 f2))

/-! ## Proofs -/

section fold
variable (F : Nat → List Nat)

theorem foldMerge_mem : ∀ (l acc : List Nat) (x : Nat), (x ∈ acc ∨ ∃ j ∈ l, x ∈ F j) →
    x ∈ l.foldl (fun acc j => List.merge acc (F j) (fun a b => decide (a ≤ b))) acc := by
  intro l
  induction l with
  | nil => intro acc x h; rcases h with h | ⟨j, hj, -⟩; exact h; cases hj
  | cons j0 l ih =>
    intro acc x h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨j, hj, hx⟩
    · exact Or.inl (List.mem_merge.2 (Or.inl h))
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact Or.inl (List.mem_merge.2 (Or.inr hx))
      · exact Or.inr ⟨j, hj, hx⟩

theorem foldMerge_sorted : ∀ (l acc : List Nat), (∀ j ∈ l, (F j).Pairwise (· ≤ ·)) → acc.Pairwise (· ≤ ·) →
    (l.foldl (fun acc j => List.merge acc (F j) (fun a b => decide (a ≤ b))) acc).Pairwise (· ≤ ·) := by
  intro l
  induction l with
  | nil => intro acc _ h; exact h
  | cons j l ih =>
    intro acc hF h
    simp only [List.foldl_cons]
    apply ih _ (fun j' hj' => hF j' (List.mem_cons_of_mem _ hj'))
    have hm := List.pairwise_merge (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) acc (F j)
      (h.imp fun {a b} hab => by simp only [decide_eq_true_eq]; exact hab)
      ((hF j (List.mem_cons_self ..)).imp fun {a b} hab => by simp only [decide_eq_true_eq]; exact hab)
    exact hm.imp fun {a b} hab => by simpa using hab

end fold

section anch
variable {L Pp : Type} [LookG L Pp] (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)
  (g : Genome) (hg : GenomeBytes gbs g) (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

include hlk in
theorem anchAll_sorted (R : ByteArray) (hm : 0 < R.size / 25) : (anchAll ix G R).Pairwise (· ≤ ·) := by
  unfold anchAll
  apply foldMerge_sorted _ _ _ _ List.Pairwise.nil
  intro j hj
  rw [List.mem_range] at hj
  have hl := hlk R (j * (R.size / (R.size / 25))) (R.size - j * (R.size / (R.size / 25)))
    (seed_fits R.size j hm hj)
  rw [List.pairwise_map]
  exact hl.1.imp fun {a b} hab => Nat.div_le_div_right (Nat.le_of_lt hab)

include hg hcat hlk in
/-- **Every hit lies on an anchor's diagonal**: a window of score `≥ −P` (fast path)
has an anchor `x` (global coordinates) with `x = offs[c] + start + a + n`,
`len = n + a + b`, `|a| + |b| ≤ gapBound`. -/
theorem anch_of_hit (P : Nat) (read : List Char) (R : ByteArray) (hr : Encodes R read) (hf : fastT P R = true)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) (hS : -(P : Int) ≤ s) :
    ∃ x ∈ anchAll ix G R, ∃ a b : Int, a.natAbs + b.natAbs ≤ gapBound sc0 (-(P : Int)) ∧
      (x : Int) = (offs[w.chr]! : Int) + w.start + a + R.size ∧ (w.len : Int) = R.size + a + b := by
  unfold fastT at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hm, hsb⟩ := hf
  have hn : R.size = read.length := hr.1
  generalize hM : R.size / 25 = m at hm hsb
  have hk1 : m - 1 + 1 = m := by omega
  have hLs : read.length / (m - 1 + 1) = R.size / m := by rw [hk1, hn]
  have h25 := le_div_seeds R.size (by omega)
  rw [hM] at h25
  obtain ⟨j, hj, p, a, b, hc, hmatch, hshape, ha1, hnn, hst, hwl⟩ :=
    coverLE g read gbs R hg hr (-(P : Int)) q (by decide) (m - 1) (by rw [hLs]; exact h25)
      (by rw [hLs]; have : q = 25 := rfl; omega)
      (List.range m) List.nodup_range (fun j hj => by rw [List.mem_range] at hj; omega)
      (by rw [List.length_range, ← sbound_def]; exact hsb) w s hs hS
  rw [hLs] at hmatch ha1 hst
  rw [← hn] at hwl
  rw [List.mem_range] at hj
  generalize hL : R.size / m = Ls at hmatch ha1 hst
  have hfit : j * Ls + q ≤ R.size := by
    have := seed_fits R.size j (by omega) (by omega); rw [hM, hL] at this; exact this
  -- the place in the concatenated genome
  obtain ⟨hcs, hce⟩ := catOk_spec G offs gbs hcat w.chr hc
  have hmG : MatchAt G (offs[w.chr]! + p) R (j * Ls) := ⟨by have := hmatch.1; omega, fun k hk => by
    rw [Nat.add_assoc, hce _ (by have := hmatch.1; omega)]; exact hmatch.2 k hk⟩
  have hl := hlk R (j * Ls) (R.size - j * Ls) hfit
  have he : (offs[w.chr]! + p + (R.size - j * Ls)) * 16 + 0 ∈
      (LookG.look ix G R (j * Ls) (R.size - j * Ls) (LookG.prep ix (seedHashAt R (j * Ls)))).toList :=
    (hl.2 _).mpr ⟨_, hmG, rfl⟩
  refine ⟨offs[w.chr]! + p + (R.size - j * Ls), ?_, a, b, hshape.1, ?_, ?_⟩
  · unfold anchAll
    simp only [hM, hL]
    apply foldMerge_mem
    right
    refine ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨_, he, by omega⟩⟩
  · have : q = 25 := rfl
    omega
  · omega

end anch

section main
variable {L Pp : Type} [LookG L Pp] (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)
  (g : Genome) (hg : GenomeBytes gbs g) (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

theorem fastT_size (P : Nat) (R R' : ByteArray) (h : R'.size = R.size) : fastT P R' = fastT P R := by
  unfold fastT; rw [h]

theorem revCompK_encodes (R : ByteArray) (read : List Char) (h : Encodes R read) :
    Encodes (revCompK R) (revComp read) := by
  rw [revCompK_eq]; exact revCompB_encodes R read h

theorem revCompK_size (R : ByteArray) (read : List Char) (h : Encodes R read) : (revCompK R).size = R.size := by
  have h1 := (revCompK_encodes R read h).1
  rw [h1, h.1]; simp [revComp]

theorem absB (a : Int) : a ≤ (a.natAbs : Int) ∧ -a ≤ (a.natAbs : Int) := by
  refine ⟨Int.le_natAbs, ?_⟩
  have := @Int.le_natAbs (-a); rw [Int.natAbs_neg] at this; exact this

set_option maxHeartbeats 1000000 in
include hg hcat hlk in
/-- **`noPairJ` proves `noPair`**: no hit of mate 1 (cap `P1`) and hit of mate 2 (cap
`P2`) form a proper pair. -/
theorem noPairJ_ok (lo hi P1 P2 : Nat) (m1 m2 : List Char) (R1 R2 : ByteArray) (h1 : Encodes R1 m1)
    (h2 : Encodes R2 m2) (h : noPairJ P1 P2 hi ix G R1 R2 = true) :
    ∀ a ∈ hitsBoth sc0 (-(P1 : Int)) g m1, ∀ b ∈ hitsBoth sc0 (-(P2 : Int)) g m2,
      properPair lo hi a.1 b.1 = false := by
  unfold noPairJ at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hf1, hf2⟩, hj1, hj2⟩ := h
  have hm1 : 0 < R1.size / 25 := by unfold fastT at hf1; simp at hf1; omega
  have hm2 : 0 < R2.size / 25 := by unfold fastT at hf2; simp at hf2; omega
  have hs1 := revCompK_size R1 m1 h1
  have hs2 := revCompK_size R2 m2 h2
  have hfr1 : fastT P1 (revCompK R1) = true := by rw [fastT_size P1 R1 _ hs1]; exact hf1
  have hfr2 : fastT P2 (revCompK R2) = true := by rw [fastT_size P2 R2 _ hs2]; exact hf2
  have hmr1 : 0 < (revCompK R1).size / 25 := by rw [hs1]; exact hm1
  have hmr2 : 0 < (revCompK R2).size / 25 := by rw [hs2]; exact hm2
  have hd1 := nearAnyF_false _ _ _ _ (anchAll_sorted ix G hlk R1 hm1) (anchAll_sorted ix G hlk _ hmr2) hj1
  have hd2 := nearAnyF_false _ _ _ _ (anchAll_sorted ix G hlk _ hmr1) (anchAll_sorted ix G hlk R2 hm2) hj2
  intro ⟨⟨w1, st1⟩, s1⟩ ha ⟨⟨w2, st2⟩, s2⟩ hb
  rw [mem_hitsBoth_T] at ha hb
  obtain ⟨-, hsa, hTa⟩ := ha
  obtain ⟨-, hsb, hTb⟩ := hb
  apply Classical.byContradiction
  intro hp
  simp only [Bool.not_eq_false] at hp
  unfold joinW at hd1 hd2
  cases st1 <;> cases st2
  · simp [properPair] at hp
  · -- mate 1 forward, mate 2 reverse
    simp only [properPair, if_true, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨⟨hc, -⟩, -⟩, hle⟩, -⟩, hhi⟩ := hp
    obtain ⟨x1, hx1, a1, b1, hab1, hx1e, -⟩ :=
      anch_of_hit ix G offs gbs g hg hcat hlk P1 m1 R1 h1 hf1 w1 s1 hsa hTa
    obtain ⟨x2, hx2, a2, b2, hab2, hx2e, hl2⟩ :=
      anch_of_hit ix G offs gbs g hg hcat hlk P2 (revComp m2) (revCompK R2) (revCompK_encodes R2 m2 h2) hfr2
        w2 s2 hsb hTb
    rw [hs2] at hx2e hl2
    rw [← hc] at hx2e
    have := hd1 x1 hx1 x2 hx2
    have := absB a1; have := absB b1; have := absB a2; have := absB b2
    generalize a1.natAbs = A1 at *; generalize b1.natAbs = B1 at *
    generalize a2.natAbs = A2 at *; generalize b2.natAbs = B2 at *
    omega
  · -- mate 1 reverse, mate 2 forward
    simp only [properPair, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [reduceCtorEq, if_false, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨⟨hc, -⟩, -⟩, hle⟩, -⟩, hhi⟩ := hp
    obtain ⟨x1, hx1, a1, b1, hab1, hx1e, hl1⟩ :=
      anch_of_hit ix G offs gbs g hg hcat hlk P1 (revComp m1) (revCompK R1) (revCompK_encodes R1 m1 h1) hfr1
        w1 s1 hsa hTa
    obtain ⟨x2, hx2, a2, b2, hab2, hx2e, -⟩ :=
      anch_of_hit ix G offs gbs g hg hcat hlk P2 m2 R2 h2 hf2 w2 s2 hsb hTb
    rw [hs1] at hx1e hl1
    rw [hc] at hx2e
    have := hd2 x1 hx1 x2 hx2
    have := absB a1; have := absB b1; have := absB a2; have := absB b2
    generalize a1.natAbs = A1 at *; generalize b1.natAbs = B1 at *
    generalize a2.natAbs = A2 at *; generalize b2.natAbs = B2 at *
    omega
  · simp [properPair] at hp

end main

end MapSpec.Fast

#print axioms MapSpec.Fast.nearAnyF_false
#print axioms MapSpec.Fast.anch_of_hit
#print axioms MapSpec.Fast.noPairJ_ok
