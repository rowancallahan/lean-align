import Proofs.Shift

/-! # What the minimizer builder makes (`Index.buildMz` with k=22, B=26, c=0, 5-byte slots, t=6)

Both branches are `buildW` on the genome's bytes (`buildWV_eq`, `buildWP_eq'`). `buildW_ok`: on a
genome of `N < 2^32` letters it does not panic, the bucket offsets are `4 (2^26 + 1)` bytes of
prefix sums `≤ total ≤ N`, the slots are `5 · total` bytes, the runs are `≤ N` (at most `2N`), and
every small field fits 64 bits (`BuiltOk`). -/
open MapSpec MapSpec.Mz

namespace Spec.Build
open MapSpec.Fast (PGen Rep)

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem allAP_eq (stop : Nat) : ∀ d i, stop - i = d → allAP P i stop = allA G i stop := by
  intro d
  induction d with
  | zero => intro i hd; unfold allAP allA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i hd
    unfold allAP allA
    simp only [show i < stop from by omega, if_true, h.2, ih (i + 1) (by omega)]

theorem wcGoP_eq (stop : Nat) : ∀ d i x, stop - i = d → wcGoP P i stop x = wcGo G i stop x := by
  intro d
  induction d with
  | zero => intro i x hd; unfold wcGoP wcGo; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i x hd
    unfold wcGoP wcGo
    have ih' := fun x => ih (i + 1) x (by omega)
    simp only [show i < stop from by omega, if_true, h.2, ih']

theorem slotAtP_eq (ix : MzIdx) (pm hh : Nat) : slotAtP ix P pm hh = slotAt ix G pm hh := by
  simp only [slotAtP, slotAt, h.1, fun i stop => allAP_eq h stop _ i rfl, fun i stop x => wcGoP_eq h stop _ i x rfl]

theorem foldMinsP_eq' {α : Type} (ix0 : MzIdx) (f : α → Nat → Nat → α) :
    ∀ d p x good last acc, G.size - p = d →
      foldMinsP ix0 P f p x good last acc = foldMinsGo ix0 G f p x good last acc := by
  intro d
  induction d with
  | zero =>
    intro p x good last acc hd
    unfold foldMinsP foldMinsGo; rw [h.1, if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro p x good last acc hd
    unfold foldMinsP foldMinsGo
    have ih' := fun x good last acc => ih (p + 1) x good last acc (by omega)
    simp only [h.1, show p < G.size from by omega, if_true, h.2, ih']

/-- **The builder over a packed genome is `buildW` on the bytes it spells.** -/
theorem buildWP_eq' (k B c sw t : Nat) : buildWP P k B c sw t = buildW G k B c sw t := by
  simp only [buildWP, buildW, foldMins, h.1, h.2, foldMinsP_eq' h _ _ _ 0 0 0 0 _ rfl, slotAtP_eq h,
    panicWithPosWithDecl, panic, panicCore]

end


def ix0 (G : ByteArray) : MzIdx := mkIdx 22 26 0 5 (G.size.log2 + 1) 6

def cnt1 (G : ByteArray) : ByteArray :=
  foldMins (ix0 G) G (zeros (4 * (2 ^ 26 + 1))) fun cnt _ h =>
    setU32 cnt (h >>> (ix0 G).kb + 1) (getU32 cnt (h >>> (ix0 G).kb + 1) + 1)

def cnt2 (G : ByteArray) : ByteArray :=
  (List.range (2 ^ 26)).foldl (fun cnt b => setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)) (cnt1 G)

def slB (G : ByteArray) : ByteArray :=
  (foldMins (ix0 G) G (cnt2 G, zeros (5 * getU32 (cnt2 G) (2 ^ 26))) fun (fill, sl) pm h =>
    (setU32 fill (h >>> (ix0 G).kb) (getU32 fill (h >>> (ix0 G).kb) + 1),
      wrLE sl (5 * getU32 fill (h >>> (ix0 G).kb)) (slotAt (ix0 G) G pm h) 5)).2

def runStep (G : ByteArray) (runs : Array Nat) (p : Nat) : Array Nat :=
  let odd := !acgt (G.get! p)
  let runs := if (odd && (p == 0 || acgt (G.get! (p - 1)))) = true then runs.push p else runs
  if (odd && (p + 1 == G.size || acgt (G.get! (p + 1)))) = true then runs.push (p + 1) else runs

def runsB (G : ByteArray) : Array Nat := (List.range G.size).foldl (runStep G) #[]

theorem log2_le (n : Nat) (hN : n < 2 ^ 39) : n.log2 + 1 ≤ 39 := by
  by_cases h0 : n = 0
  · subst h0; rw [Nat.log2_zero]; omega
  · have := (Nat.log2_lt (n := n) (k := 39) h0).2 hN; omega

theorem buildW_eq (G : ByteArray) (hN : G.size < 2 ^ 39) :
    buildW G 22 26 0 5 6 = { ix0 G with offs := cnt2 G, sl := slB G, runs := runsB G } := by
  have hpb := log2_le G.size hN
  have hc : ¬ ((decide (2 * 22 < 26) || decide (32 < 26) || decide (22 = 0) || decide (q < 22) || decide (q - 22 < 0) ||
      decide (6 = 0) || decide (22 < 6) || (22 - 6) % (q + 1 - 22) != 0 ||
      !(decide (5 = 4) || decide (5 = 5) || decide (5 = 6) || decide (5 = 8)) ||
      decide (8 * 5 < G.size.log2 + 1 + 4 * 0 + 1)) = true) := by
    simp only [q]; simp; omega
  unfold buildW
  dsimp only
  rw [if_neg hc]
  have body : (fun (p : Nat) (r : Array Nat) =>
      (if (!acgt (G.get! p) && (p == 0 || acgt (G.get! (p - 1)))) = true then
        if (!acgt (G.get! p) && (p + 1 == G.size || acgt (G.get! (p + 1)))) = true then
          pure (ForInStep.yield ((r.push p).push (p + 1)))
        else pure (ForInStep.yield (r.push p))
      else
        if (!acgt (G.get! p) && (p + 1 == G.size || acgt (G.get! (p + 1)))) = true then
          pure (ForInStep.yield (r.push (p + 1)))
        else pure (ForInStep.yield r) : Id (ForInStep (Array Nat)))) =
      fun p r => pure (ForInStep.yield (runStep G r p)) := by
    funext p r; unfold runStep; dsimp only
    split <;> split <;> rename_i h1 h2 <;> simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.range'_eq_map_range, List.forIn_pure_yield_eq_foldl,
    Nat.zero_add, List.map_id', Id.run, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, body,
    pure_bind]
  rfl


/-! ## Facts about the pieces -/

open Spec.Shift Spec.Pack

theorem foldMinsGo_inv {α : Type} (ix0 : MzIdx) (G : ByteArray) (f : α → Nat → Nat → α) (Q : Nat → α → Prop)
    (hs : ∀ p acc pm h, p < G.size → Q p acc → Q (p + 1) (f acc pm h))
    (hk : ∀ p acc, p < G.size → Q p acc → Q (p + 1) acc) :
    ∀ d p x good last acc, G.size - p = d → p ≤ G.size → Q p acc → Q G.size (foldMinsGo ix0 G f p x good last acc) := by
  intro d
  induction d with
  | zero =>
    intro p x good last acc hd hp hq
    unfold foldMinsGo; rw [if_neg (by omega)]; rw [show G.size = p by omega]; exact hq
  | succ d ih =>
    intro p x good last acc hd hp hq
    unfold foldMinsGo
    rw [if_pos (by omega)]
    dsimp only
    repeat' split
    all_goals first
      | exact ih _ _ _ _ _ (by omega) (by omega) (hs p acc _ _ (by omega) hq)
      | exact ih _ _ _ _ _ (by omega) (by omega) (hk p acc (by omega) hq)

theorem foldMins_inv {α : Type} (ix0 : MzIdx) (G : ByteArray) (init : α) (f : α → Nat → Nat → α) (Q : Nat → α → Prop)
    (hs : ∀ p acc pm h, p < G.size → Q p acc → Q (p + 1) (f acc pm h))
    (hk : ∀ p acc, p < G.size → Q p acc → Q (p + 1) acc) (h0 : Q 0 init) : Q G.size (foldMins ix0 G init f) :=
  foldMinsGo_inv ix0 G f Q hs hk _ 0 0 0 0 init rfl (Nat.zero_le _) h0

theorem zeros_spec (n : Nat) : (zeros n).size = n ∧ ∀ i, (zeros n).get! i = 0 := by
  have e : zeros n = (List.range n).foldl (fun B _ => B.push 0) (ByteArray.emptyWithCapacity n) := by
    unfold zeros
    simp [Std.Legacy.Range.forIn_eq_forIn_range', List.range'_eq_map_range]
  rw [e]
  have : ∀ (L : List Nat) (B : ByteArray), (∀ i, B.get! i = 0) →
      (L.foldl (fun B _ => B.push 0) B).size = B.size + L.length ∧ ∀ i, (L.foldl (fun B _ => B.push 0) B).get! i = 0 := by
    intro L
    induction L with
    | nil => intro B h; simpa using h
    | cons a L ih =>
      intro B h
      obtain ⟨h1, h2⟩ := ih (B.push 0) (fun i => by rw [get_push]; split; exact h i; split <;> rfl)
      simp only [List.foldl_cons, List.length_cons]
      exact ⟨by rw [h1, ByteArray.size_push]; omega, h2⟩
  have h0 : (ByteArray.emptyWithCapacity n).size = 0 := rfl
  obtain ⟨h1, h2⟩ := this (List.range n) (ByteArray.emptyWithCapacity n) (fun i => Fast.get!_out _ _ (by omega))
  exact ⟨by rw [h1, h0]; simp, h2⟩

theorem getU32_zero (B : ByteArray) (hB : ∀ i, B.get! i = 0) (j : Nat) : getU32 B j = 0 := by
  rw [getU32_eq, hB, hB, hB, hB]; rfl

/-- `Σ_{j < k} getU32 B j` -/
def sumU (B : ByteArray) : Nat → Nat
  | 0 => 0
  | k + 1 => sumU B k + getU32 B k

theorem sumU_set (B : ByteArray) (i v : Nat) (hB : B.size % 4 = 0) (hi : 4 * i + 3 < B.size) (hv : v < 2 ^ 32) :
    ∀ k, sumU (setU32 B i v) k + (if i < k then getU32 B i else 0) = sumU B k + (if i < k then v else 0) := by
  intro k
  induction k with
  | zero => simp [sumU]
  | succ k ih =>
    simp only [sumU]
    rw [getU32_setU32 _ _ _ _ hB]
    by_cases e : k = i
    · subst e
      rw [if_pos ⟨rfl, hi⟩, Nat.mod_eq_of_lt hv, if_pos (by omega), if_pos (by omega)]
      rw [if_neg (by omega), if_neg (by omega)] at ih
      omega
    · rw [if_neg (fun h => e h.1)]
      by_cases h2 : i < k
      · rw [if_pos h2, if_pos h2] at ih; rw [if_pos (by omega), if_pos (by omega)]; omega
      · rw [if_neg h2, if_neg h2] at ih; rw [if_neg (by omega), if_neg (by omega)]; omega

theorem sumU_set_out (B : ByteArray) (i v : Nat) (hB : B.size % 4 = 0) (hi : B.size ≤ 4 * i + 3) :
    ∀ j, getU32 (setU32 B i v) j = getU32 B j := by
  intro j; rw [getU32_setU32 _ _ _ _ hB, if_neg (fun h => by omega)]

theorem getU32_le_sumU (B : ByteArray) : ∀ k j, j < k → getU32 B j ≤ sumU B k := by
  intro k
  induction k with
  | zero => intro j h; omega
  | succ k ih =>
    intro j h; simp only [sumU]
    by_cases e : j = k
    · subst e; omega
    · have := ih j (by omega); omega


theorem sumU_mono (B : ByteArray) : ∀ k k', k ≤ k' → sumU B k ≤ sumU B k' := by
  intro k k' h
  induction k' with
  | zero => rw [show k = 0 by omega]; exact Nat.le_refl _
  | succ k' ih =>
    by_cases e : k = k' + 1
    · rw [e]; exact Nat.le_refl _
    · have := ih (by omega); simp only [sumU]; omega

theorem cnt1_spec (G : ByteArray) (hN : G.size < 2 ^ 32) :
    (cnt1 G).size = 4 * (2 ^ 26 + 1) ∧ sumU (cnt1 G) (2 ^ 26 + 1) ≤ G.size ∧ getU32 (cnt1 G) 0 = 0 := by
  unfold cnt1
  apply foldMins_inv _ _ _ _ (fun p (cnt : ByteArray) =>
    cnt.size = 4 * (2 ^ 26 + 1) ∧ sumU cnt (2 ^ 26 + 1) ≤ p ∧ getU32 cnt 0 = 0)
  · intro p cnt pm h hp ⟨h1, h2, h3⟩
    generalize h >>> (ix0 G).kb = b0
    generalize hbd : b0 + 1 = b
    have hb1 : 1 ≤ b := by omega
    have hB : cnt.size % 4 = 0 := by rw [h1]
    by_cases hb : 4 * b + 3 < cnt.size
    · have hold : getU32 cnt b ≤ sumU cnt (2 ^ 26 + 1) := getU32_le_sumU _ _ _ (by omega)
      have := sumU_set cnt b (getU32 cnt b + 1) hB hb (by omega) (2 ^ 26 + 1)
      rw [if_pos (by omega), if_pos (by omega)] at this
      refine ⟨by rw [setU32_size, h1], by omega, ?_⟩
      rw [getU32_setU32 _ _ _ _ hB]
      by_cases e : (0 : Nat) = b
      · omega
      · rw [if_neg (fun h => e h.1), h3]
    · refine ⟨by rw [setU32_size, h1], ?_, ?_⟩
      · have : sumU (setU32 cnt b (getU32 cnt b + 1)) (2 ^ 26 + 1) = sumU cnt (2 ^ 26 + 1) := by
          have e := sumU_set_out cnt b (getU32 cnt b + 1) hB (by omega)
          generalize 2 ^ 26 + 1 = k
          induction k with
          | zero => rfl
          | succ k ih => simp only [sumU, ih, e]
        omega
      · rw [sumU_set_out cnt b _ hB (by omega), h3]
  · intro p acc _ ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
  · obtain ⟨z1, z2⟩ := zeros_spec (4 * (2 ^ 26 + 1))
    refine ⟨z1, ?_, getU32_zero _ z2 0⟩
    have : ∀ k, sumU (zeros (4 * (2 ^ 26 + 1))) k = 0 := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [sumU, ih, getU32_zero _ z2]
    rw [this]; exact Nat.le_refl _


theorem cnt2_spec (G : ByteArray) (hN : G.size < 2 ^ 32) :
    (cnt2 G).size = 4 * (2 ^ 26 + 1) ∧ ∀ j, j ≤ 2 ^ 26 → getU32 (cnt2 G) j = sumU (cnt1 G) (j + 1) := by
  obtain ⟨c1, c2, c3⟩ := cnt1_spec G hN
  have key : ∀ k, k ≤ 2 ^ 26 →
      let B := (List.range k).foldl (fun cnt b => setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)) (cnt1 G)
      B.size = 4 * (2 ^ 26 + 1) ∧ (∀ j, j ≤ k → getU32 B j = sumU (cnt1 G) (j + 1)) ∧
        (∀ j, k < j → getU32 B j = getU32 (cnt1 G) j) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨c1, fun j hj => ?_, fun j _ => rfl⟩
      rw [show j = 0 by omega]; simp [sumU, c3]
    | succ k ih =>
      intro hk
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl (fun cnt b => setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)) (cnt1 G) = B at i1 i2 i3
      have hB : B.size % 4 = 0 := by rw [i1]
      have hv : getU32 B (k + 1) + getU32 B k = sumU (cnt1 G) (k + 2) := by
        rw [i3 (k + 1) (by omega), i2 k (Nat.le_refl _)]; simp only [sumU]; omega
      have hlt : sumU (cnt1 G) (k + 2) < 2 ^ 32 := by
        have := sumU_mono (cnt1 G) (k + 2) (2 ^ 26 + 1) (by omega); omega
      refine ⟨by rw [setU32_size, i1], fun j hj => ?_, fun j hj => ?_⟩
      · rw [getU32_setU32 _ _ _ _ hB]
        by_cases e : j = k + 1
        · subst e; rw [if_pos ⟨rfl, by rw [i1]; omega⟩, hv, Nat.mod_eq_of_lt hlt]
        · rw [if_neg (fun h => e h.1)]; exact i2 j (by omega)
      · rw [getU32_setU32 _ _ _ _ hB, if_neg (fun h => by omega)]; exact i3 j (by omega)
  obtain ⟨k1, k2, -⟩ := key (2 ^ 26) (Nat.le_refl _)
  exact ⟨k1, k2⟩

theorem wrLE_size (B : ByteArray) (v : UInt64) : ∀ n j, (wrLE B j v n).size = B.size := by
  intro n
  induction n generalizing B v with
  | zero => intro j; rfl
  | succ n ih => intro j; simp only [wrLE, ih, size_set]

theorem slB_size (G : ByteArray) : (slB G).size = 5 * getU32 (cnt2 G) (2 ^ 26) := by
  unfold slB
  apply foldMins_inv _ _ _ _ (fun _ (x : ByteArray × ByteArray) => x.2.size = 5 * getU32 (cnt2 G) (2 ^ 26))
  · intro p acc pm h _ hq; simp only [wrLE_size]; exact hq
  · intro p acc _ hq; exact hq
  · exact (zeros_spec _).1

theorem runsB_spec (G : ByteArray) : (runsB G).size ≤ 2 * G.size ∧ ∀ x ∈ runsB G, x ≤ G.size := by
  have key : ∀ k, k ≤ G.size → ((List.range k).foldl (runStep G) #[]).size ≤ 2 * k ∧
      ∀ x ∈ (List.range k).foldl (runStep G) #[], x ≤ k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨i1, i2⟩ := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl (runStep G) #[] = R at i1 i2
      unfold runStep; dsimp only
      split <;> split <;> refine ⟨by (try simp only [Array.size_push]); omega, fun x hx => ?_⟩ <;>
        (try simp only [Array.mem_push] at hx) <;> (repeat' rcases hx with hx | hx) <;>
        first | (have := i2 x hx; omega) | omega
  unfold runsB; exact key G.size (Nat.le_refl _)


/-- What the save/load and checker-shift proofs need from the built minimizer index. -/
structure BuiltOk (ix : MzIdx) (N : Nat) : Prop where
  sz : ix.offs.size = 4 * (2 ^ ix.B + 1)
  ob0 : ix.ob = 0
  sw : ix.sw = 5
  le : ∀ b, b ≤ 2 ^ ix.B → getU32 ix.offs b ≤ getU32 ix.offs (2 ^ ix.B)
  tot : getU32 ix.offs (2 ^ ix.B) ≤ N
  sl : ix.sl.size = 5 * getU32 ix.offs (2 ^ ix.B)
  runsSz : ix.runs.size ≤ 2 * N
  runsLe : ∀ x ∈ ix.runs, x ≤ N
  small : ix.k < 2 ^ 64 ∧ ix.B < 2 ^ 64 ∧ ix.w < 2 ^ 64 ∧ ix.c < 2 ^ 64 ∧ ix.kb < 2 ^ 64 ∧ ix.kf < 2 ^ 64 ∧
    ix.T < 2 ^ 64 ∧ ix.t < 2 ^ 64 ∧ ix.kbM < 2 ^ 64 ∧ ix.fM < 2 ^ 64 ∧ ix.tM < 2 ^ 64 ∧
    ix.pm.size < 2 ^ 64 ∧ (∀ x ∈ ix.pm, x < 2 ^ 64) ∧ ix.bsh < 2 ^ 64 ∧ ix.ash < 2 ^ 64 ∧ ix.fsh < 2 ^ 64

theorem buildW_ok (G : ByteArray) (hN : G.size < 2 ^ 32) : BuiltOk (buildW G 22 26 0 5 6) G.size := by
  rw [buildW_eq G (by omega)]
  obtain ⟨c1, c2⟩ := cnt2_spec G hN
  obtain ⟨r1, r2⟩ := runsB_spec G
  have hB : (ix0 G).B = 26 := rfl
  have tot : getU32 (cnt2 G) (2 ^ 26) ≤ G.size := by rw [c2 _ (Nat.le_refl _)]; exact (cnt1_spec G hN).2.1
  have hkf : (ix0 G).kf ≤ 18 := by simp only [ix0, mkIdx]; omega
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, r1, r2, ?_⟩
  · simp only [hB]; exact c1
  · intro b hb; simp only [hB] at hb ⊢
    rw [c2 b hb, c2 _ (Nat.le_refl _)]; exact sumU_mono _ _ _ (by omega)
  · simp only [hB]; exact tot
  · simp only [hB]; exact slB_size G
  · have p1 : 2 ^ (ix0 G).kf ≤ 2 ^ 18 := Nat.pow_le_pow_right (by omega) hkf
    have hT : (ix0 G).T = (ix0 G).kf := by simp only [ix0, mkIdx]; rfl
    refine ⟨by simp [ix0, mkIdx], by simp [ix0, mkIdx], by simp [ix0, mkIdx, q], by simp [ix0, mkIdx],
      by simp [ix0, mkIdx], by simp only [] ; omega, by simp only []; rw [hT]; omega, by simp [ix0, mkIdx],
      by simp only [show (ix0 G).kbM = 2 ^ (ix0 G).kf - 1 from rfl]; omega, by simp [ix0, mkIdx],
      by simp only [show (ix0 G).tM = 2 ^ (ix0 G).T - 1 from rfl]; rw [hT]; omega, by simp [ix0, mkIdx, q], ?_,
      by simp only [show (ix0 G).bsh = (ix0 G).kf from rfl]; omega,
      by simp only [show (ix0 G).ash = (ix0 G).kf + 2 * 0 from rfl]; omega,
      by simp only [show (ix0 G).fsh = (ix0 G).kf + 4 * 0 from rfl]; omega⟩
    intro x hx
    simp only [show (ix0 G).pm = (Array.range (q + 1 - 22 + 1)).map fun i => 2 ^ (2 * i) - 1 from rfl,
      Array.mem_map, Array.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [q] at hi
    have : 2 ^ (2 * i) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    omega


theorem ofChroms_n (gbs : Array ByteArray) : (Fast.GV.ofChroms gbs).n = (Pack.catL gbs.toList).length := by
  have key : ∀ (L : List ByteArray) (st : Array Nat), 0 < st.size →
      (L.foldl (fun st g => st.push (st.back! + g.size)) st).back! = st.back! + (Pack.catL L).length := by
    intro L
    induction L with
    | nil => intro st _; simp [Pack.catL]
    | cons g L ih =>
      intro st hs
      simp only [List.foldl_cons]
      rw [ih _ (by simp)]
      simp only [Pack.catL, List.length_append, Pack.dl_len, Array.back!_push]
      omega
  have e0 : (Fast.GV.ofChroms gbs).n = (forIn (m := Id) gbs (#[0] : Array Nat) fun g r =>
      pure (ForInStep.yield (r.push (r.back! + g.size)))).back! := rfl
  have e : (Fast.GV.ofChroms gbs).n = (gbs.toList.foldl (fun st g => st.push (st.back! + g.size)) #[0]).back! := by
    rw [e0, Array.forIn_pure_yield_eq_foldl, Array.foldl_toList]; rfl
  rw [e, key _ _ (by simp)]
  simp


/-- Both branches of `buildMz` build `buildW` on a genome of `N` letters. -/
theorem buildMz_ok (byteGenome : GenomeFile) (hN : (Pack.catG byteGenome).length < 2 ^ 32) :
    BuiltOk (Index.buildMz (byteGenome.map (·.2)) (Index.packAll (byteGenome.map (·.2)))) (Pack.catG byteGenome).length := by
  unfold Index.buildMz
  simp only [Index.kMz, Index.bMz, Index.cMz, Index.swMz, Index.tMz]
  split
  · rw [buildWV_eq _ _ (Fast.repV_unpack _)]
    have hs : (Fast.unpackV (Fast.GV.ofChroms (byteGenome.map (·.2)))).size = (Pack.catG byteGenome).length := by
      rw [← (Fast.repV_unpack _).1, ofChroms_n]; rfl
    have := buildW_ok _ (by rw [hs]; exact hN)
    rw [hs] at this; exact this
  · rw [buildWP_eq' (rep_unpack _)]
    have hs : (unpack (Index.packAll (byteGenome.map (·.2)))).size = (Pack.catG byteGenome).length := by
      rw [← (rep_unpack _).1]; exact (Pack.packAll_spec byteGenome hN).1
    have := buildW_ok _ (by rw [hs]; exact hN)
    rw [hs] at this; exact this

end Spec.Build

#print axioms Spec.Build.buildMz_ok
