import FastGenShort

/-!
# Batched seed scan for short reads

`scanL` scans a chromosome once per seed.  `batchScan` scans it once for a
batch of seeds whose first `K = 12` letters are ACGT: a rolling 2-bit code of the
last 12 genome letters (`roll`, invariant `RollOk`), a 4^12-byte table of the
seeds' prefix codes, and a binary search in the sorted keys `code·S + sid`; each
candidate is verified letter by letter.  The result for every seed is exactly
`scanL` (`batchScan_eq`), so the short-read proofs apply unchanged.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Codes of ACGT words -/

/-- 2-bit value of a letter; `4` = not ACGT. -/
@[inline] def acgtV (b : UInt8) : Nat :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

theorem acgtV_le (b : UInt8) : acgtV b ≤ 4 := by unfold acgtV; split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- Code of `A[p, p+k)` (first letter most significant), if all ACGT. -/
def codeW (A : ByteArray) (p : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => match codeW A p k with
    | some c => if acgtV (A.get! (p + k)) < 4 then some (c * 4 + acgtV (A.get! (p + k))) else none
    | none => none

/-- Equal letters, equal codes. -/
theorem codeW_congr (A B : ByteArray) (p s : Nat) : ∀ k, (∀ i, i < k → A.get! (p + i) = B.get! (s + i)) →
    codeW A p k = codeW B s k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [codeW]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem codeW_some (A : ByteArray) (p : Nat) : ∀ k, (∀ i, i < k → acgtV (A.get! (p + i)) < 4) →
    ∃ c, codeW A p k = some c ∧ c < 4 ^ k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, rfl, by simp⟩
  | succ k ih =>
    intro h
    obtain ⟨c, hc, hlt⟩ := ih (fun i hi => h i (by omega))
    have hv := h k (by omega)
    refine ⟨c * 4 + acgtV (A.get! (p + k)), by simp only [codeW, hc, if_pos hv], ?_⟩
    rw [Nat.pow_succ]; omega

theorem codeW_acgt (A : ByteArray) (p : Nat) : ∀ k c, codeW A p k = some c →
    ∀ i, i < k → acgtV (A.get! (p + i)) < 4 := by
  intro k
  induction k with
  | zero => intro c _ i hi; omega
  | succ k ih =>
    intro c h i hi
    simp only [codeW] at h
    cases hk : codeW A p k with
    | none => rw [hk] at h; cases h
    | some c' =>
      rw [hk] at h
      simp only [] at h
      split at h
      · next hv =>
        by_cases e : i = k
        · subst e; exact hv
        · exact ih c' hk i (by omega)
      · cases h

/-! ## The rolling code -/

def K12 : Nat := 12

/-- After letter `x`: `c` = code of the last `min r K` letters (mod `4^K`), `r` = the
length of the ACGT run ending at `x` (capped at `K`). -/
@[inline] def roll (G : ByteArray) (x : Nat) (st : Nat × Nat) : Nat × Nat :=
  let v := acgtV (G.get! x)
  if v < 4 then ((st.1 * 4 + v) % 4 ^ K12, min (st.2 + 1) K12) else (0, 0)

/-- The state after the letters `[0, x)`. -/
structure RollOk (G : ByteArray) (x : Nat) (st : Nat × Nat) : Prop where
  le : st.2 ≤ K12
  le_x : st.2 ≤ x
  code : ∀ r, r ≤ st.2 → codeW G (x - r) r = some (st.1 % 4 ^ r)
  run : ∀ r, r ≤ K12 → r ≤ x → (∀ i, i < r → acgtV (G.get! (x - r + i)) < 4) → r ≤ st.2

theorem rollOk_zero (G : ByteArray) : RollOk G 0 (0, 0) :=
  ⟨by unfold K12; omega, Nat.le_refl _, fun r hr => by
    have : r = 0 := by simpa using hr
    subst this; rfl, fun r _ hr _ => by omega⟩

theorem mod_step (c v r : Nat) (hv : v < 4) : (c * 4 + v) % 4 ^ (r + 1) = c % 4 ^ r * 4 + v := by
  rw [Nat.pow_succ]
  have h4 : 0 < 4 ^ r := Nat.pow_pos (by decide : (0 : Nat) < 4)
  rw [Nat.mul_comm (4 ^ r) 4]
  have e : c * 4 + v = (c % 4 ^ r * 4 + v) + (c / 4 ^ r) * (4 * 4 ^ r) := by
    have := Nat.div_add_mod c (4 ^ r)
    have : c * 4 = (4 ^ r * (c / 4 ^ r) + c % 4 ^ r) * 4 := by rw [this]
    rw [this]
    rw [Nat.add_mul, Nat.mul_comm (4 ^ r) (c / 4 ^ r), Nat.mul_assoc, Nat.mul_comm (4 ^ r) 4]
    omega
  rw [e, Nat.add_mul_mod_self_right]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt c h4
  have : c % 4 ^ r * 4 + v < (c % 4 ^ r + 1) * 4 := by omega
  have : (c % 4 ^ r + 1) * 4 ≤ 4 * 4 ^ r := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem rollOk_step (G : ByteArray) (x : Nat) (st : Nat × Nat) (h : RollOk G x st) :
    RollOk G (x + 1) (roll G x st) := by
  obtain ⟨hle, hlx, hcode, hrun⟩ := h
  unfold roll
  dsimp only
  have hK : K12 = 12 := rfl
  split
  · next hv =>
    refine ⟨by simp only; omega, by simp only; omega, fun r hr => ?_, fun r hr hrx hall => ?_⟩
    · simp only at hr
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp [codeW, Nat.mod_one]
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hc := hcode r' (by omega)
        have e : x + 1 - (r' + 1) = x - r' := by omega
        rw [e]
        simp only [codeW, hc]
        have e2 : x - r' + r' = x := by omega
        rw [e2, if_pos hv]
        congr 1
        rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 4 (by omega : r' + 1 ≤ K12)), mod_step _ _ _ hv]
    · simp only
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · omega
      · have := hrun (r - 1) (by omega) (by omega) (fun i hi => by
          have := hall i (by omega)
          rwa [show x + 1 - r + i = x - (r - 1) + i by omega] at this)
        omega
  · next hv =>
    refine ⟨by simp only; unfold K12; omega, by simp only; omega, fun r hr => ?_, fun r hr hrx hall => ?_⟩
    · simp only at hr
      have : r = 0 := by omega
      subst this; rfl
    · simp only
      apply Classical.byContradiction; intro hne
      have := hall (r - 1) (by omega)
      rw [show x + 1 - r + (r - 1) = x by omega] at this
      exact hv this

/-! ## `scanL` as a filter -/

theorem scanAux_toList (G R : ByteArray) (s l base stop : Nat) :
    ∀ d p (acc : Array Nat), stop - p = d → (scanAux G R s l base stop p acc).toList =
      acc.toList ++ ((List.range' p (stop - p)).filter (fun p => eqRun G R p s l)).map (fun p => (p + base) * 16) := by
  intro d
  induction d with
  | zero =>
    intro p acc hd
    unfold scanAux; rw [if_neg (by omega), hd]; simp
  | succ d ih =>
    intro p acc hd
    unfold scanAux; rw [if_pos (by omega)]
    rw [ih (p + 1) _ (by omega), show stop - p = (stop - (p + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
    split
    · simp
    · rfl

theorem scanL_toList (G R : ByteArray) (s l base : Nat) :
    (scanL G R s l base).toList =
      ((List.range (G.size + 1 - l)).filter (fun p => eqRun G R p s l)).map (fun p => (p + base) * 16) := by
  unfold scanL
  rw [scanAux_toList G R s l base _ _ 0 #[] rfl, List.range_eq_range']
  simp

/-! ## The batch -/

structure Seed where
  R : ByteArray
  s : Nat
  l : Nat
  base : Nat

instance : Inhabited Seed := ⟨⟨ByteArray.empty, 0, 0, 0⟩⟩

/-- The seed's prefix code, when it has `K` ACGT letters. -/
def seedKey (sd : Seed) : Option Nat := if K12 ≤ sd.l then codeW sd.R sd.s K12 else none

/-- Sorted keys `code·S + i` of the seeds with a prefix code. -/
def batchKeys (sds : Array Seed) : Array Nat :=
  (((List.range sds.size).filterMap fun i => (seedKey sds[i]!).map fun k => k * sds.size + i).mergeSort
    (fun a b => decide (a ≤ b))).toArray

/-- `1` at every seed prefix code. -/
def batchTbl (ks : Array Nat) (S : Nat) : ByteArray :=
  ks.foldl (fun t e => t.set! (e / S) 1) ⟨Array.replicate (4 ^ K12) 0⟩

/-- Candidate key `e` at window start `p`: verify the seed and record the anchor. -/
@[inline] def visit (G : ByteArray) (sds : Array Seed) (p : Nat) (out : Array (Array Nat)) (e : Nat) :
    Array (Array Nat) :=
  let i := e % sds.size
  let sd := sds[i]!
  if p + sd.l ≤ G.size ∧ eqRun G sd.R p sd.s sd.l = true then out.set! i (out[i]!.push ((p + sd.base) * 16))
  else out

def batchAux (G : ByteArray) (sds : Array Seed) (ks : Array Nat) (tbl : ByteArray) (x : Nat) (st : Nat × Nat)
    (out : Array (Array Nat)) : Array (Array Nat) :=
  if x < G.size then
    let st' := roll G x st
    let out' := if K12 ≤ st'.2 ∧ tbl[st'.1]! = 1 then
        (ks.extract (lbA ks (st'.1 * sds.size) 0 ks.size) (lbA ks ((st'.1 + 1) * sds.size) 0 ks.size)).foldl
          (visit G sds (x + 1 - K12)) out
      else out
    batchAux G sds ks tbl (x + 1) st' out'
  else out
termination_by G.size - x

/-- Every seed's anchors in `G` (`batchScan_eq`: exactly `scanL`). -/
def batchScan (G : ByteArray) (sds : Array Seed) : Array (Array Nat) :=
  let ks := batchKeys sds
  batchAux G sds ks (batchTbl ks sds.size) 0 (0, 0)
    ((Array.range sds.size).map fun i =>
      if (seedKey sds[i]!).isSome then #[] else scanL G sds[i]!.R sds[i]!.s sds[i]!.l sds[i]!.base)

/-! ## Proof: the batch is `scanL` -/

theorem codeW_lt (A : ByteArray) (p : Nat) : ∀ k c, codeW A p k = some c → c < 4 ^ k := by
  intro k
  induction k with
  | zero => intro c h; simp [codeW] at h; subst h; simp
  | succ k ih =>
    intro c h
    simp only [codeW] at h
    cases hk : codeW A p k with
    | none => rw [hk] at h; cases h
    | some c' =>
      rw [hk] at h; simp only [] at h
      split at h
      · next hv =>
        cases h
        have := ih c' hk
        rw [Nat.pow_succ]; omega
      · cases h

theorem roll_lt (G : ByteArray) (x : Nat) (st : Nat × Nat) : (roll G x st).1 < 4 ^ K12 := by
  unfold roll; dsimp only
  split
  · exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  · exact Nat.pow_pos (by decide)

section batch
variable (G : ByteArray) (sds : Array Seed)

theorem key_div_mod (k i S : Nat) (hi : i < S) : (k * S + i) % S = i ∧ (k * S + i) / S = k := by
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
  · rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]

theorem mem_batchKeys (e : Nat) :
    e ∈ (batchKeys sds).toList ↔ ∃ i, i < sds.size ∧ ∃ k, seedKey sds[i]! = some k ∧ e = k * sds.size + i := by
  unfold batchKeys
  rw [List.toList_toArray, List.mem_mergeSort, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [List.mem_range] at hi
    cases hk : seedKey sds[i]! with
    | none => rw [hk] at he; cases he
    | some k => rw [hk] at he; simp only [Option.map_some, Option.some.injEq] at he; exact ⟨i, hi, k, hk, he.symm⟩
  · rintro ⟨i, hi, k, hk, rfl⟩
    exact ⟨i, List.mem_range.mpr hi, by rw [hk]; rfl⟩

theorem batchKeys_sorted : (batchKeys sds).toList.Pairwise (· < ·) := by
  have hnd : (batchKeys sds).toList.Pairwise (· ≠ ·) := by
    unfold batchKeys
    rw [List.toList_toArray]
    apply (List.mergeSort_perm _ _).pairwise_iff (fun h => Ne.symm h) |>.2
    rw [List.pairwise_filterMap]
    apply List.nodup_range.imp_of_mem
    intro a a' ha ha' hne b hb b' hb'
    rw [List.mem_range] at ha ha'
    cases h1 : seedKey sds[a]! <;> cases h2 : seedKey sds[a']! <;> simp only [h1, h2, Option.map_some,
      Option.map_none, reduceCtorEq, Option.some.injEq] at hb hb'
    subst hb hb'
    intro he
    have := congrArg (· % sds.size) he
    simp only [(key_div_mod _ _ _ ha).1, (key_div_mod _ _ _ ha').1] at this
    exact hne this
  have hle : (batchKeys sds).toList.Pairwise (· ≤ ·) := by
    unfold batchKeys
    rw [List.toList_toArray]
    have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega)
      ((List.range sds.size).filterMap fun i => (seedKey sds[i]!).map fun k => k * sds.size + i)
    exact this.imp (fun h => by simpa using h)
  exact (hle.and hnd).imp (fun ⟨h1, h2⟩ => by omega)

end batch


theorem batchTbl_hit (ks : Array Nat) (S : Nat) (hks : ∀ e ∈ ks.toList, e / S < 4 ^ K12) :
    ∀ e ∈ ks.toList, (batchTbl ks S)[e / S]! = 1 := by
  unfold batchTbl
  rw [← Array.foldl_toList]
  have key : ∀ (L : List Nat) (t : ByteArray), t.size = 4 ^ K12 → (∀ e ∈ L, e / S < 4 ^ K12) →
      (L.foldl (fun t e => t.set! (e / S) 1) t).size = 4 ^ K12 ∧
      (∀ c : Nat, t[c]! = (1 : UInt8) → (L.foldl (fun t e => t.set! (e / S) 1) t)[c]! = 1) ∧
      ∀ e ∈ L, (L.foldl (fun t e => t.set! (e / S) 1) t)[e / S]! = 1 := by
    intro L
    induction L with
    | nil => intro t ht _; exact ⟨ht, fun c h => h, fun e he => by simp at he⟩
    | cons e L ih =>
      intro t ht hL
      have he : e / S < t.size := by rw [ht]; exact hL e List.mem_cons_self
      obtain ⟨a1, a2, a3⟩ := ih (t.set! (e / S) 1) (by simp [ht]) (fun e' h' => hL e' (List.mem_cons_of_mem _ h'))
      refine ⟨a1, fun c hc => a2 c ?_, fun e' he' => ?_⟩
      · rw [ByteArray.getElem!_set! _ _ _ _ he]; split
        · rfl
        · exact hc
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact a2 _ (by rw [ByteArray.getElem!_set!_self _ _ _ he])
        · exact a3 e' he'
  exact (key ks.toList _ (by show (Array.replicate (4 ^ K12) (0 : UInt8)).size = 4 ^ K12; simp) hks).2.2

section visit
variable (G : ByteArray) (sds : Array Seed)

theorem visit_fold (p : Nat) :
    ∀ (E : List Nat) (out : Array (Array Nat)), out.size = sds.size → (∀ e ∈ E, e % sds.size < sds.size) →
      E.Pairwise (fun a b => a % sds.size ≠ b % sds.size) →
      (E.foldl (visit G sds p) out).size = sds.size ∧
      ∀ i, i < sds.size → (E.foldl (visit G sds p) out)[i]! =
        if (∃ e ∈ E, e % sds.size = i) ∧ (p + sds[i]!.l ≤ G.size ∧ eqRun G sds[i]!.R p sds[i]!.s sds[i]!.l = true)
        then out[i]!.push ((p + sds[i]!.base) * 16) else out[i]! := by
  intro E
  induction E with
  | nil => intro out hsz _ _; exact ⟨hsz, fun i _ => by simp⟩
  | cons e E ih =>
    intro out hsz hE hpw
    rw [List.pairwise_cons] at hpw
    have he := hE e List.mem_cons_self
    generalize hi0 : e % sds.size = i0 at *
    have hv : visit G sds p out e = if p + sds[i0]!.l ≤ G.size ∧ eqRun G sds[i0]!.R p sds[i0]!.s sds[i0]!.l = true
        then out.set! i0 (out[i0]!.push ((p + sds[i0]!.base) * 16)) else out := by
      unfold visit; rw [hi0]
    have hsz1 : (visit G sds p out e).size = sds.size := by rw [hv]; split <;> simp [hsz]
    obtain ⟨a1, a2⟩ := ih (visit G sds p out e) hsz1 (fun e' h' => hE e' (List.mem_cons_of_mem _ h')) hpw.2
    rw [List.foldl_cons]
    refine ⟨a1, fun i hi => ?_⟩
    rw [a2 i hi]
    by_cases e1 : i = i0
    · subst e1
      have hno : ¬ ∃ e' ∈ E, e' % sds.size = i := fun ⟨e', h1, h2⟩ => hpw.1 e' h1 h2.symm
      simp only [hno, false_and, if_false, hv]
      have hyes : ∃ e' ∈ e :: E, e' % sds.size = i := ⟨e, List.mem_cons_self, hi0⟩
      simp only [hyes, true_and]
      split
      · rw [getElem!_set!']; simp [hsz, hi]
      · rfl
    · have hnv : (visit G sds p out e)[i]! = out[i]! := by
        rw [hv]; split
        · rw [getElem!_set!']; simp [Ne.symm e1]
        · rfl
      have hiff : (∃ e' ∈ e :: E, e' % sds.size = i) ↔ (∃ e' ∈ E, e' % sds.size = i) := by
        constructor
        · rintro ⟨e', h1, h2⟩
          rcases List.mem_cons.mp h1 with rfl | h1
          · exact absurd (h2.symm.trans hi0) e1
          · exact ⟨e', h1, h2⟩
        · rintro ⟨e', h1, h2⟩; exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩
      simp only [hnv, hiff]

end visit

section main
variable (G : ByteArray) (sds : Array Seed)

/-- Anchors of seed `i` at the window starts read so far (letters `[0, x)`). -/
def tgt (i x : Nat) : List Nat :=
  ((List.range (x + 1 - K12)).filter (fun p => decide (p + sds[i]!.l ≤ G.size) &&
    eqRun G sds[i]!.R p sds[i]!.s sds[i]!.l)).map (fun p => (p + sds[i]!.base) * 16)

structure BInv (x : Nat) (st : Nat × Nat) (out : Array (Array Nat)) : Prop where
  roll : RollOk G x st
  sz : out.size = sds.size
  key : ∀ i, i < sds.size → (seedKey sds[i]!).isSome → out[i]!.toList = tgt G sds i x
  nokey : ∀ i, i < sds.size → (seedKey sds[i]!).isSome = false →
    out[i]! = scanL G sds[i]!.R sds[i]!.s sds[i]!.l sds[i]!.base

/-- One letter of the batch loop. -/
@[inline] def stepOut (ks : Array Nat) (tbl : ByteArray) (x : Nat) (st' : Nat × Nat) (out : Array (Array Nat)) :
    Array (Array Nat) :=
  if K12 ≤ st'.2 ∧ tbl[st'.1]! = 1 then
    (ks.extract (lbA ks (st'.1 * sds.size) 0 ks.size) (lbA ks ((st'.1 + 1) * sds.size) 0 ks.size)).foldl
      (visit G sds (x + 1 - K12)) out
  else out

theorem batchAux_unfold (ks : Array Nat) (tbl : ByteArray) (x : Nat) (st : Nat × Nat) (out : Array (Array Nat)) :
    batchAux G sds ks tbl x st out = if x < G.size then
      batchAux G sds ks tbl (x + 1) (roll G x st) (stepOut G sds ks tbl x (roll G x st) out) else out := by
  rw [batchAux]; rfl

theorem tgt_succ (i x : Nat) : tgt G sds i (x + 1) = tgt G sds i x ++
    (if K12 ≤ x + 1 ∧ (x + 1 - K12 + sds[i]!.l ≤ G.size ∧ eqRun G sds[i]!.R (x + 1 - K12) sds[i]!.s sds[i]!.l = true)
      then [(x + 1 - K12 + sds[i]!.base) * 16] else []) := by
  unfold tgt
  by_cases hx : K12 ≤ x + 1
  · rw [show x + 1 + 1 - K12 = (x + 1 - K12) + 1 by omega, List.range_succ, List.filter_append, List.map_append]
    congr 1
    simp only [List.filter_cons, List.filter_nil, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hc : x + 1 - K12 + sds[i]!.l ≤ G.size ∧ eqRun G sds[i]!.R (x + 1 - K12) sds[i]!.s sds[i]!.l = true
    · rw [if_pos hc, if_pos ⟨hx, hc⟩]; rfl
    · rw [if_neg hc, if_neg (fun h => hc h.2)]; rfl
  · rw [show x + 1 + 1 - K12 = 0 by unfold K12 at *; omega, show x + 1 - K12 = 0 by unfold K12 at *; omega,
      if_neg (fun h => hx h.1)]
    simp

theorem tgt_final (i : Nat) (hl : K12 ≤ sds[i]!.l) :
    tgt G sds i G.size = (scanL G sds[i]!.R sds[i]!.s sds[i]!.l sds[i]!.base).toList := by
  rw [scanL_toList]
  unfold tgt
  generalize sds[i]!.l = l at *
  have hMN : G.size + 1 - l ≤ G.size + 1 - K12 := by omega
  rw [List.range_eq_range', List.range_eq_range',
    show G.size + 1 - K12 = (G.size + 1 - l) + (G.size + 1 - K12 - (G.size + 1 - l)) by omega,
    ← List.range'_append, List.filter_append]
  have h2 : (List.range' (0 + 1 * (G.size + 1 - l)) (G.size + 1 - K12 - (G.size + 1 - l))).filter
      (fun p => decide (p + l ≤ G.size) && eqRun G sds[i]!.R p sds[i]!.s l) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    rw [List.mem_range'] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h; omega
  rw [h2, List.append_nil]
  congr 1
  apply List.filter_congr
  intro p hp
  rw [List.mem_range'] at hp
  have : p + l ≤ G.size := by omega
  simp [this]

end main

theorem extract_sub (a : Array Nat) (i j : Nat) : (a.extract i j).toList.Sublist a.toList := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

section main2
variable (G : ByteArray) (sds : Array Seed)

theorem seedKey_spec (i k : Nat) (h : seedKey sds[i]! = some k) :
    K12 ≤ sds[i]!.l ∧ codeW sds[i]!.R sds[i]!.s K12 = some k := by
  unfold seedKey at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem keys_facts (hS : 0 < sds.size) :
    (∀ e ∈ (batchKeys sds).toList, e % sds.size < sds.size ∧
      seedKey sds[e % sds.size]! = some (e / sds.size) ∧ e / sds.size < 4 ^ K12) ∧
    (batchKeys sds).toList.Pairwise (fun a b => a % sds.size ≠ b % sds.size) := by
  have h1 : ∀ e ∈ (batchKeys sds).toList, e % sds.size < sds.size ∧
      seedKey sds[e % sds.size]! = some (e / sds.size) ∧ e / sds.size < 4 ^ K12 := by
    intro e he
    obtain ⟨i, hi, k, hk, rfl⟩ := (mem_batchKeys sds e).mp he
    rw [(key_div_mod k i _ hi).1, (key_div_mod k i _ hi).2]
    exact ⟨hi, hk, codeW_lt _ _ _ _ (seedKey_spec sds i k hk).2⟩
  refine ⟨h1, (batchKeys_sorted sds).imp_of_mem (fun {a b} ha hb hab he => ?_)⟩
  have ka := (h1 a ha).2.1
  have kb := (h1 b hb).2.1
  rw [he] at ka
  rw [ka] at kb
  have hd : a / sds.size = b / sds.size := by simpa using kb
  have := Nat.div_add_mod a sds.size
  have := Nat.div_add_mod b sds.size
  rw [hd, he] at *
  omega

set_option maxHeartbeats 1000000 in
theorem binv_step (hS : 0 < sds.size) (x : Nat) (st : Nat × Nat) (out : Array (Array Nat)) (hx : x < G.size)
    (h : BInv G sds x st out) :
    BInv G sds (x + 1) (roll G x st)
      (stepOut G sds (batchKeys sds) (batchTbl (batchKeys sds) sds.size) x (roll G x st) out) := by
  obtain ⟨hroll, hsz, hkey, hnokey⟩ := h
  have hR' := rollOk_step G x st hroll
  have hlt := roll_lt G x st
  obtain ⟨kf, kpw⟩ := keys_facts sds hS
  have htbl := batchTbl_hit (batchKeys sds) sds.size (fun e he => (kf e he).2.2)
  generalize hks : batchKeys sds = ks at kf kpw htbl
  generalize roll G x st = st' at hR' hlt
  have hinc := incA_of ks (by rw [← hks]; exact batchKeys_sorted sds)
  -- a seed matching at the new window start: the rolling state sees its code
  have code_of : ∀ i, i < sds.size → ∀ k, seedKey sds[i]! = some k → K12 ≤ x + 1 →
      (x + 1 - K12 + sds[i]!.l ≤ G.size ∧ eqRun G sds[i]!.R (x + 1 - K12) sds[i]!.s sds[i]!.l = true) →
      K12 ≤ st'.2 ∧ st'.1 = k := by
    intro i hi k hk hx12 ⟨hfit, hrun⟩
    obtain ⟨hl, hc⟩ := seedKey_spec sds i k hk
    have heq := (eqRun_spec G sds[i]!.R sds[i]!.l (x + 1 - K12) sds[i]!.s).mp hrun
    have hcw : codeW G (x + 1 - K12) K12 = some k := by
      rw [codeW_congr G sds[i]!.R (x + 1 - K12) sds[i]!.s K12 (fun t ht => heq t (by omega))]; exact hc
    have hacgt := codeW_acgt G (x + 1 - K12) K12 k hcw
    have hrunK := hR'.run K12 (Nat.le_refl _) hx12 hacgt
    have hc2 := hR'.code K12 hrunK
    rw [hcw, Nat.mod_eq_of_lt hlt] at hc2
    exact ⟨hrunK, (Option.some.inj hc2).symm⟩
  refine ⟨hR', ?_, ?_, ?_⟩ <;> unfold stepOut
  · split
    · rw [← Array.foldl_toList]
      exact (visit_fold G sds (x + 1 - K12) _ out hsz
        (fun e he => (kf e ((extract_sub ks _ _).subset he)).1)
        (kpw.sublist (extract_sub ks _ _))).1
    · exact hsz
  · intro i hi hki
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hki
    rw [tgt_succ, ← hkey i hi hki]
    split
    · next hA =>
      rw [← Array.foldl_toList]
      have hmemE : ∀ e, e ∈ (ks.extract (lbA ks (st'.1 * sds.size) 0 ks.size)
          (lbA ks ((st'.1 + 1) * sds.size) 0 ks.size)).toList ↔
          e ∈ ks.toList ∧ st'.1 * sds.size ≤ e ∧ e < (st'.1 + 1) * sds.size :=
        fun e => mem_lb_extract ks hinc _ _ e
      obtain ⟨-, vget⟩ := visit_fold G sds (x + 1 - K12) _ out hsz
        (fun e he => (kf e ((hmemE e).mp he).1).1)
        (kpw.sublist (extract_sub ks _ _))
      rw [vget i hi]
      have hex : (∃ e ∈ (ks.extract (lbA ks (st'.1 * sds.size) 0 ks.size)
          (lbA ks ((st'.1 + 1) * sds.size) 0 ks.size)).toList, e % sds.size = i) ↔ k = st'.1 := by
        constructor
        · rintro ⟨e, he, hei⟩
          obtain ⟨hk1, hlo, hhi⟩ := (hmemE e).mp he
          have := (kf e hk1).2.1
          rw [hei, hk] at this
          have hed : e / sds.size = st'.1 := Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using hlo)
            (by simpa [Nat.mul_comm] using hhi)
          rw [← hed]; exact Option.some.inj this
        · intro hks'
          refine ⟨k * sds.size + i, (hmemE _).mpr ⟨?_, ?_, ?_⟩, (key_div_mod k i _ hi).1⟩
          · rw [← hks, mem_batchKeys]; exact ⟨i, hi, k, hk, rfl⟩
          · rw [hks']; omega
          · rw [hks', Nat.succ_mul]; omega
      by_cases hc : x + 1 - K12 + sds[i]!.l ≤ G.size ∧ eqRun G sds[i]!.R (x + 1 - K12) sds[i]!.s sds[i]!.l = true
      · have hx12 : K12 ≤ x + 1 := by have := hR'.le_x; omega
        obtain ⟨-, hst⟩ := code_of i hi k hk hx12 hc
        rw [if_pos ⟨hex.mpr hst.symm, hc⟩, if_pos ⟨hx12, hc⟩]
        simp
      · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2)]
        simp
    · next hA =>
      have : ¬ (K12 ≤ x + 1 ∧ (x + 1 - K12 + sds[i]!.l ≤ G.size ∧
          eqRun G sds[i]!.R (x + 1 - K12) sds[i]!.s sds[i]!.l = true)) := by
        rintro ⟨hx12, hc⟩
        obtain ⟨hrK, hst⟩ := code_of i hi k hk hx12 hc
        apply hA
        refine ⟨hrK, ?_⟩
        have := htbl (k * sds.size + i) (by rw [← hks, mem_batchKeys]; exact ⟨i, hi, k, hk, rfl⟩)
        rw [(key_div_mod k i _ hi).2] at this
        rw [hst]; exact this
      rw [if_neg this]; simp
  · intro i hi hnk
    rw [← hnokey i hi hnk]
    split
    · rw [← Array.foldl_toList]
      have hmemE : ∀ e, e ∈ (ks.extract (lbA ks (st'.1 * sds.size) 0 ks.size)
          (lbA ks ((st'.1 + 1) * sds.size) 0 ks.size)).toList ↔
          e ∈ ks.toList ∧ st'.1 * sds.size ≤ e ∧ e < (st'.1 + 1) * sds.size :=
        fun e => mem_lb_extract ks hinc _ _ e
      obtain ⟨-, vget⟩ := visit_fold G sds (x + 1 - K12) _ out hsz
        (fun e he => (kf e ((hmemE e).mp he).1).1)
        (kpw.sublist (extract_sub ks _ _))
      rw [vget i hi, if_neg]
      rintro ⟨⟨e, he, hei⟩, -⟩
      have := (kf e ((hmemE e).mp he).1).2.1
      rw [hei] at this
      rw [this] at hnk
      cases hnk
    · rfl

theorem batchAux_spec (hS : 0 < sds.size) :
    ∀ d x st out, G.size - x = d → x ≤ G.size → BInv G sds x st out →
      BInv G sds G.size (0, 0) (batchAux G sds (batchKeys sds) (batchTbl (batchKeys sds) sds.size) x st out) ∨
      (∃ st', BInv G sds G.size st' (batchAux G sds (batchKeys sds) (batchTbl (batchKeys sds) sds.size) x st out)) := by
  intro d
  induction d with
  | zero =>
    intro x st out hd hx h
    rw [batchAux_unfold, if_neg (by omega)]
    have : x = G.size := by omega
    subst this
    exact Or.inr ⟨st, h⟩
  | succ d ih =>
    intro x st out hd hx h
    rw [batchAux_unfold, if_pos (by omega)]
    exact ih (x + 1) _ _ (by omega) (by omega) (binv_step G sds hS x st out (by omega) h)

/-- **The batch scan gives every seed exactly its `scanL` anchors.** -/
theorem batchScan_eq (i : Nat) (hi : i < sds.size) :
    (batchScan G sds)[i]! = scanL G sds[i]!.R sds[i]!.s sds[i]!.l sds[i]!.base := by
  have hS : 0 < sds.size := by omega
  have h0 : BInv G sds 0 (0, 0) ((Array.range sds.size).map fun i =>
      if (seedKey sds[i]!).isSome then #[] else scanL G sds[i]!.R sds[i]!.s sds[i]!.l sds[i]!.base) := by
    refine ⟨rollOk_zero G, by simp, fun j hj hk => ?_, fun j hj hk => ?_⟩
    · rw [getElem!_pos _ j (by simpa using hj)]
      simp only [Array.getElem_map, Array.getElem_range, hk, if_true]
      unfold tgt
      rw [show 0 + 1 - K12 = 0 by rfl]; simp
    · rw [getElem!_pos _ j (by simpa using hj)]
      simp only [Array.getElem_map, Array.getElem_range, hk]
      rfl
  have hfin : ∃ st', BInv G sds G.size st' (batchScan G sds) := by
    rcases batchAux_spec G sds hS _ 0 (0, 0) _ rfl (Nat.zero_le _) h0 with h | h
    · exact ⟨_, h⟩
    · exact h
  obtain ⟨st', hb⟩ := hfin
  cases hk : (seedKey sds[i]!).isSome with
  | true =>
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hk
    apply Array.ext'
    rw [hb.key i hi hk, tgt_final G sds i (seedKey_spec sds i k hk').1]
  | false => exact hb.nokey i hi hk

end main2

end MapSpec.Fast

#print axioms MapSpec.Fast.batchScan_eq
