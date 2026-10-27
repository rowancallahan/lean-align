import MapperK250Chunk
import MapperK250Sel
import MapperFastKernel

/-!
# Word loops = byte loops

`hamA_eq` (`hamming`), `fwdA_eq` / `fwdK_eq` (`fwdMis`), `bwdA_eq` / `bwdK_eq` (`bwdMis`)
on read letters whose genome letters lie in flagged blocks (`WOk`, `WOkB`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- Word path conditions for read letters `[0, stop)` against the genome at `st + ·`. -/
def WOk (R G : ByteArray) (P : PGen) (st stop : Nat) : Prop :=
  Rep P G ∧ (packRP R).ok = true ∧ stop ≤ R.size ∧ st + stop ≤ P.n ∧
    ∀ x, x < stop → P.w.get! (17 * ((P.o + st + x) / 64)) = 1

/-- Read letters `[lo, n)` against the genome at `d + ·` (the end diagonal). -/
def WOkB (R G : ByteArray) (P : PGen) (d lo : Nat) : Prop :=
  Rep P G ∧ (packRP R).ok = true ∧ d + R.size ≤ P.n ∧
    ∀ x, lo ≤ x → x < R.size → P.w.get! (17 * ((P.o + d + x) / 64)) = 1

/-! ## Helpers -/

/-- `p x` restricted to `x ∈ [A, B)`. -/
def qw (A B : Nat) (p : Nat → Bool) (x : Nat) : Bool := decide (A ≤ x) && decide (x < B) && p x

theorem cntNZ_of_dig (p : Nat → Bool) : ∀ (c x i : Nat),
    (∀ t, t < c → dig x t = if p (i + t) then 1 else 0) → cntNZ c x = cntP p i c := by
  intro c
  induction c with
  | zero => intros; rfl
  | succ c ih =>
    intro x i h
    rw [cntNZ, cntP, ih (x / 4) (i + 1) (fun t ht => by
      rw [dig_div4, h (t + 1) (by omega), show i + (t + 1) = i + 1 + t by omega])]
    have h0 := h 0 (by omega)
    simp only [dig, Nat.pow_zero, Nat.div_one, Nat.add_zero] at h0
    rw [h0]
    cases p i <;> simp

theorem cntP_window (p : Nat → Bool) (A B i n : Nat) :
    cntP (qw A B p) i n = cntP p (max A i) (min B (i + n) - max A i) := by
  by_cases hLU : max A i ≤ min B (i + n)
  · have e : n = (max A i - i) + ((min B (i + n) - max A i) + (i + n - min B (i + n))) := by omega
    conv => lhs; rw [e]
    rw [cntP_add, cntP_add, show i + (max A i - i) = max A i by omega,
      cntP_zero_of _ i _ (fun k h1 h2 => by simp [qw]; omega),
      cntP_zero_of _ (max A i + (min B (i + n) - max A i)) _ (fun k h1 h2 => by simp [qw]; omega),
      cntP_congr _ p _ _ (fun k h1 h2 => by
        have : A ≤ k := by omega
        have : k < B := by omega
        simp [qw, *])]
    omega
  · rw [show min B (i + n) - max A i = 0 by omega,
      cntP_zero_of _ i _ (fun k h1 h2 => by simp [qw]; omega)]
    rfl

theorem cntP_one (p : Nat → Bool) (i : Nat) : cntP p i 1 = if p i then 1 else 0 := by
  simp [cntP]

/-- Characterization of the `k`-th mismatch from the left. -/
def FSpec (p : Nat → Bool) (i0 stop k F : Nat) : Prop :=
  i0 ≤ F ∧ F ≤ stop ∧ ∀ i, i0 ≤ i → i ≤ stop → (cntP p i0 (i - i0) < k ↔ i ≤ F)

theorem FSpec_unique (p : Nat → Bool) (i0 stop k F F' : Nat) (h : FSpec p i0 stop k F)
    (h' : FSpec p i0 stop k F') : F = F' := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  have x1 := (b3 F a1 a2).1 ((a3 F a1 a2).2 (Nat.le_refl _))
  have x2 := (a3 F' b1 b2).1 ((b3 F' b1 b2).2 (Nat.le_refl _))
  omega

/-- Characterization of one past the `k`-th mismatch from the right. -/
def BSpec (p : Nat → Bool) (lo E k B : Nat) : Prop :=
  lo ≤ B ∧ B ≤ E ∧ ∀ i, lo ≤ i → i ≤ E → (cntP p i (E - i) < k ↔ B ≤ i)

theorem BSpec_unique (p : Nat → Bool) (lo E k B B' : Nat) (h : BSpec p lo E k B)
    (h' : BSpec p lo E k B') : B = B' := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  have x1 := (b3 B a1 a2).1 ((a3 B a1 a2).2 (Nat.le_refl _))
  have x2 := (a3 B' b1 b2).1 ((b3 B' b1 b2).2 (Nat.le_refl _))
  omega

/-- Chunk digits, forward scan. -/
theorem fdig (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (j t : Nat) (ht : t < 32) :
    dig (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + st) / 32 + j))
        (gword P.w ((P.o + st) / 32 + j + 1)) ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64
        (64 - 2 * ((P.o + st) % 32)).toUInt64)) (stop - 32 * j)).toNat t =
      if qw 0 stop (fun x => R.get! x != G.get! (st + x)) (32 * j + t) then 1 else 0 := by
  obtain ⟨hP, hok, hs, hn, hf⟩ := h
  rw [lowF_dig _ _ _ ht, fold_dig _ _ ht]
  by_cases h1 : t < stop - 32 * j
  · rw [if_pos h1]
    have hfl := hf (32 * j + t) (by omega)
    rw [← Nat.add_assoc] at hfl
    have hc := chunk_dig R G P hP hok st j t ht (by omega) (by omega) hfl
    have hlt : 32 * j + t < stop := by omega
    by_cases hm : R.get! (32 * j + t) = G.get! (st + (32 * j + t))
    · rw [if_pos (hc.2 (by rw [hm, Nat.add_assoc]))]
      simp [qw, hm]
    · rw [if_neg (fun hz => hm (by rw [hc.1 hz, Nat.add_assoc]))]
      simp [qw, hm, hlt]
  · rw [if_neg h1]
    have : ¬ (32 * j + t < stop) := by omega
    simp [qw, this]

/-- Chunk digits, backward scan. -/
theorem bdig (R G : ByteArray) (P : PGen) (d lo : Nat) (h : WOkB R G P d lo) (j t : Nat) (ht : t < 32) :
    dig (highF (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + d) / 32 + j))
        (gword P.w ((P.o + d) / 32 + j + 1)) ((P.o + d) % 32) (2 * ((P.o + d) % 32)).toUInt64
        (64 - 2 * ((P.o + d) % 32)).toUInt64)) (R.size - 32 * j)) (lo - 32 * j)).toNat t =
      if qw lo R.size (fun x => R.get! x != G.get! (d + x)) (32 * j + t) then 1 else 0 := by
  obtain ⟨hP, hok, hn, hf⟩ := h
  rw [highF_dig _ _ _ ht]
  by_cases h0 : t < lo - 32 * j
  · rw [if_pos h0]
    have : ¬ (lo ≤ 32 * j + t) := by omega
    simp [qw, this]
  rw [if_neg h0, lowF_dig _ _ _ ht, fold_dig _ _ ht]
  by_cases h1 : t < R.size - 32 * j
  · rw [if_pos h1]
    have hfl := hf (32 * j + t) (by omega) (by omega)
    rw [← Nat.add_assoc] at hfl
    have hc := chunk_dig R G P hP hok d j t ht (by omega) (by omega) hfl
    have hlt : 32 * j + t < R.size := by omega
    have hle : lo ≤ 32 * j + t := by omega
    by_cases hm : R.get! (32 * j + t) = G.get! (d + (32 * j + t))
    · rw [if_pos (hc.2 (by rw [hm, Nat.add_assoc]))]
      simp [qw, hm]
    · rw [if_neg (fun hz => hm (by rw [hc.1 hz, Nat.add_assoc]))]
      simp [qw, hm, hlt, hle]
  · rw [if_neg h1]
    have : ¬ (32 * j + t < R.size) := by omega
    simp [qw, this]

theorem fcnt (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (j : Nat) :
    cnt64 (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + st) / 32 + j))
        (gword P.w ((P.o + st) / 32 + j + 1)) ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64
        (64 - 2 * ((P.o + st) % 32)).toUInt64)) (stop - 32 * j)) =
      cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j)) := by
  rw [cnt64_eq, cntNZ_of_dig _ 32 _ (32 * j) (fun t ht => fdig R G P st stop h j t ht), cntP_window,
    show max 0 (32 * j) = 32 * j by omega,
    show min stop (32 * j + 32) - 32 * j = min 32 (stop - 32 * j) by omega]

theorem hamW_inv (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (lim : Nat) :
    ∀ n j acc, stop - 32 * j = n → acc ≤ lim →
      hamW (packRP R).w P.w ((P.o + st) / 32) ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64
        (64 - 2 * ((P.o + st) % 32)).toUInt64 lim stop j acc (gword P.w ((P.o + st) / 32 + j)) =
      min (acc + cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (stop - 32 * j)) (lim + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j acc hn hacc
    rw [hamW]
    by_cases hlt : 32 * j < stop
    · rw [if_pos hlt]
      simp only []
      rw [fcnt R G P st stop h j]
      have hsplit : cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (stop - 32 * j) =
          cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j)) +
          cntP (fun x => R.get! x != G.get! (st + x)) (32 * (j + 1)) (stop - 32 * (j + 1)) := by
        by_cases hs : 32 ≤ stop - 32 * j
        · rw [show min 32 (stop - 32 * j) = 32 by omega,
            show stop - 32 * j = 32 + (stop - 32 * (j + 1)) by omega, cntP_add,
            show 32 * j + 32 = 32 * (j + 1) by omega]
        · rw [show min 32 (stop - 32 * j) = stop - 32 * j by omega, show stop - 32 * (j + 1) = 0 by omega]
          rfl
      by_cases hl : lim < acc + cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j))
      · rw [if_pos hl]; omega
      · rw [if_neg hl, Nat.add_assoc ((P.o + st) / 32) j 1,
          ih (stop - 32 * (j + 1)) (by omega) (j + 1) _ rfl (by omega)]
        omega
    · rw [if_neg hlt, show stop - 32 * j = 0 by omega]
      simp [cntP]; omega

theorem hamA_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (lim : Nat) :
    hamA (packRP R).w P.w (P.o + st) lim stop = hamming R G st lim 0 stop 0 := by
  have h0 := hamW_inv R G P st stop h lim (stop - 32 * 0) 0 0 rfl (Nat.zero_le _)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.sub_zero, Nat.zero_add] at h0
  rw [hamming_spec R G st lim stop (stop - 0) 0 0 rfl (Nat.zero_le _)]
  simp only [hamA, Nat.sub_zero, Nat.zero_add]
  exact h0

theorem fwdW_inv (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) :
    ∀ n j k, stop - 32 * j = n → 32 * j ≤ stop → 1 ≤ k →
      FSpec (fun x => R.get! x != G.get! (st + x)) (32 * j) stop k
        (fwdW (packRP R).w P.w ((P.o + st) / 32) ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64
          (64 - 2 * ((P.o + st) % 32)).toUInt64 stop j k (gword P.w ((P.o + st) / 32 + j))) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j k hn hj hk
    rw [fwdW]
    by_cases hlt : 32 * j < stop
    · rw [if_pos hlt]
      simp only []
      rw [fcnt R G P st stop h j]
      generalize hC : cntP (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j)) = C
      by_cases hck : C < k
      · rw [if_pos hck, Nat.add_assoc ((P.o + st) / 32) j 1]
        by_cases hj1 : 32 * (j + 1) ≤ stop
        · obtain ⟨a1, a2, a3⟩ := ih (stop - 32 * (j + 1)) (by omega) (j + 1) (k - C) rfl hj1 (by omega)
          refine ⟨by omega, a2, fun i h1 h2 => ?_⟩
          by_cases hi : i ≤ 32 * (j + 1)
          · have := cntP_mono (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j))
              (32 * j) (i - 32 * j) (Nat.le_refl _) (by omega)
            omega
          · have := a3 i (by omega) h2
            rw [show i - 32 * j = 32 + (i - 32 * (j + 1)) by omega, cntP_add,
              show 32 * j + 32 = 32 * (j + 1) by omega]
            rw [show min 32 (stop - 32 * j) = 32 by omega] at hC
            omega
        · rw [fwdW, if_neg (by omega)]
          refine ⟨by omega, Nat.le_refl _, fun i h1 h2 => ?_⟩
          have := cntP_mono (fun x => R.get! x != G.get! (st + x)) (32 * j) (min 32 (stop - 32 * j))
              (32 * j) (i - 32 * j) (Nat.le_refl _) (by omega)
          omega
      · rw [if_neg hck]
        have hC' := hC
        rw [← fcnt R G P st stop h j, cnt64_eq] at hC'
        have hbin : Bin (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + st) / 32 + j))
            (gword P.w ((P.o + st) / 32 + j + 1)) ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64
            (64 - 2 * ((P.o + st) % 32)).toUInt64)) (stop - 32 * j)) := fun t ht => by
          rw [fdig R G P st stop h j t ht]; split <;> omega
        obtain ⟨s1, s2, s3⟩ := selLow_spec _ hbin (k - 1) (by omega)
        generalize selLow _ (k - 1) = σ at s1 s2 s3 ⊢
        rw [fdig R G P st stop h j σ s1] at s3
        have hq : qw 0 stop (fun x => R.get! x != G.get! (st + x)) (32 * j + σ) = true := by
          revert s3; split <;> simp_all
        simp only [qw, Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨⟨_, hσ⟩, hmis⟩ := hq
        rw [cntNZ_of_dig _ σ _ (32 * j) (fun t ht => fdig R G P st stop h j t (by omega)), cntP_window,
          show max 0 (32 * j) = 32 * j by omega,
          show min stop (32 * j + σ) - 32 * j = σ by omega] at s2
        refine ⟨by omega, by omega, fun i h1 h2 => ?_⟩
        by_cases hi : i ≤ 32 * j + σ
        · have := cntP_mono (fun x => R.get! x != G.get! (st + x)) (32 * j) σ
              (32 * j) (i - 32 * j) (Nat.le_refl _) (by omega)
          omega
        · have := cntP_mono (fun x => R.get! x != G.get! (st + x)) (32 * j) (i - 32 * j)
              (32 * j) (σ + 1) (Nat.le_refl _) (by omega)
          rw [cntP_add, cntP_one, if_pos hmis] at this
          omega
    · rw [if_neg hlt]
      refine ⟨hj, Nat.le_refl _, fun i h1 h2 => ?_⟩
      rw [show i - 32 * j = 0 by omega]
      simp [cntP]; omega

theorem fwdA_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (k : Nat) (hk : 1 ≤ k) :
    fwdA (packRP R).w P.w (P.o + st) stop k = fwdMis R G st stop 0 k := by
  have h0 := fwdW_inv R G P st stop h (stop - 32 * 0) 0 k rfl (by omega) hk
  simp only [Nat.add_zero, Nat.mul_zero] at h0
  have h1 := fwdMis_spec R G st stop (stop - 0) 0 k rfl (Nat.zero_le _) hk
  exact FSpec_unique _ 0 stop k _ _ h0 h1

theorem bcnt (R G : ByteArray) (P : PGen) (d lo : Nat) (h : WOkB R G P d lo) (j c : Nat) (hc : c ≤ 32) :
    cntNZ c (highF (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + d) / 32 + j))
        (gword P.w ((P.o + d) / 32 + j + 1)) ((P.o + d) % 32) (2 * ((P.o + d) % 32)).toUInt64
        (64 - 2 * ((P.o + d) % 32)).toUInt64)) (R.size - 32 * j)) (lo - 32 * j)).toNat =
      cntP (fun x => R.get! x != G.get! (d + x)) (max lo (32 * j))
        (min R.size (32 * j + c) - max lo (32 * j)) := by
  rw [cntNZ_of_dig _ c _ (32 * j) (fun t ht => bdig R G P d lo h j t (by omega)), cntP_window]

theorem bwdW_inv (R G : ByteArray) (P : PGen) (d lo : Nat) (h : WOkB R G P d lo) :
    ∀ j k, 1 ≤ k → 32 * j < R.size → lo < min R.size (32 * j + 32) →
      BSpec (fun x => R.get! x != G.get! (d + x)) lo (min R.size (32 * j + 32)) k
        (bwdW (packRP R).w P.w ((P.o + d) / 32) ((P.o + d) % 32) (2 * ((P.o + d) % 32)).toUInt64
          (64 - 2 * ((P.o + d) % 32)).toUInt64 lo R.size j k (gword P.w ((P.o + d) / 32 + j + 1))) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro k hk hj hlo
    rw [bwdW.eq_def]
    simp only []
    rw [cnt64_eq, bcnt R G P d lo h j 32 (Nat.le_refl _)]
    have hm := bcnt R G P d lo h j 32 (Nat.le_refl _)
    generalize hC : cntP (fun x => R.get! x != G.get! (d + x)) (max lo (32 * j))
      (min R.size (32 * j + 32) - max lo (32 * j)) = C at hm ⊢
    by_cases hck : k ≤ C
    · rw [if_pos hck]
      have hbin : Bin (highF (lowF (fold ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + d) / 32 + j))
          (gword P.w ((P.o + d) / 32 + j + 1)) ((P.o + d) % 32) (2 * ((P.o + d) % 32)).toUInt64
          (64 - 2 * ((P.o + d) % 32)).toUInt64)) (R.size - 32 * j)) (lo - 32 * j)) := fun t ht => by
        rw [bdig R G P d lo h j t ht]; split <;> omega
      obtain ⟨s1, s2, s3⟩ := selHigh_spec _ hbin (k - 1) (by omega)
      generalize selHigh _ (k - 1) = σ at s1 s2 s3 ⊢
      rw [bcnt R G P d lo h j (σ + 1) (by omega), hm] at s2
      rw [bdig R G P d lo h j _ s1] at s3
      have hq : qw lo R.size (fun x => R.get! x != G.get! (d + x)) (32 * j + σ) = true := by
        revert s3; split <;> simp_all
      simp only [qw, Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨hσ0, hσ⟩, hmis⟩ := hq
      have hsplit := cntP_add (fun x => R.get! x != G.get! (d + x)) (max lo (32 * j))
        (32 * j + σ + 1 - max lo (32 * j)) (min R.size (32 * j + 32) - (32 * j + σ + 1))
      rw [show 32 * j + σ + 1 - max lo (32 * j) + (min R.size (32 * j + 32) - (32 * j + σ + 1)) =
          min R.size (32 * j + 32) - max lo (32 * j) by omega,
        show max lo (32 * j) + (32 * j + σ + 1 - max lo (32 * j)) = 32 * j + σ + 1 by omega, hC] at hsplit
      rw [show min R.size (32 * j + (σ + 1)) = 32 * j + σ + 1 by omega] at s2
      refine ⟨by omega, by omega, fun i h1 h2 => ?_⟩
      by_cases hi : 32 * j + σ + 1 ≤ i
      · have := cntP_mono (fun x => R.get! x != G.get! (d + x)) (32 * j + σ + 1)
          (min R.size (32 * j + 32) - (32 * j + σ + 1)) i (min R.size (32 * j + 32) - i) hi (by omega)
        omega
      · have := cntP_mono (fun x => R.get! x != G.get! (d + x)) i (min R.size (32 * j + 32) - i)
          (32 * j + σ) (1 + (min R.size (32 * j + 32) - (32 * j + σ + 1))) (by omega) (by omega)
        rw [cntP_add, cntP_one, if_pos hmis] at this
        omega
    · rw [if_neg hck]
      by_cases hjl : 32 * j ≤ lo
      · rw [if_pos hjl]
        rw [show max lo (32 * j) = lo by omega] at hC
        refine ⟨Nat.le_refl _, by omega, fun i h1 h2 => ⟨fun _ => h1, fun _ => ?_⟩⟩
        have := cntP_mono (fun x => R.get! x != G.get! (d + x)) lo (min R.size (32 * j + 32) - lo) i
          (min R.size (32 * j + 32) - i) h1 (by omega)
        omega
      · rw [if_neg hjl]
        obtain _ | j' := j
        · omega
        · simp only []
          have hE : min R.size (32 * j' + 32) = 32 * (j' + 1) := by omega
          obtain ⟨a1, a2, a3⟩ := ih j' (by omega) (k - C) (by omega) (by omega) (by omega)
          rw [hE] at a2 a3
          rw [show (P.o + d) / 32 + j' + 1 = (P.o + d) / 32 + (j' + 1) by omega] at a1 a2 a3
          rw [show max lo (32 * (j' + 1)) = 32 * (j' + 1) by omega] at hC
          refine ⟨a1, by omega, fun i h1 h2 => ?_⟩
          by_cases hi : i ≤ 32 * (j' + 1)
          · have := a3 i h1 hi
            rw [show min R.size (32 * (j' + 1) + 32) - i =
                (32 * (j' + 1) - i) + (min R.size (32 * (j' + 1) + 32) - 32 * (j' + 1)) by omega,
              cntP_add, show i + (32 * (j' + 1) - i) = 32 * (j' + 1) by omega, hC]
            omega
          · have := cntP_mono (fun x => R.get! x != G.get! (d + x)) (32 * (j' + 1))
              (min R.size (32 * (j' + 1) + 32) - 32 * (j' + 1)) i
              (min R.size (32 * (j' + 1) + 32) - i) (by omega) (by omega)
            omega

theorem bwdA_eq (R G : ByteArray) (P : PGen) (st len lo : Nat) (hd : R.size ≤ st + len)
    (h : WOkB R G P (st + len - R.size) lo) (k : Nat) (hk : 1 ≤ k) :
    bwdA (packRP R).w P.w (P.o + (st + len - R.size)) lo R.size k = bwdMis R G st len lo R.size k := by
  generalize hdd : st + len - R.size = d at h
  have hpred : (fun x => R.get! x != G.get! (st + len + x - R.size)) = (fun x => R.get! x != G.get! (d + x)) := by
    funext x; rw [show st + len + x - R.size = d + x by omega]
  simp only [bwdA]
  by_cases hlo : lo < R.size
  · have h0 := bwdW_inv R G P d lo h ((R.size - 1) / 32) k hk (by omega) (by omega)
    rw [show min R.size (32 * ((R.size - 1) / 32) + 32) = R.size by omega] at h0
    have h1 := bwdMis_spec R G st len lo (R.size - lo) R.size k rfl (by omega) hk
    rw [hpred] at h1
    exact BSpec_unique _ lo R.size k _ _ h0 h1
  · rw [bwdMis, if_neg hlo, bwdW.eq_def]
    simp only []
    rw [cnt64_eq, bcnt R G P d lo h _ 32 (Nat.le_refl _),
      show min R.size (32 * ((R.size - 1) / 32) + 32) - max lo (32 * ((R.size - 1) / 32)) = 0 by omega]
    rw [if_neg (by simp [cntP]; omega), if_pos (by omega)]

theorem fwdK_eq (R G : ByteArray) (P : PGen) (st stop : Nat) (h : WOk R G P st stop) (k : Nat) (hk : 1 ≤ k) :
    fwdK R G (packRP R).w P.w (P.o + st) st stop k = fwdMis R G st stop 0 k := by
  simp only [fwdK]
  split
  · rename_i hf
    generalize hp : min stop pre = p at hf
    have hps : p ≤ stop := by rw [← hp]; exact Nat.min_le_left _ _
    obtain ⟨a1, a2, a3⟩ := fwdMis_spec R G st p (p - 0) 0 k rfl (Nat.zero_le _) hk
    have h1 := fwdMis_spec R G st stop (stop - 0) 0 k rfl (Nat.zero_le _) hk
    refine FSpec_unique _ 0 stop k _ _ ⟨a1, by omega, fun i h1 h2 => ?_⟩ h1
    by_cases hi : i ≤ p
    · exact a3 i h1 hi
    · have := mt (a3 p (Nat.zero_le _) (Nat.le_refl _)).1 (by omega)
      have := cntP_mono (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) 0 (p - 0) (Nat.le_refl _) (by omega)
      omega
  · exact fwdA_eq R G P st stop h k hk

theorem bwdK_eq (R G : ByteArray) (P : PGen) (st len lo : Nat) (hd : R.size ≤ st + len)
    (h : WOkB R G P (st + len - R.size) lo) (k : Nat) (hk : 1 ≤ k) :
    bwdK R G (packRP R).w P.w (P.o + (st + len - R.size)) st len lo k = bwdMis R G st len lo R.size k := by
  simp only [bwdK]
  split
  · rename_i hb
    generalize hq : max lo (R.size - pre) = q at hb
    have hlq : lo ≤ q := by rw [← hq]; exact Nat.le_max_left _ _
    by_cases hqe : q ≤ R.size
    · obtain ⟨a1, a2, a3⟩ := bwdMis_spec R G st len q (R.size - q) R.size k rfl hqe hk
      have h1 := bwdMis_spec R G st len lo (R.size - lo) R.size k rfl (by omega) hk
      refine BSpec_unique _ lo R.size k _ _ ⟨by omega, a2, fun i h1 h2 => ?_⟩ h1
      by_cases hi : q ≤ i
      · exact a3 i hi h2
      · have := mt (a3 q (Nat.le_refl _) hqe).1 (by omega)
        have := cntP_mono (fun x => R.get! x != G.get! (st + len + x - R.size)) i (R.size - i) q
          (R.size - q) (by omega) (by omega)
        omega
    · rw [bwdMis, if_neg (by omega)] at hb
      omega
  · exact bwdA_eq R G P st len lo hd h k hk

end MapSpec.Fast
