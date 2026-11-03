import TierHeur

/-!
# `bandCellsJ` = `bandCells` (so `bandDPg true = bandDPg false`)

`bandCellsJ` jumps over the cells `bandCells` skips. Started at the same row `i` and diagonal `k`,
`bandCellsJ` with any fuel ≥ `stepsLeft` returns what `bandCells` returns with fuel `stepsLeft` (the steps
`bandCells` needs to the end of row `n`), when the counters cannot overflow (`Bnd`: `K < 2^30`,
`c0s ≤ 2^22`, `n, m < 2^20`, `lim ≤ 2^23`; `bandDPg` guarantees all but `K`, i.e. `w < 2^29`).

  * a skip step is the same in both (`bc_skip`);
  * cells before `rowStart` are skipped by `bandCells` (`rowStart_skips`, `bc_prefix`);
  * after a skip for `col > m` or (`k ≥ pb`, `hl`, `e` over the limit) `bandCells` skips the rest of the row
    (`bc_rest`: the column grows with `k`; `hl`, `e` become `INF = 2^24 ≥ lim`);
  * `bandCells`' fuel ends exactly after row `n`, where `bandCellsJ` stops by `i == n`.
-/

namespace TierHeur

/-- Steps `bandCells` takes from row `i`, diagonal `k` to the end of row `n`. -/
def stepsLeft (n K i k : Nat) : Nat := (n - i) * (K + 1) + (K + 1 - k)

/-- No counter overflows. -/
structure Bnd (K c0s m lim n : UInt32) : Prop where
  hK : K.toNat < 2 ^ 30
  hc : c0s.toNat ≤ 2 ^ 22
  hn : n.toNat < 2 ^ 20
  hm : m.toNat < 2 ^ 20
  hl : lim.toNat ≤ 2 ^ 23

/-- `bandCells`' skip test at cell `(i, k)`. -/
def skipC (c0s m lim i k hl e pa pb : UInt32) : Bool :=
  i + k + c0s < 1048576 || i + k + c0s > 1048576 + m || k + 1 < pa || (k ≥ pb && hl + 8 ≥ lim && e + 2 ≥ lim)

theorem bc_skip (X W : ByteArray) (K c0s m lim : UInt32) (f : Nat) (i k hl e pa pb nlo nhi : UInt32)
    (H F : Array UInt32) (tb : ByteArray) (hk : (k == K) = false) (hs : skipC c0s m lim i k hl e pa pb = true) :
    bandCells X W K c0s m lim (f + 1) i k hl e pa pb nlo nhi H F tb =
      bandCells X W K c0s m lim f i (k + 1) 16777216 16777216 pa pb nlo nhi H F tb := by
  unfold skipC at hs
  simp only [bandCells, hk, hs, Bool.false_eq_true, ↓reduceIte]

theorem bc_atK (X W : ByteArray) (K c0s m lim : UInt32) (f : Nat) (i hl e hl' e' pa pb nlo nhi : UInt32)
    (H F : Array UInt32) (tb : ByteArray) :
    bandCells X W K c0s m lim f i K hl e pa pb nlo nhi H F tb = bandCells X W K c0s m lim f i K hl' e' pa pb nlo nhi H F tb := by
  cases f <;> simp [bandCells]

/-- UInt32 order and sums as `Nat` (no overflow under the bounds in context), then `omega`. -/
macro "u32" : tactic => `(tactic| (simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_add,
  gt_iff_lt, ge_iff_le, UInt32.reduceToNat, ← UInt32.toNat_inj] at *; omega))

theorem u_ne (a b : UInt32) (h : a.toNat ≠ b.toNat) : (a == b) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => h (by rw [e])

/-- After a skip for `col > m`, or right of `pb` with `hl`, `e` over the limit, `bandCells` skips the rest of
the row. -/
theorem bc_rest (X W : ByteArray) (K c0s m lim : UInt32) (i pa pb nlo nhi : UInt32) (H F : Array UInt32)
    (tb : ByteArray) (r : Nat) (hK : K.toNat < 2 ^ 30) (hc : c0s.toNat ≤ 2 ^ 22) (hm : m.toNat < 2 ^ 20)
    (hL : lim.toNat ≤ 2 ^ 23) (hi : i.toNat ≤ 2 ^ 20) :
    ∀ d (k hl e : UInt32), k.toNat + d = K.toNat →
    (i + k + c0s > 1048576 + m ∨ (k ≥ pb ∧ hl + 8 ≥ lim ∧ e + 2 ≥ lim)) →
    bandCells X W K c0s m lim (d + r) i k hl e pa pb nlo nhi H F tb =
      bandCells X W K c0s m lim r i K 16777216 16777216 pa pb nlo nhi H F tb
  | 0, k, hl, e, hd, _ => by
    have : k = K := UInt32.toNat_inj.mp (by omega)
    subst this; rw [Nat.zero_add]; exact bc_atK ..
  | d + 1, k, hl, e, hd, hs => by
    have hsk : skipC c0s m lim i k hl e pa pb = true := by
      unfold skipC
      rcases hs with h | ⟨h1, h2, h3⟩
      · simp [h]
      · simp [h1, h2, h3]
    rw [show d + 1 + r = (d + r) + 1 by omega, bc_skip X W K c0s m lim _ i k hl e pa pb nlo nhi H F tb
      (u_ne _ _ (by omega)) hsk]
    have ek : (k + 1).toNat = k.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    apply bc_rest X W K c0s m lim i pa pb nlo nhi H F tb r hK hc hm hL hi d (k + 1) _ _ (by omega)
    rcases hs with h | ⟨h1, _, _⟩
    · left; u32
    · right; refine ⟨by u32, by u32, by u32⟩

theorem rowStart_nat (K c0s i pa : UInt32) (hc : c0s.toNat ≤ 2 ^ 22) (hi : i.toNat ≤ 2 ^ 20 + 1) :
    (rowStart K c0s i pa).toNat =
      min K.toNat (max (pa.toNat - 1) (1048576 - (i.toNat + c0s.toNat))) := by
  have ea : (if pa > 0 then pa - 1 else 0 : UInt32).toNat = pa.toNat - 1 := by
    split
    · rename_i h; rw [UInt32.toNat_sub_of_le _ _ (by u32)]; rfl
    · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at h; simp; omega
  have eic : (i + c0s).toNat = i.toNat + c0s.toNat := by rw [UInt32.toNat_add]; omega
  have eb : (if i + c0s < 1048576 then 1048576 - (i + c0s) else 0 : UInt32).toNat = 1048576 - (i.toNat + c0s.toNat) := by
    split
    · rename_i h; rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt h), eic]; rfl
    · rename_i h; rw [UInt32.lt_iff_toNat_lt, eic] at h; simp at h; simp; omega
  unfold rowStart
  dsimp only
  generalize (if pa > 0 then pa - 1 else 0 : UInt32) = a at ea
  generalize (if i + c0s < 1048576 then 1048576 - (i + c0s) else 0 : UInt32) = b at eb
  have emax : (max a b).toNat = max a.toNat b.toNat := by
    show (if a ≤ b then b else a).toNat = _
    split <;> rename_i h <;> rw [UInt32.le_iff_toNat_le] at h <;> omega
  have emin : (min K (max a b)).toNat = min K.toNat (max a b).toNat := by
    show (if K ≤ max a b then K else max a b).toNat = _
    split <;> rename_i h <;> rw [UInt32.le_iff_toNat_le] at h <;> omega
  rw [emin, emax, ea, eb]

/-- `bandCells` skips the cells of a row before `rowStart` (window column `< 0`, or left of `pa`). -/
theorem bc_prefix (X W : ByteArray) (K c0s m lim : UInt32) (i pa pb nlo nhi : UInt32) (H F : Array UInt32)
    (tb : ByteArray) (r : Nat) (hK : K.toNat < 2 ^ 30) (hc : c0s.toNat ≤ 2 ^ 22) (hi : i.toNat ≤ 2 ^ 20 + 1) :
    ∀ d (k : UInt32), k.toNat + d = (rowStart K c0s i pa).toNat →
    bandCells X W K c0s m lim (d + r) i k 16777216 16777216 pa pb nlo nhi H F tb =
      bandCells X W K c0s m lim r i (rowStart K c0s i pa) 16777216 16777216 pa pb nlo nhi H F tb
  | 0, k, hd => by
    have : k = rowStart K c0s i pa := UInt32.toNat_inj.mp (by omega)
    subst this; rw [Nat.zero_add]
  | d + 1, k, hd => by
    have ers := rowStart_nat K c0s i pa hc hi
    have hsk : skipC c0s m lim i k 16777216 16777216 pa pb = true := by
      unfold skipC
      by_cases h : k.toNat + 1 < pa.toNat
      · have : k + 1 < pa := by u32
        simp [this]
      · have : i + k + c0s < 1048576 := by u32
        simp [this]
    rw [show d + 1 + r = (d + r) + 1 by omega, bc_skip X W K c0s m lim _ i k _ _ pa pb nlo nhi H F tb
      (u_ne _ _ (by omega)) hsk]
    have ek : (k + 1).toNat = k.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    exact bc_prefix X W K c0s m lim i pa pb nlo nhi H F tb r hK hc hi d (k + 1) (by omega)

/-- **Simulation**: from row `i`, diagonal `k`, `bandCellsJ` with any fuel `≥ stepsLeft` returns what `bandCells`
returns with fuel `stepsLeft`. -/
theorem bandCellsJ_eq (X W : ByteArray) (K c0s m lim n : UInt32) (B : Bnd K c0s m lim n) :
    ∀ (fJ : Nat) (i k : UInt32), 1 ≤ i.toNat → i.toNat ≤ n.toNat → k.toNat ≤ K.toNat →
    stepsLeft n.toNat K.toNat i.toNat k.toNat ≤ fJ →
    ∀ (hl e pa pb nlo nhi : UInt32) (H F : Array UInt32) (tb : ByteArray),
    bandCellsJ X W K c0s m lim n fJ i k hl e pa pb nlo nhi H F tb =
      bandCells X W K c0s m lim (stepsLeft n.toNat K.toNat i.toNat k.toNat) i k hl e pa pb nlo nhi H F tb
  | 0, i, k, _, _, hk, hf => by unfold stepsLeft at hf; omega
  | f + 1, i, k, hi1, hin, hk, hf => by
    intro hl e pa pb nlo nhi H F tb
    have hK := B.hK; have hc := B.hc; have hn := B.hn; have hm := B.hm; have hL := B.hl
    by_cases hkK : k = K
    · subst hkK
      have e1 : stepsLeft n.toNat k.toNat i.toNat k.toNat = (n.toNat - i.toNat) * (k.toNat + 1) + 1 := by
        unfold stepsLeft; omega
      rw [e1]
      simp only [bandCellsJ, bandCells, beq_self_eq_true, ↓reduceIte]
      by_cases hnl : (nlo == k) = true
      · simp [hnl]
      · simp only [hnl, Bool.false_eq_true, ↓reduceIte]
        by_cases hni : i = n
        · subst hni; simp [bandCells]
        · have hni' : i.toNat < n.toNat := by
            have : i.toNat ≠ n.toNat := fun e => hni (UInt32.toNat_inj.mp e)
            omega
          simp only [u_ne i n (by omega), Bool.false_eq_true, ↓reduceIte]
          have ei : (i + 1).toNat = i.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
          have ers := rowStart_nat k c0s (i + 1) nlo hc (by omega)
          have hrs : (rowStart k c0s (i + 1) nlo).toNat ≤ k.toNat := by rw [ers]; exact Nat.min_le_left _ _
          have hmul : (n.toNat - i.toNat) * (k.toNat + 1) = (n.toNat - (i.toNat + 1)) * (k.toNat + 1) + (k.toNat + 1) := by
            rw [show n.toNat - i.toNat = (n.toNat - (i.toNat + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
          have hf' := hf
          unfold stepsLeft at hf'
          rw [bandCellsJ_eq X W k c0s m lim n B f (i + 1) _ (by omega) (by omega) hrs
            (by unfold stepsLeft; rw [ei]; omega)]
          have e2 : (n.toNat - i.toNat) * (k.toNat + 1) =
              (rowStart k c0s (i + 1) nlo).toNat + stepsLeft n.toNat k.toNat (i + 1).toNat (rowStart k c0s (i + 1) nlo).toNat := by
            unfold stepsLeft; rw [ei]
            have : n.toNat - i.toNat = (n.toNat - (i.toNat + 1)) + 1 := by omega
            rw [this, Nat.add_mul, Nat.one_mul]; omega
          rw [e2, bc_prefix X W k c0s m lim (i + 1) nlo nhi k 0 H F tb _ hK hc (by omega) _ 0 (by simp)]
    · have hkK' : k.toNat < K.toNat := by
        have : k.toNat ≠ K.toNat := fun e => hkK (UInt32.toNat_inj.mp e)
        omega
      have ek : (k + 1).toNat = k.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
      have e1 : stepsLeft n.toNat K.toNat i.toNat k.toNat = stepsLeft n.toNat K.toNat i.toNat (k + 1).toNat + 1 := by
        unfold stepsLeft; rw [ek]; omega
      have ih := bandCellsJ_eq X W K c0s m lim n B f i (k + 1) hi1 hin (by omega) (by omega)
      rw [e1]
      by_cases h1 : (i + k + c0s < 1048576 || k + 1 < pa) = true
      · have hs : skipC c0s m lim i k hl e pa pb = true := by
          unfold skipC; simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
          rcases h1 with h | h <;> simp [h]
        rw [bc_skip X W K c0s m lim _ i k hl e pa pb nlo nhi H F tb (u_ne _ _ (by omega)) hs, ← ih]
        simp only [bandCellsJ, u_ne k K (by omega), h1, Bool.false_eq_true, ↓reduceIte]
      · by_cases h2 : (i + k + c0s > 1048576 + m || (k ≥ pb && hl + 8 ≥ lim && e + 2 ≥ lim)) = true
        · have er : stepsLeft n.toNat K.toNat i.toNat (k + 1).toNat + 1 =
              (K.toNat - k.toNat) + stepsLeft n.toNat K.toNat i.toNat K.toNat := by
            unfold stepsLeft; rw [ek]; omega
          rw [er, bc_rest X W K c0s m lim i pa pb nlo nhi H F tb _ hK hc hm hL (by omega) _ k hl e (by omega)
            (by simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
                exact h2.imp id (fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩)),
            ← bandCellsJ_eq X W K c0s m lim n B f i K hi1 hin (Nat.le_refl _) (by unfold stepsLeft at hf ⊢; omega)]
          simp only [bandCellsJ, u_ne k K (by omega), Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          simp only [Bool.not_eq_true] at h1
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        · simp only [Bool.not_eq_true] at h1 h2
          have h3 : (i + k + c0s < 1048576 || i + k + c0s > 1048576 + m || k + 1 < pa ||
              (k ≥ pb && hl + 8 ≥ lim && e + 2 ≥ lim)) = false := by
            simp only [Bool.or_eq_false_iff] at h1 h2 ⊢; exact ⟨⟨⟨h1.1, h2.1⟩, h1.2⟩, h2.2⟩
          simp only [bandCellsJ, bandCells, u_ne k K (by omega), h1, h2, h3, Bool.false_eq_true, ↓reduceIte, ih]

theorem toU32_toNat (a : Nat) (h : a < 2 ^ 32) : a.toUInt32.toNat = a := by
  show (UInt32.ofNat a).toNat = a
  rw [UInt32.toNat_ofNat']; omega

/-- The call in `bandDPg`: `bandCellsJ` from row 1 at `rowStart` = `bandCells` from row 1 at diagonal 0. -/
theorem cells_eq (X W : ByteArray) (K n : Nat) (c0s m lim : UInt32) (hK : K < 2 ^ 30) (hn : n < 2 ^ 20)
    (hc : c0s.toNat ≤ 2 ^ 22) (hm : m.toNat < 2 ^ 20) (hl : lim.toNat ≤ 2 ^ 23)
    (hl0 e0 pa pb nlo nhi : UInt32) (H F : Array UInt32) (tb : ByteArray) (h16 : hl0 = 16777216) (e16 : e0 = 16777216) :
    bandCellsJ X W K.toUInt32 c0s m lim n.toUInt32 (n * (K + 1)) 1 (rowStart K.toUInt32 c0s 1 pa) hl0 e0
        pa pb nlo nhi H F tb =
      bandCells X W K.toUInt32 c0s m lim (n * (K + 1)) 1 0 hl0 e0 pa pb nlo nhi H F tb := by
  subst h16 e16
  have eK := toU32_toNat K (by omega)
  have en := toU32_toNat n (by omega)
  have B : Bnd K.toUInt32 c0s m lim n.toUInt32 := ⟨by omega, hc, by omega, hm, hl⟩
  have ers := rowStart_nat K.toUInt32 c0s 1 pa hc (by simp)
  have hrs : (rowStart K.toUInt32 c0s 1 pa).toNat ≤ K := by rw [ers, eK]; exact Nat.min_le_left _ _
  by_cases h0 : n = 0
  · subst h0; simp [bandCellsJ, bandCells]
  · have hmul : n * (K + 1) = (n - 1) * (K + 1) + (K + 1) := by
      rw [show n = (n - 1) + 1 by omega, Nat.add_mul, Nat.one_mul]; simp
    have e1 : (1 : UInt32).toNat = 1 := rfl
    rw [bandCellsJ_eq X W _ c0s m lim _ B _ 1 _ (by rw [e1]; omega) (by rw [e1, en]; omega) (by rw [eK]; exact hrs)
      (by simp only [stepsLeft]; rw [en, eK, e1]; omega)]
    have e2 : n * (K + 1) = (rowStart K.toUInt32 c0s 1 pa).toNat +
        stepsLeft n.toUInt32.toNat K.toUInt32.toNat (1 : UInt32).toNat (rowStart K.toUInt32 c0s 1 pa).toNat := by
      simp only [stepsLeft]; rw [en, eK, e1]; omega
    rw [e2, bc_prefix X W _ c0s m lim 1 pa pb nlo nhi H F tb _ (by omega) hc (by rw [e1]; omega) _ 0 (by simp)]

/-- `cells_eq` with the sizes as `UInt32`. -/
theorem cells_eqU (X W : ByteArray) (K c0s m lim n : UInt32) (B : Bnd K c0s m lim n)
    (pa pb : UInt32) (H F : Array UInt32) (tb : ByteArray) :
    bandCellsJ X W K c0s m lim n (n.toNat * (K.toNat + 1)) 1 (rowStart K c0s 1 pa) 16777216 16777216 pa pb K 0 H F tb =
      bandCells X W K c0s m lim (n.toNat * (K.toNat + 1)) 1 0 16777216 16777216 pa pb K 0 H F tb := by
  have h := cells_eq X W K.toNat n.toNat c0s m lim B.hK B.hn B.hc B.hm B.hl 16777216 16777216 pa pb K 0 H F tb rfl rfl
  have eK : K.toNat.toUInt32 = K := UInt32.toNat_inj.mp (toU32_toNat _ (by have := B.hK; omega))
  have en : n.toNat.toUInt32 = n := UInt32.toNat_inj.mp (toU32_toNat _ (by have := B.hn; omega))
  rw [eK, en] at h
  exact h

/-- **`bandCellsJ` is `bandCells`** inside `bandDPg`: for all arguments. -/
theorem bandCellsG_jump : bandCellsG true = bandCellsG false := by
  funext X W K c0s m lim n fuel pa pb H F tb
  unfold bandCellsG
  simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hK, hc⟩, hn⟩, hm⟩, hl⟩, hf⟩ := h
    subst hf
    exact cells_eqU X W K c0s m lim n ⟨hK, hc, hn, hm, hl⟩ pa pb H F tb
  · rfl

/-- **`bandDPg true = bandDPg false`**: jumping over the skipped cells changes nothing (start, length,
penalty, runs), for every read, window, band and limit. -/
theorem bandDPg_jump : bandDPg true = bandDPg false := by
  funext X W s0 w lim
  unfold bandDPg
  rw [bandCellsG_jump]

#print axioms bandDPg_jump
#print axioms bandCellsJ_eq

end TierHeur
