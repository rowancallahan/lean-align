import MzIndex

/-!
# A faster `Mz.check`: rolling window code in the completeness pass

`checkComp` reads every 25-letter window twice (`allA`, `wcGo`).  `compR` reads
each letter once: it keeps `g` = length (capped at 25) of the ACGT run ending at
the last letter read and `x` = the code of those `g` letters (`UInt64`), and gets
the k-word of the minimizer from `x` (`sub`).  `compR_eq`: under the invariant
`RollInv`, `compR … = checkComp …`; hence `check2 ix G = check ix G` (`check2_eq`)
and every theorem about `check` holds for `check2`.
-/

namespace MapSpec.Mz

/-- Read letter `c`: run length capped at `q`, code of the run's last `≤ q` letters. -/
@[inline] def roll (c : UInt8) (x : UInt64) (g : Nat) : UInt64 × Nat :=
  if acgt c then (((x * 4) + (byteCode c).toUInt64) &&& 0x3FFFFFFFFFFFF, min (g + 1) q) else (0, 0)

/-- The state after reading `G[0, e)`. -/
def rollTo (G : ByteArray) : (e : Nat) → UInt64 × Nat
  | 0 => (0, 0)
  | e + 1 => roll (G.get! e) (rollTo G e).1 (rollTo G e).2

/-- `checkComp` with the window code rolled: the state `(x, g)` has read `G[0, p+q-1)`. -/
def compR (ix : MzIdx) (G : ByteArray) (fill : ByteArray) (last : Nat) :
    (n p : Nat) → (x : UInt64) → (g : Nat) → Bool
  | 0, _, _, _ => true
  | n + 1, p, x, g =>
    let s := roll (G.get! (p + q - 1)) x g
    if q ≤ s.2 then
      let v := s.1.toNat
      let o := ix.mini v
      let pm := p + o
      if pm + 1 = last then compR ix G fill last n (p + 1) s.1 s.2
      else
        let b := ix.hsh (ix.sub v o) >>> ix.kb
        let t := getU32 fill b
        decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf (ix.slot t) == pm &&
          compR ix G (setU32 fill b (t + 1)) (pm + 1) n (p + 1) s.1 s.2
    else compR ix G fill last n (p + 1) s.1 s.2

/-- The runtime checker, with the rolling completeness pass. -/
def check2 (ix : MzIdx) (G : ByteArray) : Bool :=
  checkParams ix && checkSound ix G (2 ^ ix.B) 0 &&
    (let s := rollTo G (q - 1); compR ix G ix.offs 0 (G.size + 1 - q) 0 s.1 s.2) &&
    checkRuns ix G ix.nr 0 && checkCover ix G 0 G.size 0

/-! ## Proof -/

/-- `(x, g)` describes the letters before `e`. -/
def RollInv (G : ByteArray) (e : Nat) (x : UInt64) (g : Nat) : Prop :=
  g ≤ q ∧ g ≤ e ∧ (∀ i, i < g → acgt (G.get! (e - 1 - i)) = true) ∧
    (g < q → g = e ∨ acgt (G.get! (e - 1 - g)) = false) ∧ x.toNat = wc G (e - g) g

theorem rollInv_step (G : ByteArray) (e : Nat) (x : UInt64) (g : Nat) (h : RollInv G e x g) :
    RollInv G (e + 1) (roll (G.get! e) x g).1 (roll (G.get! e) x g).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold roll
  split
  · next ha =>
    dsimp only
    have hq : q = 25 := rfl
    refine ⟨Nat.min_le_right _ _, by omega, fun i hi => ?_, fun hlt => ?_, ?_⟩
    · by_cases i0 : i = 0
      · subst i0; simpa using ha
      · have := h3 (i - 1) (by omega); rwa [show e - 1 - (i - 1) = e + 1 - 1 - i by omega] at this
    · have hg : min (g + 1) q = g + 1 := by omega
      rw [hg]
      rcases h4 (by omega) with h4 | h4
      · left; omega
      · right; rwa [show e + 1 - 1 - (g + 1) = e - 1 - g by omega]
    · have hb := byteCode_lt (G.get! e)
      have hx : x.toNat < 2 ^ 50 := by
        rw [h5]; exact Nat.lt_of_lt_of_le (wc_lt G _ g) (by rw [four_pow]; exact Nat.pow_le_pow_right (by omega) (by omega))
      rw [UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_mul, show (0x3FFFFFFFFFFFF : UInt64).toNat = 2 ^ 50 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, show (4 : UInt64).toNat = 4 from rfl,
        Nat.mod_eq_of_lt (show x.toNat * 4 < 2 ^ 64 by omega),
        UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show byteCode (G.get! e) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show x.toNat * 4 + byteCode (G.get! e) < 2 ^ 64 by omega), h5]
      have hw : wc G (e - g) g * 4 + byteCode (G.get! e) = wc G (e - g) (g + 1) := by
        rw [wc, show e - g + g = e by omega]
      rw [hw]
      by_cases hgq : g < q
      · rw [show min (g + 1) q = g + 1 by omega, show e + 1 - (g + 1) = e - g by omega]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_lt_of_le (wc_lt G _ _) (by rw [four_pow]; exact Nat.pow_le_pow_right (by omega) (by omega))
      · have hg : g = q := by omega
        subst hg
        rw [show min (q + 1) q = q by omega, show (2 : Nat) ^ 50 = 4 ^ q from by rw [four_pow]; rfl,
          show q + 1 = 1 + q by omega, wc_mod, show e - q + 1 = e + 1 - q by omega]
  · next ha =>
    refine ⟨by decide, by omega, fun i hi => by omega, fun _ => ?_, rfl⟩
    right; simpa using ha

theorem rollTo_inv (G : ByteArray) : ∀ e, RollInv G e (rollTo G e).1 (rollTo G e).2 := by
  intro e
  induction e with
  | zero =>
    show RollInv G 0 (0 : UInt64) 0
    exact ⟨Nat.zero_le _, Nat.le_refl _, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ => Or.inl rfl, rfl⟩
  | succ e ih => exact rollInv_step G e _ _ ih

theorem compR_eq (ix : MzIdx) (G : ByteArray) (hg : Good ix) :
    ∀ n p fill last x g, RollInv G (p + q - 1) x g →
      compR ix G fill last n p x g = checkComp ix G fill last n p := by
  intro n
  induction n with
  | zero => intro p fill last x g _; rfl
  | succ n ih =>
    intro p fill last x g h
    have hq : q = 25 := rfl
    have h' := rollInv_step G (p + q - 1) x g h
    rw [show p + q - 1 + 1 = p + 1 + q - 1 by omega] at h'
    obtain ⟨r1, r2, r3, r4, r5⟩ := h'
    generalize hs : roll (G.get! (p + q - 1)) x g = s at r1 r2 r3 r4 r5
    -- the window `[p, p+q)` is ACGT iff the run reaches `q`
    have hall : allA G p (p + q) = true ↔ q ≤ s.2 := by
      rw [allA_iff]
      constructor
      · intro hA
        apply Classical.byContradiction; intro hlt
        rcases r4 (by omega) with r4 | r4
        · omega
        · have := hA (q - 1 - s.2) (by omega)
          rw [show p + (q - 1 - s.2) = p + 1 + q - 1 - 1 - s.2 by omega, r4] at this; cases this
      · intro hle t ht
        have := r3 (q - 1 - t) (by omega)
        rwa [show p + 1 + q - 1 - 1 - (q - 1 - t) = p + t by omega] at this
    unfold compR checkComp
    rw [hs]
    dsimp only
    by_cases hw : q ≤ s.2
    · have hs2 : s.2 = q := by omega
      have hv : s.1.toNat = wcGo G p (p + q) 0 := by
        rw [r5, hs2, wcGo_zero, show p + 1 + q - 1 - q = p by omega]
      rw [if_pos hw, if_pos (hall.2 hw), hv]
      have hsub : ix.sub (wcGo G p (p + q) 0) (ix.mini (wcGo G p (p + q) 0)) =
          wcGo G (p + ix.mini (wcGo G p (p + q) 0)) (p + ix.mini (wcGo G p (p + q) 0) + ix.k) 0 := by
        have hw' := hg.w_eq
        rw [wcGo_zero]
        have hm := mini_lt hg (wc G p q)
        rw [sub_wc hg _ _ _ (by omega), wcGo_zero]
      rw [hsub]
      split
      · exact ih _ _ _ _ _ ⟨r1, r2, r3, r4, by rw [r5]⟩
      · congr 1
        exact ih _ _ _ _ _ ⟨r1, r2, r3, r4, by rw [r5]⟩
    · rw [if_neg hw, if_neg (fun h => hw (hall.1 h))]
      exact ih _ _ _ _ _ ⟨r1, r2, r3, r4, by rw [r5]⟩

theorem check2_eq (ix : MzIdx) (G : ByteArray) : check2 ix G = check ix G := by
  unfold check2 check
  by_cases hp : checkParams ix = true
  · have hg := good_of_checkParams ix hp
    dsimp only
    rw [compR_eq ix G hg _ 0 _ _ _ _ (by
      have := rollTo_inv G (q - 1); rwa [show 0 + q - 1 = q - 1 from rfl])]
  · simp [hp]

end MapSpec.Mz

#print axioms MapSpec.Mz.check2_eq
