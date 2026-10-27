import AlignmentWfaCertified
import ProbeU32

/-!
# UInt32 arithmetic foundations for padded wavefronts

Proof work towards the speed probe alignment/probes/ProbeU32.lean:

* fronts are `Array UInt32` codes (`0` = no cell, `k + 1` = offset `k`,
  the `RFront` code), padded with `margin` zero cells on both sides so
  that a read from a source level needs no band test;
* the three fronts of a level are built by one recursion over the band
  (`uFillGo`), all per-cell arithmetic in UInt32.

The arithmetic lemmas below connect UInt32 operations to their `Nat`
counterparts below `2^30`. Padded-array denotation, the complete level loop,
and optimality are still outstanding. This is not a certified aligner yet.

Algorithm reference: Marco-Sola et al. 2021 (WFA); WFA2-lib's offsets
(github.com/smarco/WFA2-lib).
-/
namespace AlignmentSpec.U32Proof

-- ══════════════════════════════════════════════════════════════════
-- Data and UInt32 cell arithmetic
-- ══════════════════════════════════════════════════════════════════

/-- One level: fronts sharing a band; diagonal `t` lives at index
`t + margin - lo`; `w = 0` means the level is empty. -/
structure ULevel where
  lo : Nat
  w  : Nat
  mf : Array UInt32
  xf : Array UInt32
  yf : Array UInt32
deriving Inhabited

def uEmpty : ULevel := ⟨0, 0, #[], #[], #[]⟩

/-- Saturating subtraction: the UInt32 image of `Nat` subtraction. -/
@[inline] def usub (a b : UInt32) : UInt32 := if a < b then 0 else a - b

/-- Left-biased max on codes (`betterR`). -/
@[inline] def ubetter (a b : UInt32) : UInt32 := if b ≤ a then a else b

/-- `joffOf` on UInt32. -/
@[inline] def ujoff (m t off : UInt32) : UInt32 := usub (off + t) m

@[inline] def upushX (m n t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := ujoff m t off
    if j < n then a else if 1 ≤ off ∧ 1 ≤ j then off else 0

@[inline] def upushY (m t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    if off < m then a + 1 else if 1 ≤ off ∧ 1 ≤ ujoff m t off then a else 0

@[inline] def upushD (m n t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    let j := ujoff m t off
    if off < m ∧ j < n then a + 1 else if 1 ≤ off ∧ 1 ≤ j then a else 0

/-- Free extension on codes: `extR` with the LCP loop of the proven kernel. -/
@[inline] def uext (m : UInt32) (xa ya : Array Char) (t a : UInt32) : UInt32 :=
  if a = 0 then 0 else
    let off := a - 1
    off + (lcpArr xa ya off.toNat (ujoff m t off).toNat).toUInt32 + 1

-- ── UInt32 ↔ Nat ──

theorem UInt32.toNat_add_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

theorem usub_toNat (a b : UInt32) : (usub a b).toNat = a.toNat - b.toNat := by
  unfold usub
  by_cases h : a < b
  · rw [if_pos h]
    change 0 = a.toNat - b.toNat
    have hn := UInt32.lt_iff_toNat_lt.mp h
    omega
  · rw [if_neg h]
    have hn : ¬a.toNat < b.toNat := h
    exact UInt32.toNat_sub_of_le a b (UInt32.le_iff_toNat_le.mpr (by omega))

theorem ubetter_toNat (a b : UInt32) : (ubetter a b).toNat = betterR a.toNat b.toNat := by
  unfold ubetter betterR
  by_cases h : b ≤ a
  · rw [if_pos h, if_pos (UInt32.le_iff_toNat_le.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (UInt32.le_iff_toNat_le.mpr h'))]

theorem ujoff_toNat (m t off : UInt32) (h : off.toNat + t.toNat < 2 ^ 32) :
    (ujoff m t off).toNat = joffOf m.toNat t.toNat off.toNat := by
  unfold ujoff joffOf
  rw [usub_toNat, UInt32.toNat_add_of_lt _ _ h]

theorem UInt32.toNat_eq_zero_iff (a : UInt32) : a = 0 ↔ a.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UInt32.toNat_inj.mp (by rw [h]; rfl)

theorem UInt32.toNat_pred (a : UInt32) (h : a ≠ 0) : (a - 1).toNat = a.toNat - 1 := by
  have hn : a.toNat ≠ 0 := fun he => h ((UInt32.toNat_eq_zero_iff a).mpr he)
  have hle : (1 : UInt32) ≤ a := by change 1 ≤ a.toNat; omega
  simpa using UInt32.toNat_sub_of_le a 1 hle

theorem UInt32.toNat_succ (a : UInt32) (h : a.toNat + 1 < 2 ^ 32) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add_of_lt _ _ (by rw [UInt32.toNat_one]; exact h), UInt32.toNat_one]

/-- Bounds under which the UInt32 arithmetic never wraps. -/
def UBound (m n t a : UInt32) : Prop :=
  m.toNat < 2 ^ 30 ∧ n.toNat < 2 ^ 30 ∧ t.toNat < 2 ^ 30 ∧ a.toNat < 2 ^ 30

theorem upushX_toNat (m n t a : UInt32) (hb : UBound m n t a) :
    (upushX m n t a).toNat = pushXR m.toNat n.toNat t.toNat a.toNat := by
  obtain ⟨hm, hn, ht, ha⟩ := hb
  unfold upushX pushXR
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos ((UInt32.toNat_eq_zero_iff a).mp h0)]; rfl
  · rw [if_neg h0, if_neg (fun h => h0 ((UInt32.toNat_eq_zero_iff a).mpr h))]
    have hoff := UInt32.toNat_pred a h0
    have hj := ujoff_toNat m t (a - 1) (by omega)
    rw [hoff] at hj
    simp only [hj, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_one, hoff]
    split <;> simp_all
    split <;> simp_all

theorem upushY_toNat (m n t a : UInt32) (hb : UBound m n t a) :
    (upushY m t a).toNat = pushYR m.toNat n.toNat t.toNat a.toNat := by
  obtain ⟨hm, hn, ht, ha⟩ := hb
  unfold upushY pushYR
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos ((UInt32.toNat_eq_zero_iff a).mp h0)]; rfl
  · rw [if_neg h0, if_neg (fun h => h0 ((UInt32.toNat_eq_zero_iff a).mpr h))]
    have hoff := UInt32.toNat_pred a h0
    have hj := ujoff_toNat m t (a - 1) (by omega)
    rw [hoff] at hj
    have hs := UInt32.toNat_succ a (by omega)
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_one, hoff, hj]
    split <;> simp_all
    split <;> simp_all

theorem upushD_toNat (m n t a : UInt32) (hb : UBound m n t a) :
    (upushD m n t a).toNat = pushDR m.toNat n.toNat t.toNat a.toNat := by
  obtain ⟨hm, hn, ht, ha⟩ := hb
  unfold upushD pushDR
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos ((UInt32.toNat_eq_zero_iff a).mp h0)]; rfl
  · rw [if_neg h0, if_neg (fun h => h0 ((UInt32.toNat_eq_zero_iff a).mpr h))]
    have hoff := UInt32.toNat_pred a h0
    have hj := ujoff_toNat m t (a - 1) (by omega)
    rw [hoff] at hj
    have hs := UInt32.toNat_succ a (by omega)
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_one, hoff, hj]
    split <;> simp_all
    split <;> simp_all

theorem lcpArrGo_le_fuel (xa ya : Array Char) (fuel i j acc : Nat) :
    lcpArrGo xa ya fuel i j acc ≤ acc + fuel := by
  induction fuel generalizing i j acc with
  | zero => simp [lcpArrGo]
  | succ fuel ih =>
    simp only [lcpArrGo]
    split
    · split
      · have h := ih (i + 1) (j + 1) (acc + 1); omega
      · omega
    · omega

theorem lcpArr_le (xa ya : Array Char) (i j : Nat) : lcpArr xa ya i j ≤ xa.size := by
  have h := lcpArrGo_le_fuel xa ya (xa.size - i) i j 0
  unfold lcpArr
  omega

theorem uext_toNat (m n t a : UInt32) (xa ya : Array Char) (hb : UBound m n t a)
    (hx : xa.size < 2 ^ 30) :
    (uext m xa ya t a).toNat = extR m.toNat xa ya t.toNat a.toNat := by
  obtain ⟨hm, hn, ht, ha⟩ := hb
  unfold uext extR
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos ((UInt32.toNat_eq_zero_iff a).mp h0)]; rfl
  · rw [if_neg h0, if_neg (fun h => h0 ((UInt32.toNat_eq_zero_iff a).mpr h))]
    have hoff := UInt32.toNat_pred a h0
    have hj := ujoff_toNat m t (a - 1) (by omega)
    rw [hoff] at hj
    have hl : lcpArr xa ya (a.toNat - 1) (joffOf m.toNat t.toNat (a.toNat - 1)) ≤ xa.size :=
      lcpArr_le xa ya _ _
    simp only [hoff, hj]
    let count := lcpArr xa ya (a.toNat - 1) (joffOf m.toNat t.toNat (a.toNat - 1))
    have hc : count.toUInt32.toNat = count :=
      UInt32.toNat_ofNat_of_lt' (by change count < 4294967296; dsimp [count]; omega)
    have hs : ((a - 1) + count.toUInt32).toNat = a.toNat - 1 + count := by
      rw [UInt32.toNat_add_of_lt _ _ (by rw [hoff, hc]; dsimp [count]; omega), hoff, hc]
    change (((a - 1) + count.toUInt32) + 1).toNat = a.toNat - 1 + count + 1
    rw [UInt32.toNat_succ _ (by rw [hs]; dsimp [count]; omega), hs]

/-- On a valid diagonal, subtraction in the actual probe cannot underflow. -/
theorem ujoff_eq_raw (m t off : UInt32)
    (hsum : off.toNat + t.toNat < 2 ^ 32)
    (hgeom : m.toNat ≤ off.toNat + t.toNat) :
    ujoff m t off = off + t - m := by
  unfold ujoff usub
  have hs := UInt32.toNat_add_of_lt off t hsum
  have hn : ¬off + t < m := by
    rw [UInt32.lt_iff_toNat_lt, hs]
    omega
  rw [if_neg hn]

/-- Bridge to the actual benchmarked probe, not just the saturating model. -/
theorem probe_pushX_eq (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    AlignmentSpec.upushX m n t a = upushX m n t a := by
  by_cases h0 : a = 0
  · simp [AlignmentSpec.upushX, upushX, h0]
  · have hp := UInt32.toNat_pred a h0
    obtain ⟨hm, hn, ht, ha⟩ := hb
    have hj := ujoff_eq_raw m t (a - 1) (by rw [hp]; omega) (by rw [hp]; exact hgeom h0)
    simp [AlignmentSpec.upushX, upushX, h0, hj]

theorem probe_pushY_eq (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    AlignmentSpec.upushY m t a = upushY m t a := by
  by_cases h0 : a = 0
  · simp [AlignmentSpec.upushY, upushY, h0]
  · have hp := UInt32.toNat_pred a h0
    obtain ⟨hm, hn, ht, ha⟩ := hb
    have hj := ujoff_eq_raw m t (a - 1) (by rw [hp]; omega) (by rw [hp]; exact hgeom h0)
    simp [AlignmentSpec.upushY, upushY, h0, hj]

theorem probe_pushD_eq (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    AlignmentSpec.upushD m n t a = upushD m n t a := by
  by_cases h0 : a = 0
  · simp [AlignmentSpec.upushD, upushD, h0]
  · have hp := UInt32.toNat_pred a h0
    obtain ⟨hm, hn, ht, ha⟩ := hb
    have hj := ujoff_eq_raw m t (a - 1) (by rw [hp]; omega) (by rw [hp]; exact hgeom h0)
    simp [AlignmentSpec.upushD, upushD, h0, hj]

theorem probe_pushX_toNat (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    (AlignmentSpec.upushX m n t a).toNat = pushXR m.toNat n.toNat t.toNat a.toNat := by
  rw [probe_pushX_eq m n t a hb hgeom, upushX_toNat m n t a hb]

theorem probe_pushY_toNat (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    (AlignmentSpec.upushY m t a).toNat = pushYR m.toNat n.toNat t.toNat a.toNat := by
  rw [probe_pushY_eq m n t a hb hgeom, upushY_toNat m n t a hb]

theorem probe_pushD_toNat (m n t a : UInt32) (hb : UBound m n t a)
    (hgeom : a ≠ 0 → m.toNat ≤ a.toNat - 1 + t.toNat) :
    (AlignmentSpec.upushD m n t a).toNat = pushDR m.toNat n.toNat t.toNat a.toNat := by
  rw [probe_pushD_eq m n t a hb hgeom, upushD_toNat m n t a hb]

/-- A nonzero code names a cell inside the alignment rectangle.
Writing this in terms of the code avoids truncated subtraction in invariants. -/
def ValidCode (m n t a : Nat) : Prop :=
  a = 0 ∨ (1 ≤ a ∧ a ≤ m + 1 ∧ m + 1 ≤ a + t ∧ a + t ≤ m + n + 1)

theorem betterR_valid (m n t a b : Nat)
    (ha : ValidCode m n t a) (hb : ValidCode m n t b) :
    ValidCode m n t (betterR a b) := by
  unfold betterR
  split <;> assumption

theorem pushXR_valid (m n t a : Nat) (h : ValidCode m n t a) :
    ValidCode m n (t + 1) (pushXR m n t a) := by
  unfold ValidCode at *
  rcases h with h0 | h
  · subst a; simp [pushXR]
  · have hn : a ≠ 0 := by omega
    unfold pushXR
    rw [if_neg hn]
    dsimp only [joffOf]
    by_cases h1 : a - 1 + t - m < n <;> by_cases h2 : 1 ≤ a - 1 ∧ 1 ≤ a - 1 + t - m <;>
      simp [h1, h2] <;> omega

theorem pushYR_valid (m n t a : Nat) (h : ValidCode m n (t + 1) a) :
    ValidCode m n t (pushYR m n (t + 1) a) := by
  unfold ValidCode at *
  rcases h with h0 | h
  · subst a; simp [pushYR]
  · have hn : a ≠ 0 := by omega
    unfold pushYR
    rw [if_neg hn]
    dsimp only [joffOf]
    by_cases h1 : a - 1 < m <;> by_cases h2 : 1 ≤ a - 1 ∧ 1 ≤ a - 1 + (t + 1) - m <;>
      simp [h1, h2] <;> omega

theorem pushDR_valid (m n t a : Nat) (h : ValidCode m n t a) :
    ValidCode m n t (pushDR m n t a) := by
  unfold ValidCode at *
  rcases h with h0 | h
  · subst a; simp [pushDR]
  · have hn : a ≠ 0 := by omega
    unfold pushDR
    rw [if_neg hn]
    dsimp only [joffOf]
    by_cases h1 : a - 1 < m ∧ a - 1 + t - m < n <;> by_cases h2 : 1 ≤ a - 1 ∧ 1 ≤ a - 1 + t - m <;>
      simp [h1, h2] <;> omega

end AlignmentSpec.U32Proof
#print axioms AlignmentSpec.U32Proof.upushX_toNat
#print axioms AlignmentSpec.U32Proof.upushY_toNat
#print axioms AlignmentSpec.U32Proof.upushD_toNat
#print axioms AlignmentSpec.U32Proof.uext_toNat
#print axioms AlignmentSpec.U32Proof.probe_pushX_toNat
#print axioms AlignmentSpec.U32Proof.probe_pushY_toNat
#print axioms AlignmentSpec.U32Proof.probe_pushD_toNat
#print axioms AlignmentSpec.U32Proof.pushXR_valid
#print axioms AlignmentSpec.U32Proof.pushYR_valid
#print axioms AlignmentSpec.U32Proof.pushDR_valid
