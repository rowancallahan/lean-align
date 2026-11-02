import Proofs.SaveLoad

/-! # The loaded minimizer index passes the checker when the built one does

The loader reads the bucket offsets and the slots in place in the saved bytes `S`: offset `b` at
`UInt32` `ob + b`, each plus `m`, and slot `t` of `ix.sl` as slot `t + m` of `S` (`Shifted`).
`check2_sh`: then `check2 ix U = true → check2 (ixL ix S ob) U = true` (the per-bucket pass gives
the same answers; the completeness pass's fill hints stay `m` apart). -/
open MapSpec MapSpec.Mz

namespace Spec.Shift
open Spec.Pack Spec.SaveLoad

theorem getU32_out (B : ByteArray) (i : Nat) (h : B.size ≤ 4 * i) : getU32 B i = 0 := by
  unfold getU32; dsimp only
  rw [Fast.get!_out B _ (by omega), Fast.get!_out B _ (by omega), Fast.get!_out B _ (by omega), Fast.get!_out B _ (by omega)]; rfl

theorem getU32_eq (B : ByteArray) (i : Nat) : getU32 B i =
    (B.get! (4 * i)).toNat + 256 * (B.get! (4 * i + 1)).toNat + 65536 * (B.get! (4 * i + 2)).toNat +
      16777216 * (B.get! (4 * i + 3)).toNat := by
  unfold getU32; dsimp only; exact rd32 _ _ _ _

theorem setU32_size (B : ByteArray) (i v : Nat) : (setU32 B i v).size = B.size := by
  simp [setU32, size_set]

theorem getU32_setU32 (B : ByteArray) (i v j : Nat) (hB : B.size % 4 = 0) :
    getU32 (setU32 B i v) j = if j = i ∧ 4 * i + 3 < B.size then v % 2 ^ 32 else getU32 B j := by
  have gs : ∀ p, (setU32 B i v).get! p = if p = 4 * i ∧ 4 * i < B.size then v.toUInt32.toUInt8
      else if p = 4 * i + 1 ∧ 4 * i + 1 < B.size then (v.toUInt32 >>> 8).toUInt8
      else if p = 4 * i + 2 ∧ 4 * i + 2 < B.size then (v.toUInt32 >>> 16).toUInt8
      else if p = 4 * i + 3 ∧ 4 * i + 3 < B.size then (v.toUInt32 >>> 24).toUInt8 else B.get! p := by
    intro p
    simp only [setU32, get_set, size_set]
    by_cases a3 : p = 4 * i + 3 ∧ 4 * i + 3 < B.size
    · rw [if_pos a3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos a3]
    · rw [if_neg a3]
      by_cases a2 : p = 4 * i + 2 ∧ 4 * i + 2 < B.size
      · rw [if_pos a2, if_neg (by omega), if_neg (by omega), if_pos a2]
      · rw [if_neg a2]
        by_cases a1 : p = 4 * i + 1 ∧ 4 * i + 1 < B.size
        · rw [if_pos a1, if_neg (by omega), if_pos a1]
        · rw [if_neg a1]
          by_cases a0 : p = 4 * i ∧ 4 * i < B.size
          · rw [if_pos a0, if_pos a0]
          · rw [if_neg a0, if_neg a0, if_neg a1, if_neg a2, if_neg a3]
  rw [getU32_eq, getU32_eq, gs, gs, gs, gs]
  by_cases e : j = i ∧ 4 * i + 3 < B.size
  · obtain ⟨rfl, h⟩ := e
    simp only [true_and, show 4 * j < B.size by omega, show 4 * j + 1 < B.size by omega,
      show 4 * j + 2 < B.size by omega, h, and_self, ite_true, show ¬ 4 * j + 1 = 4 * j by omega,
      show ¬ 4 * j + 2 = 4 * j by omega, show ¬ 4 * j + 3 = 4 * j by omega, show ¬ 4 * j + 2 = 4 * j + 1 by omega,
      show ¬ 4 * j + 3 = 4 * j + 1 by omega, show ¬ 4 * j + 3 = 4 * j + 2 by omega, false_and, ite_false, and_true]
    have e1 := byte32 v.toUInt32 8 (by omega); have e2 := byte32 v.toUInt32 16 (by omega)
    have e3 := byte32 v.toUInt32 24 (by omega)
    simp only [show (8 : Nat).toUInt32 = 8 from rfl, show (16 : Nat).toUInt32 = 16 from rfl,
      show (24 : Nat).toUInt32 = 24 from rfl] at e1 e2 e3
    rw [e1, e2, e3, UInt32.toNat_toUInt8, show v.toUInt32.toNat = v % 2 ^ 32 by simp [Nat.toUInt32, UInt32.toNat_ofNat']]
    have : v % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by omega)
    generalize v % 2 ^ 32 = y at this ⊢
    simp only [show (2 : Nat) ^ 8 = 256 from rfl, show (2 : Nat) ^ 16 = 65536 from rfl,
      show (2 : Nat) ^ 24 = 16777216 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
    omega
  · rw [if_neg e]
    by_cases hj : j = i
    · subst hj
      have : B.size ≤ 4 * j := by omega
      simp only [show ¬ 4 * j < B.size by omega, show ¬ 4 * j + 1 < B.size by omega,
        show ¬ 4 * j + 2 < B.size by omega, show ¬ 4 * j + 3 < B.size by omega, and_false, ite_false]
    · simp only [show ¬ 4 * j = 4 * i by omega, show ¬ 4 * j + 1 = 4 * i by omega, show ¬ 4 * j + 2 = 4 * i by omega,
        show ¬ 4 * j + 3 = 4 * i by omega, show ¬ 4 * j = 4 * i + 1 by omega, show ¬ 4 * j + 1 = 4 * i + 1 by omega,
        show ¬ 4 * j + 2 = 4 * i + 1 by omega, show ¬ 4 * j + 3 = 4 * i + 1 by omega,
        show ¬ 4 * j = 4 * i + 2 by omega, show ¬ 4 * j + 1 = 4 * i + 2 by omega,
        show ¬ 4 * j + 2 = 4 * i + 2 by omega, show ¬ 4 * j + 3 = 4 * i + 2 by omega,
        show ¬ 4 * j = 4 * i + 3 by omega, show ¬ 4 * j + 1 = 4 * i + 3 by omega,
        show ¬ 4 * j + 2 = 4 * i + 3 by omega, show ¬ 4 * j + 3 = 4 * i + 3 by omega, false_and, ite_false]


theorem get_extract (B : ByteArray) (a e i : Nat) (he : e ≤ B.size) (hi : a + i < e) :
    (B.extract a e).get! i = B.get! (a + i) := by
  have hs : (B.extract a e).size = min e B.size - a := ByteArray.size_extract
  rw [bget, bget, getElem!_pos (B.extract a e).data i (show i < (B.extract a e).size by omega),
    getElem!_pos B.data (a + i) (show a + i < B.size by omega)]
  have := ByteArray.getElem_extract (b := B) (start := a) (stop := e) (i := i) (h := by omega)
  simp only [ByteArray.getElem_eq_getElem_data] at this
  exact this

theorem getU32_extract (B : ByteArray) (a e b : Nat) (he : e ≤ B.size) (hb : 4 * a + 4 * b + 3 < e) :
    getU32 (B.extract (4 * a) e) b = getU32 B (a + b) := by
  rw [getU32_eq, getU32_eq, get_extract _ _ _ _ he (by omega), get_extract _ _ _ _ he (by omega),
    get_extract _ _ _ _ he (by omega), get_extract _ _ _ _ he (by omega)]
  simp only [show 4 * a + 4 * b = 4 * (a + b) by omega, show 4 * a + (4 * b + 1) = 4 * (a + b) + 1 by omega,
    show 4 * a + (4 * b + 2) = 4 * (a + b) + 2 by omega, show 4 * a + (4 * b + 3) = 4 * (a + b) + 3 by omega]

/-- The loaded index: the built one with `offs`, `sl` read from `S` and the offsets from `ob`. -/
def ixL (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx := { ix with offs := S, ob := ob, sl := S }

@[simp] theorem ixL_k (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).k = ix.k := rfl
@[simp] theorem ixL_B (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).B = ix.B := rfl
@[simp] theorem ixL_w (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).w = ix.w := rfl
@[simp] theorem ixL_c (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).c = ix.c := rfl
@[simp] theorem ixL_kb (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).kb = ix.kb := rfl
@[simp] theorem ixL_kf (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).kf = ix.kf := rfl
@[simp] theorem ixL_T (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).T = ix.T := rfl
@[simp] theorem ixL_kmU (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).kmU = ix.kmU := rfl
@[simp] theorem ixL_t (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).t = ix.t := rfl
@[simp] theorem ixL_tmU (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).tmU = ix.tmU := rfl
@[simp] theorem ixL_kbM (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).kbM = ix.kbM := rfl
@[simp] theorem ixL_fM (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).fM = ix.fM := rfl
@[simp] theorem ixL_tM (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).tM = ix.tM := rfl
@[simp] theorem ixL_pm (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).pm = ix.pm := rfl
@[simp] theorem ixL_bsh (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).bsh = ix.bsh := rfl
@[simp] theorem ixL_ash (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).ash = ix.ash := rfl
@[simp] theorem ixL_fsh (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).fsh = ix.fsh := rfl
@[simp] theorem ixL_sw (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).sw = ix.sw := rfl
@[simp] theorem ixL_runs (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).runs = ix.runs := rfl
@[simp] theorem ixL_offs (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).offs = S := rfl
@[simp] theorem ixL_ob (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).ob = ob := rfl
@[simp] theorem ixL_sl (ix : MzIdx) (S : ByteArray) (ob : Nat) : (ixL ix S ob).sl = S := rfl

theorem ixL_eq (ix : MzIdx) (S : ByteArray) (ob : Nat) : ixL ix S ob = { ix with offs := S, ob := ob, sl := S } := rfl

@[simp] theorem ixL_mini (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.mini (ixL ix S ob) = MzIdx.mini ix := by
  rfl
@[simp] theorem ixL_hsh (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.hsh (ixL ix S ob) = MzIdx.hsh ix := by
  funext v; simp only [MzIdx.hsh, ixL_kmU]
@[simp] theorem ixL_sub (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.sub (ixL ix S ob) = MzIdx.sub ix := by
  funext v o; simp only [MzIdx.sub, ixL_k, ixL_kmU]
@[simp] theorem ixL_posOf (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.posOf (ixL ix S ob) = MzIdx.posOf ix := by
  funext v; simp only [MzIdx.posOf, ixL_T]
@[simp] theorem ixL_tagOf (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.tagOf (ixL ix S ob) = MzIdx.tagOf ix := by
  funext v; simp only [MzIdx.tagOf, ixL_tM]
@[simp] theorem ixL_keyF (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.keyF (ixL ix S ob) = MzIdx.keyF ix := by
  funext v; simp only [MzIdx.keyF, ixL_kbM]
@[simp] theorem ixL_befF (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.befF (ixL ix S ob) = MzIdx.befF ix := by
  funext v; simp only [MzIdx.befF, ixL_bsh, ixL_fM]
@[simp] theorem ixL_aftF (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.aftF (ixL ix S ob) = MzIdx.aftF ix := by
  funext v; simp only [MzIdx.aftF, ixL_ash, ixL_fM]
@[simp] theorem ixL_flagF (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.flagF (ixL ix S ob) = MzIdx.flagF ix := by
  funext v; simp only [MzIdx.flagF, ixL_fsh]
@[simp] theorem ixL_nr (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.nr (ixL ix S ob) = MzIdx.nr ix := by
  simp only [MzIdx.nr, ixL_runs]
@[simp] theorem ixL_ra (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.ra (ixL ix S ob) = MzIdx.ra ix := by
  funext i; simp only [MzIdx.ra, ixL_runs]
@[simp] theorem ixL_rb (ix : MzIdx) (S : ByteArray) (ob : Nat) : MzIdx.rb (ixL ix S ob) = MzIdx.rb ix := by
  funext i; simp only [MzIdx.rb, ixL_runs]
@[simp] theorem ixL_checkParams (ix : MzIdx) (S : ByteArray) (ob : Nat) : checkParams (ixL ix S ob) = checkParams ix := by
  rfl

/-- The loaded index is the built one with the offsets read from `S` at `ob` (each plus `m`) and
the slots read from `S` from slot `m`. -/
structure Shifted (ix : MzIdx) (S : ByteArray) (ob m T : Nat) : Prop where
  sz : ix.offs.size = 4 * (2 ^ ix.B + 1)
  ob0 : ix.ob = 0
  off : ∀ b, b ≤ 2 ^ ix.B → getU32 S (ob + b) = getU32 ix.offs b + m
  le : ∀ b, b ≤ 2 ^ ix.B → getU32 ix.offs b ≤ T
  fit : T + m < 2 ^ 32
  slot : ∀ t, t < T → rdSlot S ix.sw (t + m) = rdSlot ix.sl ix.sw t
  hint : 4 * (ob + 2 ^ ix.B + 1) ≤ S.size

def FillRel (ix : MzIdx) (m T : Nat) (fill fill' : ByteArray) : Prop :=
  fill.size = 4 * (2 ^ ix.B + 1) ∧ fill'.size = 4 * (2 ^ ix.B + 1) ∧
  ∀ b, b ≤ 2 ^ ix.B → getU32 fill' b = getU32 fill b + m ∧ getU32 fill b ≤ T

section
variable {ix : MzIdx} {S : ByteArray} {ob m T : Nat} (H : Shifted ix S ob m T)
include H

theorem loB_sh (b : Nat) (hb : b ≤ 2 ^ ix.B) :
    MzIdx.loB (ixL ix S ob) b = ix.loB b + m := by
  simp only [MzIdx.loB, H.ob0, Nat.zero_add]; exact H.off b hb

theorem hiB_sh (b : Nat) (hb : b + 1 ≤ 2 ^ ix.B) :
    MzIdx.hiB (ixL ix S ob) b = ix.hiB b + m := by
  simp only [MzIdx.hiB, H.ob0, Nat.zero_add]; rw [Nat.add_assoc]; exact H.off (b + 1) hb

theorem slot_sh (t : Nat) (ht : t < T) :
    MzIdx.slot (ixL ix S ob) (t + m) = ix.slot t := by
  simp only [MzIdx.slot]; exact H.slot t ht

theorem hiB_pos (b : Nat) (h : 0 < ix.hiB b) : b + 1 ≤ 2 ^ ix.B := by
  simp only [MzIdx.hiB, H.ob0, Nat.zero_add] at h
  by_cases hc : b + 1 ≤ 2 ^ ix.B
  · exact hc
  · rw [getU32_out _ _ (by rw [H.sz]; omega)] at h; omega

theorem hiB_le (b : Nat) (hb : b + 1 ≤ 2 ^ ix.B) : ix.hiB b ≤ T := by
  simp only [MzIdx.hiB, H.ob0, Nat.zero_add]; exact H.le (b + 1) hb

theorem hint_rel : FillRel ix m T ix.hint (MzIdx.hint (ixL ix S ob)) := by
  have hs : ix.offs.extract 0 (4 * (2 ^ ix.B + 1)) = ix.offs := by
    rw [← H.sz]; exact ByteArray.extract_zero_size
  refine ⟨?_, ?_, fun b hb => ?_⟩
  · simp only [MzIdx.hint, H.ob0, Nat.mul_zero, Nat.zero_add, hs, H.sz]
  · simp only [MzIdx.hint, ByteArray.size_extract, ixL_offs, ixL_ob, ixL_B]; have := H.hint; omega
  · simp only [MzIdx.hint, H.ob0, Nat.mul_zero, Nat.zero_add, hs, ixL_offs, ixL_ob, ixL_B]
    rw [getU32_extract _ _ _ _ H.hint (by omega)]
    exact ⟨H.off b hb, H.le b hb⟩


theorem compR_sh (U : ByteArray) : ∀ n fill fill' last p x g, FillRel ix m T fill fill' →
    compR ix U fill last n p x g = true → compR (ixL ix S ob) U fill' last n p x g = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ n ih =>
    intro fill fill' last p x g R h
    simp only [compR, ixL_mini, ixL_hsh, ixL_sub, ixL_kb, ixL_posOf] at h ⊢
    split at h
    · rename_i hq
      rw [if_pos hq]
      split at h
      · rename_i hl; rw [if_pos hl]; exact ih _ _ _ _ _ _ R h
      · rename_i hl
        rw [if_neg hl]
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        have hb := hiB_pos H _ (Nat.lt_of_le_of_lt (Nat.zero_le _) h2)
        have hhi := hiB_le H _ hb
        obtain ⟨hf1, hf2, hf3⟩ := R
        have hfb := hf3 _ (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hb))
        rw [hfb.1, loB_sh H _ (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hb)), hiB_sh H _ hb,
          slot_sh H _ (Nat.lt_of_lt_of_le h2 hhi)]
        refine ⟨⟨⟨by omega, by omega⟩, h3⟩, ?_⟩
        refine ih _ _ _ _ _ _ ⟨by rw [setU32_size, hf1], by rw [setU32_size, hf2], fun b' hb' => ?_⟩ h4
        have m1 : fill.size % 4 = 0 := by rw [hf1]; omega
        have m2 : fill'.size % 4 = 0 := by rw [hf2]; omega
        rw [getU32_setU32 _ _ _ _ m1, getU32_setU32 _ _ _ _ m2]
        split
        · rename_i e
          obtain ⟨rfl, -⟩ := e
          rw [if_pos ⟨rfl, by rw [hf1]; omega⟩]
          rw [Nat.mod_eq_of_lt (by have := H.fit; omega), Nat.mod_eq_of_lt (by have := H.fit; omega)]
          omega
        · rename_i e
          rw [if_neg (fun h => e ⟨h.1, by rw [hf2]; rw [hf1] at h; exact h.2⟩)]; exact hf3 b' hb'
    · rename_i hq
      rw [if_neg hq]
      exact ih _ _ _ _ _ _ R h

theorem entryOk_sh (U : ByteArray) (b hi t : Nat) (ht : t < hi) (hT : hi ≤ T) :
    entryOk (ixL ix S ob) U b (hi + m) (t + m) = entryOk ix U b hi t := by
  simp only [entryOk, ixL_posOf, ixL_tagOf, ixL_k, ixL_hsh, ixL_c, ixL_kb, ixL_keyF, ixL_kbM, ixL_flagF, ixL_befF,
    ixL_aftF]
  rw [slot_sh H t (by omega)]
  by_cases e : hi ≤ t + 1
  · simp only [show hi + m ≤ t + m + 1 by omega, e, decide_true, Bool.or_true, Bool.true_or]
  · rw [show t + m + 1 = (t + 1) + m by omega, slot_sh H (t + 1) (by omega)]
    simp only [show ¬ hi + m ≤ t + 1 + m by omega, e, decide_false, Bool.false_or]

theorem checkBucket_sh (U : ByteArray) (b hi : Nat) (hT : hi ≤ T) : ∀ n t, t + n ≤ hi →
    checkBucket (ixL ix S ob) U b (hi + m) n (t + m) = checkBucket ix U b hi n t := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro t ht
    simp only [checkBucket]
    rw [entryOk_sh H U b hi t (by omega) hT, show t + m + 1 = (t + 1) + m by omega, ih (t + 1) (by omega)]

theorem checkSound_sh (U : ByteArray) : ∀ n b, b + n ≤ 2 ^ ix.B →
    checkSound (ixL ix S ob) U n b = checkSound ix U n b := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro b hb
    simp only [checkSound]
    rw [loB_sh H b (by omega), hiB_sh H b (by omega), ih (b + 1) (by omega),
      show ix.hiB b + m - (ix.loB b + m) = ix.hiB b - ix.loB b by omega]
    have hT : ix.hiB b ≤ T := by simpa [MzIdx.hiB, H.ob0] using H.le (b + 1) (by omega)
    by_cases hl : ix.loB b ≤ ix.hiB b
    · rw [checkBucket_sh H U b _ hT _ _ (by omega)]
    · rw [show ix.hiB b - ix.loB b = 0 by omega]; rfl

omit H in
theorem checkRuns_sh (U : ByteArray) : ∀ n i,
    checkRuns (ixL ix S ob) U n i = checkRuns ix U n i := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih => intro i; simp only [checkRuns, ih]; rfl

omit H in
theorem advance_sh (x : Nat) : ∀ f c, advance (ixL ix S ob) x f c = advance ix x f c := by
  intro f; induction f with
  | zero => intro _; rfl
  | succ f ih => intro c; simp only [advance, ih]; rfl

omit H in
theorem checkCover_sh (U : ByteArray) : ∀ n c x,
    checkCover (ixL ix S ob) U c n x = checkCover ix U c n x := by
  intro n; induction n with
  | zero => intro _ _; rfl
  | succ n ih => intro c x; simp only [checkCover, ih, advance_sh, ixL_nr, ixL_ra, ixL_rb]

/-- **The loaded index passes the checker** whenever the built one does. -/
theorem check2_sh (U : ByteArray) (h : check2 ix U = true) :
    check2 (ixL ix S ob) U = true := by
  unfold check2 at h ⊢
  simp only [Bool.and_eq_true, ixL_B, ixL_checkParams, ixL_nr] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [checkSound_sh H U _ 0 (by omega)]; exact h2
  · exact compR_sh H U _ _ _ _ _ _ _ (hint_rel H) h3
  · rw [checkRuns_sh]; exact h4
  · rw [checkCover_sh]; exact h5

end

end Spec.Shift

#print axioms Spec.Shift.check2_sh
