import PairGuarQ

/-!
# `pairGQ`, part (b): the word reject keeps the partner scan

* `rejW_ker`: at a start `rejW` rejects, the kernel answers `lim + 1` (`lim ≤ 15`): the first
  32 letters already hold more than `lim / 4` mismatches (`fcnt`), so the whole window does.
* `pscanQ_eq`: hence `pscanQ` lists what `partnerK` lists.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-- A rejected start: more than `lim / 4` mismatches in the first 32 letters (bytes `Mz.unpack P`). -/
theorem rejW_cnt (R : ByteArray) (P : PGen) (st lim : Nat) (h : rejW R (packRP R) P st lim = true) :
    32 ≤ R.size ∧ lim / 4 < cntP (fun x => R.get! x != (Mz.unpack P).get! (st + x)) 0 32 := by
  unfold rejW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hok, hR⟩, hn⟩, hf1⟩, hf2⟩, hc⟩ := h
  have hW : WOk R (Mz.unpack P) P st 32 :=
    ⟨Mz.rep_unpack P, hok, hR, hn, fun x hx => by
      rcases (show (P.o + st + x) / 64 = (P.o + st) / 64 ∨ (P.o + st + x) / 64 = (P.o + st + 31) / 64 by omega)
        with e | e <;> rw [e] <;> assumption⟩
  have hf := fcnt R (Mz.unpack P) P st 32 hW 0
  simp only [Nat.add_zero, Nat.mul_zero, Nat.sub_zero, Nat.min_self] at hf
  unfold lowF at hf
  rw [if_neg (by omega)] at hf
  rw [hf] at hc
  exact ⟨hR, hc⟩

/-- (b1) A rejected start: the kernel answers `lim + 1`. -/
theorem rejW_ker (R : ByteArray) (pgs2 : Array PGen) (c st lim : Nat) (hl : lim ≤ 15)
    (h : rejW R (packRP R) pgs2[c]! st lim = true) :
    kerHKG R (packRP R) pgs2 pgs2 c st R.size lim = lim + 1 := by
  obtain ⟨hR, hc⟩ := rejW_cnt R pgs2[c]! st lim h
  unfold kerHKG
  rw [if_pos hl, kerGKG_same (Mz.rep_unpack pgs2[c]!).same, kerGKG_bytes,
    kerGK_kerG R _ _ (Mz.rep_unpack pgs2[c]!) st R.size lim hl, kerG_eq _ _ _ _ _ hl]
  split
  · unfold fB preB
    rw [if_pos rfl]
    have := cntP_mono (fun x => R.get! x != (Mz.unpack pgs2[c]!).get! (st + x)) 0 R.size 0 32
      (Nat.le_refl _) (by omega)
    omega
  · rfl

/-- (b2) The scan with the reject lists what `partnerK` lists. -/
theorem pscanQ_eq (pgs2 : Array PGen) (RY : ByteArray) (sl lo hi lim : Nat) (hl : lim ≤ 15) (x : Placement) :
    pscanQ pgs2 RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi lim x =
      partnerK pgs2 RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi lim x := by
  have hsz : (revCompK RY).size = RY.size := by rw [revCompK_eq]; exact revCompB_size RY
  unfold pscanQ partnerK
  simp only [decide_eq_true_eq]
  congr 1
  funext s
  by_cases hx : x.2 = Strand.fwd
  · simp only [hx, if_true]
    split
    · next hr =>
      have := rejW_ker (revCompK RY) pgs2 x.1.chr s lim hl hr
      rw [hsz] at this
      rw [this, if_neg (by omega)]
    · rfl
  · simp only [hx, if_false]
    split
    · next hr =>
      rw [rejW_ker RY pgs2 x.1.chr s lim hl hr, if_neg (by omega)]
    · rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.rejW_cnt
#print axioms MapSpec.Fast.rejW_ker
#print axioms MapSpec.Fast.pscanQ_eq
