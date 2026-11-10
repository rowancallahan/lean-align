import ReadTrim
import AdapterTrim

/-! # The quality trimmer on bytes, against the frozen contract

`winTrim minLen letters qual`: the best quality window (`ReadTrim.trimRead`, whose compiled code is the fast `@[csimp]`
loops), then the minimum length (`AdapterTrim.dropShort`). `winTrim_contract`: for at most 10 000 letters it is
`keepB` of the frozen contract's `get_best_window` (`contractWin`): that window, or nothing when there is none or it is
shorter than `minLen` (`1 < minLen`). Used by `Proofs/Draft/Trim.lean` to fill `Spec.Trim.trim`. -/

namespace Spec.TrimCore

/-- The best window, then the minimum length. -/
def winTrim (minLen : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  match ReadTrim.trimRead letters qual with
  | some (s, e) => AdapterTrim.dropShort minLen (letters.extract s e) (qual.extract s e)
  | none => AdapterTrim.dropShort minLen ByteArray.empty ByteArray.empty

/-- The frozen contract's best window of the letters and qualities. -/
def contractWin (letters qual : ByteArray) : Option (Nat × Nat) :=
  get_best_window [] (ReadTrim.scoresOf letters qual) (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ))

/-- The window `[s, e)` kept, or nothing when there is none or it is shorter than `minLen`. -/
def keepB (minLen : Nat) (letters qual : ByteArray) : Option (Nat × Nat) → ByteArray × ByteArray
  | some (s, e) => if e - s < minLen then (ByteArray.empty, ByteArray.empty) else (letters.extract s e, qual.extract s e)
  | none => (ByteArray.empty, ByteArray.empty)

theorem sum_const (l : List Int) (c : Int) (h : ∀ x ∈ l, x = c) : l.sum = c * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons, ih (fun y hy => h y (by simp [hy])), h x (by simp), List.length_cons]
    push_cast; rw [Int.mul_add, Int.mul_one, Int.add_comm]

theorem dropShort_eq (m : Nat) (l q : ByteArray) :
    AdapterTrim.dropShort m l q = if l.size < m then (ByteArray.empty, ByteArray.empty) else (l, q) := rfl

/-- With no A/C/G/T letter, every window of the contract scores −1 000 000 per base, so its best window is one base. -/
theorem contractWin_noACGT (L Q : ByteArray) (hno : ∀ j, j < L.size → ReadTrim.isACGT L[j]! = false) (s e : Nat)
    (hw : contractWin L Q = some (s, e)) : e - s ≤ 1 := by
  unfold contractWin at hw
  have hv := get_best_window_returns_a_valid_window _ _ _ _ hw
  simp only at hv
  have hlen : (ReadTrim.scoresOf L Q).length = L.size := by simp [ReadTrim.scoresOf]
  have hm := get_best_window_returns_a_maximum_score _ _ _ _ (s, s + 1) hw (by simp) (by simp only; omega)
  have hall : ∀ x ∈ (ReadTrim.scoresOf L Q).map (ReadTrim.perBase ReadTrim.defQ), x = -1000000 := by
    intro x hx
    simp only [ReadTrim.scoresOf, List.map_map, List.mem_map, List.mem_range, Function.comp] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp [ReadTrim.perBase, ReadTrim.enc, hno i hi]
  have hws : ∀ a b, a < b → b ≤ L.size →
      window_score (ReadTrim.scoresOf L Q) (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) (a, b) =
        -1000000 * ((b - a : Nat) : Int) := by
    intro a b hab hb'
    generalize ReadTrim.scoresOf L Q = S at hall hlen ⊢
    have hsub : ∀ x ∈ ((S.drop a).take (b - a)).map (ReadTrim.perBase ReadTrim.defQ), x = -1000000 := by
      intro x hx
      apply hall x
      rw [List.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, List.mem_of_mem_drop (List.mem_of_mem_take hy), rfl⟩
    unfold window_score
    show (((S.drop a).take (b - a)).map (ReadTrim.perBase ReadTrim.defQ)).sum = _
    rw [sum_const _ _ hsub]
    simp only [List.length_map, List.length_take, List.length_drop, hlen]
    rw [Nat.min_eq_left (by omega)]
  rw [hws s (s + 1) (by omega) (by omega), hws s e hv.1 (by omega)] at hm
  omega

/-- **The byte trimmer is the frozen contract** (window, then minimum length), for at most 10 000 letters. -/
theorem winTrim_contract (minLen : Nat) (hm : 1 < minLen) (L Q : ByteArray) (h : L.size ≤ 10000) :
    winTrim minLen L Q = keepB minLen L Q (contractWin L Q) := by
  by_cases hA : ∃ j, j < L.size ∧ ReadTrim.isACGT L[j]! = true
  · obtain ⟨j, hj, hjA⟩ := hA
    have hc := ReadTrim.trimRead_def_eq_contract L Q h j hj hjA
    unfold winTrim
    rw [hc]
    unfold contractWin keepB
    split
    · rename_i s e hse
      have ha := ReadTrim.trimRead_def_acgt _ _ s e (hc.trans hse)
      rw [dropShort_eq, ByteArray.size_extract, Nat.min_eq_left ha.1]
    · rw [dropShort_eq, if_pos (by simp [ByteArray.size]; omega)]
  · have hno : ∀ j, j < L.size → ReadTrim.isACGT L[j]! = false := fun j hj => by
      cases e : ReadTrim.isACGT L[j]!
      · rfl
      · exact absurd ⟨j, hj, e⟩ hA
    have htn : ReadTrim.trimRead L Q = none := by
      cases ht : ReadTrim.trimRead L Q with
      | none => rfl
      | some w =>
        obtain ⟨s, e⟩ := w
        have ha := ReadTrim.trimRead_def_acgt _ _ s e ht
        have := ha.2.2 s (Nat.le_refl _) ha.2.1
        rw [hno s (by omega)] at this; cases this
    unfold winTrim
    rw [htn, dropShort_eq, if_pos (by simp [ByteArray.size]; omega)]
    cases hw : contractWin L Q with
    | none => rfl
    | some w =>
      obtain ⟨s, e⟩ := w
      have := contractWin_noACGT L Q hno s e hw
      simp only [keepB, if_pos (show e - s < minLen by omega)]

/-- The quality trimmer for any length: the fast `winTrim` up to 10 000 letters, else the contract directly (never
reached from valid FASTQ, which has at most 1000 letters). -/
def trimW (minLen : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  if letters.size ≤ 10000 then winTrim minLen letters qual
  else keepB minLen letters qual (contractWin letters qual)

theorem trimW_eq (minLen : Nat) (hm : 1 < minLen) (L Q : ByteArray) :
    trimW minLen L Q = keepB minLen L Q (contractWin L Q) := by
  unfold trimW; split
  · exact winTrim_contract minLen hm L Q (by assumption)
  · rfl

/-- **The fast trimmer on bytes**: the TruSeq adapter cut (`AdapterTrim.cutTruSeq`, machine-word scan), then the best
quality window and the minimum length 25 (`trimW`). `Spec.Trim.trimB_eq`: it is `Spec.Trim.trim (Spec.Trim.cut r)`. -/
def trimB (seq qual : ByteArray) : ByteArray × ByteArray :=
  let c := AdapterTrim.cutTruSeq seq qual
  trimW 25 c.1 c.2

end Spec.TrimCore

#print axioms Spec.TrimCore.winTrim_contract
