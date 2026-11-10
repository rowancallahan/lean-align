-- LOCKED (Rowan, 2026-11-10): the trimming spec.
import Proofs.Fastq
import Proofs.Draft.TrimCore

namespace Spec.Trim
open Spec.FQ

def adapter   : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList

-- cut the read where the adapter starts: all 13 letters with ≤ 1 mismatch,
-- or at least its first 6 letters exactly, running off the read's end
def cut (r : FQ.Read) : FQ.Read :=
  let adapterAt (i : Nat) : Bool :=
    let rest := r.sequence.extract i
    match decide (adapter.length ≤ rest.length) with
    | true =>
      ((adapter.zip rest).filter fun (a, b) => a != b).length ≤ 1
    | false =>
      6 ≤ rest.length && rest == adapter.extract 0 rest.length
  let c := ((List.range r.sequence.length).find? adapterAt).getD r.sequence.length
  ⟨r.name, r.sequence.extract 0 c, r.quality.extract 0 c⟩

-- the score of the window [start, stop) of a read: each base scores Phred - 25,
-- and an N rules the window out
def windowScore (r : FQ.Read) (start stop : Nat) : Int :=
  let baseScore (b q : UInt8) : Int :=
    match b with
    | 0x41 | 0x43 | 0x47 | 0x54 =>
      (min (q.toNat - 33) 93 : Nat) - 25
    | _ =>
      -1000000
  (List.zipWith baseScore (r.sequence.extract start stop) (r.quality.extract start stop)).sum

def minLength : Nat := 25

def trim (r : FQ.Read) : FQ.Read :=
  let t := if r.sequence.length ≤ 10000 then
      TrimCore.winTrim minLength ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
    else
      TrimCore.keepB minLength ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
        (TrimCore.contractWin ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩)
  ⟨r.name, t.1.data.toList, t.2.data.toList⟩

/-! ## Proof of `trim_correct` -/

/-- `trim` is the frozen contract's best window, kept when at least `minLength` long (`TrimCore.winTrim_contract`). -/
theorem trim_eq (r : FQ.Read) :
    trim r = ⟨r.name,
      (TrimCore.keepB minLength ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
        (TrimCore.contractWin ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩)).1.data.toList,
      (TrimCore.keepB minLength ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
        (TrimCore.contractWin ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩)).2.data.toList⟩ := by
  unfold trim
  split
  · rename_i h
    rw [TrimCore.winTrim_contract minLength (by decide) _ _ (by simpa [ByteArray.size] using h)]
  · rfl

/-- The per-base score of `windowScore`. -/
def baseScoreS (b q : UInt8) : Int :=
  match b with
  | 0x41 | 0x43 | 0x47 | 0x54 =>
    (min (q.toNat - 33) 93 : Nat) - 25
  | _ =>
    -1000000

theorem windowScore_eq (r : FQ.Read) (start stop : Nat) :
    windowScore r start stop =
      (List.zipWith baseScoreS (r.sequence.extract start stop) (r.quality.extract start stop)).sum := rfl

theorem baseScoreS_eq (b q : UInt8) : ReadTrim.perBase ReadTrim.defQ (ReadTrim.enc b q) = baseScoreS b q := by
  unfold baseScoreS
  split <;> simp_all [ReadTrim.perBase, ReadTrim.enc, ReadTrim.isACGT, ReadTrim.defQ] <;> omega

theorem ba_size (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  show l.toArray.size = l.length; simp

theorem ba_get (l : List UInt8) (i : Nat) (h : i < l.length) : (⟨l.toArray⟩ : ByteArray)[i]! = l[i] := by
  rw [getElem!_pos (⟨l.toArray⟩ : ByteArray) i (by rw [ba_size]; exact h)]; rfl

theorem scoresOf_length (L Q : ByteArray) : (ReadTrim.scoresOf L Q).length = L.size := by
  unfold ReadTrim.scoresOf; simp

theorem scoresOf_get (L Q : ByteArray) (i : Nat) (h : i < (ReadTrim.scoresOf L Q).length) :
    (ReadTrim.scoresOf L Q)[i] = ReadTrim.enc L[i]! Q[i]! := by
  simp only [ReadTrim.scoresOf, List.getElem_map, List.getElem_range]

theorem window_score_eq (r : FQ.Read) (h : r.sequence.length = r.quality.length) (a b : Nat) (hab : a < b)
    (hb : b ≤ r.sequence.length) :
    window_score (ReadTrim.scoresOf ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩)
      (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) (a, b) = windowScore r a b := by
  rw [windowScore_eq]
  unfold window_score
  show (List.map (ReadTrim.perBase ReadTrim.defQ)
    (((ReadTrim.scoresOf ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).drop a).take (b - a))).sum = _
  have hl := scoresOf_length ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
  rw [ba_size] at hl
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, hl, List.length_zipWith, List.extract]
    omega
  · intro k h1 h2
    simp only [List.length_map, List.length_take, List.length_drop, hl] at h1
    rw [List.getElem_map, List.getElem_take, List.getElem_drop, scoresOf_get, List.getElem_zipWith, baseScoreS_eq]
    simp only [List.extract, List.getElem_take, List.getElem_drop]
    rw [ba_get _ _ (by omega), ba_get _ _ (by omega)]

-- the kept part is a best window [start, stop): no proposed window scores higher;
-- it is dropped if shorter than `minLength`
theorem trim_correct (r : FQ.Read) (h : r.sequence.length = r.quality.length) :
    (r.sequence = [] ∧
     trim r = ⟨r.name, [], []⟩)
    ∨
    ∃ start stop,
      let windowLength := stop - start
      start < stop ∧
      stop ≤ r.sequence.length ∧
      (∀ proposedStart proposedStop,
        (proposedStart < proposedStop ∧ proposedStop ≤ r.sequence.length) →
        windowScore r proposedStart proposedStop ≤ windowScore r start stop) ∧
      trim r =
        match decide (minLength ≤ windowLength) with
        | true =>
          ⟨r.name, r.sequence.extract start stop, r.quality.extract start stop⟩
        | false =>
          ⟨r.name, [], []⟩ := by
  have hl := scoresOf_length ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
  rw [ba_size] at hl
  by_cases hn : r.sequence = []
  · left
    refine ⟨hn, ?_⟩
    have hw : TrimCore.contractWin ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ = none := by
      unfold TrimCore.contractWin
      cases hc : get_best_window [] (ReadTrim.scoresOf ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩)
          (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) with
      | none => rfl
      | some w =>
        have := get_best_window_returns_a_valid_window _ _ _ _ hc
        rw [hl, hn] at this; simp at this; omega
    rw [trim_eq, hw]
    simp [TrimCore.keepB]
  · right
    have hpos : 0 < (ReadTrim.scoresOf ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).length := by
      rw [hl]; exact List.length_pos_iff.mpr hn
    obtain ⟨⟨s, e⟩, hw⟩ := get_best_window_returns_some_when_scores_nonempty [] _
      (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) hpos
    have hv := get_best_window_returns_a_valid_window _ _ _ _ hw
    simp only [hl] at hv
    refine ⟨s, e, hv.1, hv.2, fun ps pe hp => ?_, ?_⟩
    · have hm := get_best_window_returns_a_maximum_score _ _ _ _ (ps, pe) hw hp.1 (by simp only [hl]; exact hp.2)
      rwa [window_score_eq r h ps pe hp.1 hp.2, window_score_eq r h s e hv.1 hv.2] at hm
    · have hc : TrimCore.contractWin ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ = some (s, e) := hw
      rw [trim_eq, hc]
      by_cases hm : minLength ≤ e - s
      · simp [TrimCore.keepB, hm, show ¬ e - s < minLength by omega, ByteArray.data_extract, List.extract]
      · simp [TrimCore.keepB, hm, show e - s < minLength by omega]

end Spec.Trim

#print axioms Spec.Trim.trim_correct
