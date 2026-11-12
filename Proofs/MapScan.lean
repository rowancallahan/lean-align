import Proofs.MapFast
import Proofs.MapStream
/-! # `MapFast.advance` (the scan of `cutSlices`) is `cutLines` on the buffer's bytes. Ported from byte_specs/CutAfter.lean. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast

theorem advance_succ (b : ByteArray) (n i : Nat) :
    advance b (n + 1) i = if findNewline b i < b.size then
      ((advance b n (findNewline b i + 1)).1, (advance b n (findNewline b i + 1)).2 + 1) else (b.size, 0) := by
  simp only [advance]
  try (split <;> rfl)

theorem splitNl_none : ∀ l : List UInt8, newline ∉ l → splitNl l = none
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ newline := fun e => h (by simp [e])
    simp [splitNl, hx, splitNl_none xs (fun e => h (List.mem_cons_of_mem _ e))]

theorem advance_ge (b : ByteArray) : ∀ n p, p ≤ b.size → p ≤ (advance b n p).1 ∧ (advance b n p).1 ≤ b.size
  | 0, p, h => by simp [advance, h]
  | n + 1, p, h => by
    have hs := findNewlineGo_spec b (b.size - p) p h (Nat.le_refl _)
    rw [advance_succ]
    split
    · rename_i hj
      have := advance_ge b n (findNewline b p + 1) (by omega)
      have h1 : p ≤ findNewline b p := hs.1
      simp only []
      omega
    · simp [h]

theorem take_cut (c R : List UInt8) (m : Nat) : (c ++ newline :: R).take (c.length + 1 + m) = c ++ newline :: R.take m := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  rw [show c.length + 1 + m - c.length = m + 1 by omega, List.take_succ_cons]

-- the recursion cuts the bytes of `b` from `i` on exactly like `cutLines`
theorem cutLines_advance (b : ByteArray) : ∀ n i, i ≤ b.size →
    cutLines n (L b i) = if (advance b n i).2 = n then some ((L b i).take ((advance b n i).1 - i), L b (advance b n i).1) else none
  | 0, i, h => by simp [cutLines, advance]
  | n + 1, i, h => by
    have hs := findNewlineGo_spec b (b.size - i) i h (Nat.le_refl _)
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hj : findNewline b i = findNewlineGo b (b.size - i) i := rfl
    rw [← hj] at h1 h2 h3 h4
    rw [advance_succ]
    by_cases hlt : findNewline b i < b.size
    · have hL := h4 hlt
      have hsplit : L b i = (L b i).take (findNewline b i - i) ++ newline :: L b (findNewline b i + 1) := by
        rw [← hL]; exact L_split b i _ h1
      have hsn : splitNl (L b i) = some ((L b i).take (findNewline b i - i), L b (findNewline b i + 1)) := by
        have := splitNl_append ((L b i).take (findNewline b i - i)) (L b (findNewline b i + 1)) h3
        rw [← hsplit] at this
        exact this
      have ih := cutLines_advance b n (findNewline b i + 1) (by omega)
      have hge := advance_ge b n (findNewline b i + 1) (by omega)
      have hlen : ((L b i).take (findNewline b i - i)).length = findNewline b i - i := by
        simp [L]; omega
      rw [if_pos hlt]
      simp only [cutLines, hsn, Option.bind_some, ih]
      by_cases hf : (advance b n (findNewline b i + 1)).2 = n
      · simp only [hf, if_true, Option.map_some]
        congr 2
        generalize hc : (L b i).take (findNewline b i - i) = c at hsplit hlen
        have key := take_cut c (L b (findNewline b i + 1)) ((advance b n (findNewline b i + 1)).1 - (findNewline b i + 1))
        rw [hlen, show findNewline b i - i + 1 + ((advance b n (findNewline b i + 1)).1 - (findNewline b i + 1)) =
          (advance b n (findNewline b i + 1)).1 - i by omega, ← hsplit] at key
        rw [key]
      · simp [hf]
    · have hnl : newline ∉ L b i := by
        have : findNewline b i = b.size := by omega
        have h3' := h3
        rw [this] at h3'
        have hl : (L b i).take (b.size - i) = L b i := by
          apply List.take_of_length_le; simp [L]
        rwa [hl] at h3'
      simp [cutLines, splitNl_none _ hnl, hlt]

-- the newline found by `findNewline`, as a split of the bytes from `i` on
theorem findNewline_split (b : ByteArray) (i : Nat) (h : i ≤ b.size) :
    (findNewline b i < b.size → i ≤ findNewline b i ∧
      L b i = (L b i).take (findNewline b i - i) ++ newline :: L b (findNewline b i + 1) ∧
      newline ∉ (L b i).take (findNewline b i - i)) ∧
    (¬ findNewline b i < b.size → newline ∉ L b i) := by
  obtain ⟨h1, h2, h3, h4⟩ := findNewlineGo_spec b (b.size - i) i h (Nat.le_refl _)
  have hj : findNewline b i = findNewlineGo b (b.size - i) i := rfl
  rw [← hj] at h1 h2 h3 h4
  refine ⟨fun hlt => ⟨h1, ?_, h3⟩, fun hlt => ?_⟩
  · rw [← h4 hlt]; exact L_split b i _ h1
  · have : findNewline b i = b.size := by omega
    have h3' := h3
    rw [this] at h3'
    have hl : (L b i).take (b.size - i) = L b i := by
      apply List.take_of_length_le; simp [L]
    rwa [hl] at h3'

theorem advance_le (b : ByteArray) : ∀ n p, (advance b n p).2 ≤ n
  | 0, p => by simp [advance]
  | n + 1, p => by
    rw [advance_succ]; split
    · have := advance_le b n (findNewline b p + 1); simp only []; omega
    · simp

-- fewer than `n` newlines found: the loop scanned to the end and counted every newline there
theorem advance_count (b : ByteArray) : ∀ n i, i ≤ b.size → (advance b n i).2 < n →
    (advance b n i).2 = (L b i).count newline ∧ (advance b n i).1 = b.size
  | 0, i, _, h => by simp [advance] at h
  | n + 1, i, hi, h => by
    obtain ⟨hs1, hs2⟩ := findNewline_split b i hi
    rw [advance_succ] at h ⊢
    by_cases hlt : findNewline b i < b.size
    · obtain ⟨hge, hsp, hnc⟩ := hs1 hlt
      rw [if_pos hlt] at h ⊢
      simp only [] at h ⊢
      have ih := advance_count b n (findNewline b i + 1) (by omega) (by omega)
      have hcz : ((L b i).take (findNewline b i - i)).count newline = 0 := List.count_eq_zero.2 hnc
      refine ⟨?_, ih.2⟩
      have e := congrArg (List.count newline) hsp
      rw [List.count_append, List.count_cons_self, hcz] at e
      omega
    · rw [if_neg hlt] at h ⊢
      simp [List.count_eq_zero.2 (hs2 hlt)]


theorem splitNl_noNl_append (P Q : List UInt8) (h : newline ∉ P) :
    splitNl (P ++ Q) = (splitNl Q).map fun (c, r) => (P ++ c, r) := by
  induction P with
  | nil => cases hq : splitNl Q <;> simp [hq]
  | cons x xs ih =>
    have hx : x ≠ newline := fun e => h (by simp [e])
    have := ih (fun e => h (List.mem_cons_of_mem _ e))
    simp only [List.cons_append, splitNl, hx, if_false, this]
    cases hq : splitNl Q <;> simp [hq]


theorem cutLines_pos (n : Nat) (l pre post : List UInt8) (h : cutLines (n + 1) l = some (pre, post)) : pre ≠ [] := by
  unfold cutLines at h
  cases hs : splitNl l with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨c, rest⟩ := p
    cases hr : cutLines n rest with
    | none => simp [hs, hr] at h
    | some q =>
      simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp


-- the carry buffer's scanned prefix `P` (with `count P` newlines) followed by `Q`: the cut continues in `Q`
theorem cutLines_append_count : ∀ (len : Nat) (P Q : List UInt8) (n : Nat), P.length = len → P.count newline < n →
    cutLines n (P ++ Q) = (cutLines (n - P.count newline) Q).map fun (a, b) => (P ++ a, b)
  | len, P, Q, n, hl, hc => by
    by_cases hm : newline ∈ P
    · obtain ⟨c, P', hs⟩ := splitNl_of_mem P hm
      have e := splitNl_spec P c P' hs
      have hcf := splitNl_nl_free P c P' hs
      have hcc : c.count newline = 0 := List.count_eq_zero.2 hcf
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcnt : P.count newline = P'.count newline + 1 := by
        rw [e, List.count_append, List.count_cons_self, hcc]; omega
      have hlen : P'.length < len := by rw [← hl, e]; simp; omega
      have ih := cutLines_append_count P'.length P' Q m rfl (by omega)
      have hsn : splitNl (P ++ Q) = some (c, P' ++ Q) := by
        rw [e, List.append_assoc, List.cons_append]; exact splitNl_append c _ hcf
      have hsucc : cutLines (m + 1) (P ++ Q) = (cutLines m (P' ++ Q)).map fun (pre, post) => (c ++ newline :: pre, post) := by
        rw [cutLines.eq_2, hsn]; simp only [Option.bind_some]
      rw [hsucc, ih, show m + 1 - P.count newline = m - P'.count newline by omega]
      cases hq : cutLines (m - P'.count newline) Q with
      | none => simp
      | some q =>
        obtain ⟨a1, a2⟩ := q
        simp only [Option.map_some]
        congr 2
        rw [e]; simp
    · have hz : P.count newline = 0 := List.count_eq_zero.2 hm
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      unfold cutLines
      rw [splitNl_noNl_append P Q hm, hz]
      simp only [Nat.sub_zero]
      cases hs : splitNl Q with
      | none => simp
      | some p =>
        obtain ⟨c, r⟩ := p
        simp only [Option.map_some, Option.bind_some]
        cases cutLines m r <;> simp


end Spec.FQ.MapStream
