import Spec.Shim
/-! The reader's `cutAfter` (the `for` loop of Spec/Shim.lean, unchanged) is `cutLines`, the list model used by `slices_parse`
(FastqSlices.lean): if the loop finds all `n` newlines, the bytes `[i, p)` are `cutLines`' prefix and the buffer from `p` on its rest;
if it finds fewer, `cutLines` is `none`. Imports Spec.Shim only (not Proofs.Fastq: the two define the same names), so the
definitions `splitNl`, `cutLines`, `L` and `findNewlineGo_spec` below are copies of those in FastqSlices.lean / Proofs/Fastq.lean
(`check_copies.sh` diffs them). Check: `lake env lean Testing/notes/byte_specs/CutAfter.lean`. -/
namespace Spec.FQ

-- the first line (without its newline) and what follows; none if there is no newline
def splitNl : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | x :: xs => if x = newline then some ([], xs) else (splitNl xs).map fun (c, r) => (x :: c, r)

theorem splitNl_append : ∀ (c r : List UInt8), newline ∉ c → splitNl (c ++ newline :: r) = some (c, r)
  | [], r, _ => by simp [splitNl]
  | x :: xs, r, h => by
    have hx : x ≠ newline := fun e => h (by simp [e])
    have ih := splitNl_append xs r (fun e => h (List.mem_cons_of_mem _ e))
    simp [splitNl, hx, ih]

theorem splitNl_spec : ∀ (l c r : List UInt8), splitNl l = some (c, r) → l = c ++ newline :: r
  | [], c, r, h => by simp [splitNl] at h
  | x :: xs, c, r, h => by
    unfold splitNl at h
    split at h
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := by simpa using h
      simp [hx]
    · cases hr : splitNl xs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨c', r'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [splitNl_spec xs c' r' hr]; rfl

def cutLines : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, l => some ([], l)
  | n + 1, l => (splitNl l).bind fun (c, rest) => (cutLines n rest).map fun (pre, post) => (c ++ newline :: pre, post)

theorem cutLines_spec : ∀ (n : Nat) (l pre post : List UInt8), cutLines n l = some (pre, post) → l = pre ++ post
  | 0, l, pre, post, h => by simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, l, pre, post, h => by
    unfold cutLines at h
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      cases hc : cutLines n rest with
      | none => simp [hs, hc] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hc, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [splitNl_spec l c rest hs, cutLines_spec n rest p1 p2 hc]; simp

-- the bytes of `b` from byte `i` on
def L (b : ByteArray) (i : Nat) : List UInt8 := b.data.toList.drop i

theorem L_cons (b : ByteArray) (i : Nat) (h : i < b.size) : L b i = b[i]! :: L b (i + 1) := by
  unfold L
  rw [List.drop_eq_getElem_cons (by simpa using h), getElem!_pos b i h, Array.getElem_toList,
    ← ByteArray.getElem_eq_getElem_data]

theorem L_size (b : ByteArray) (i : Nat) (h : b.size ≤ i) : L b i = [] := by
  unfold L; simp; simpa using h

theorem extract_list (b : ByteArray) (i j : Nat) : (b.extract i j).data.toList = (L b i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take]; rfl

theorem L_split (b : ByteArray) (i j : Nat) (h : i ≤ j) : L b i = (L b i).take (j - i) ++ L b j := by
  conv => lhs; rw [← List.take_append_drop (j - i) (L b i)]
  unfold L; rw [List.drop_drop, Nat.add_sub_cancel' h]

theorem findNewlineGo_spec (b : ByteArray) : ∀ k i, i ≤ b.size → b.size - i ≤ k →
    i ≤ findNewlineGo b k i ∧ findNewlineGo b k i ≤ b.size ∧
    newline ∉ (L b i).take (findNewlineGo b k i - i) ∧
    (findNewlineGo b k i < b.size → L b (findNewlineGo b k i) = newline :: L b (findNewlineGo b k i + 1))
  | 0, i, h1, h2 => by
    have : i = b.size := by omega
    subst this; simp [findNewlineGo]
  | k + 1, i, h1, h2 => by
    rw [findNewlineGo]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨hi, hb⟩ := hc
      obtain ⟨a1, a2, a3, a4⟩ := findNewlineGo_spec b k (i + 1) (by omega) (by omega)
      refine ⟨by omega, a2, ?_, a4⟩
      rw [L_cons b i hi, show findNewlineGo b k (i + 1) - i = (findNewlineGo b k (i + 1) - (i + 1)) + 1 by omega,
        List.take_succ_cons]
      intro m
      rcases List.mem_cons.mp m with e | e
      · exact hb (by rw [← e]; rfl)
      · exact a3 e
    · rename_i hc
      refine ⟨Nat.le_refl _, h1, by simp, ?_⟩
      intro hi
      rw [L_cons b i hi]
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
      rw [hc hi]; rfl


theorem splitNl_none : ∀ l : List UInt8, newline ∉ l → splitNl l = none
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ newline := fun e => h (by simp [e])
    simp [splitNl, hx, splitNl_none xs (fun e => h (List.mem_cons_of_mem _ e))]

-- the loop as a recursion on the number of newlines wanted: (position after the last newline found, newlines found)
def cutAfterR (b : ByteArray) : Nat → Nat → Nat × Nat
  | 0, p => (p, 0)
  | n + 1, p => if findNewline b p < b.size then
      let r := cutAfterR b n (findNewline b p + 1); (r.1, r.2 + 1) else (b.size, 0)

theorem cutAfterR_ge (b : ByteArray) : ∀ n p, p ≤ b.size → p ≤ (cutAfterR b n p).1 ∧ (cutAfterR b n p).1 ≤ b.size
  | 0, p, h => by simp [cutAfterR, h]
  | n + 1, p, h => by
    have hs := findNewlineGo_spec b (b.size - p) p h (Nat.le_refl _)
    unfold cutAfterR
    split
    · rename_i hj
      have := cutAfterR_ge b n (findNewline b p + 1) (by omega)
      have h1 : p ≤ findNewline b p := hs.1
      simp only []
      omega
    · simp [h]

theorem loop_eq (b : ByteArray) (l : List Nat) : ∀ s : Nat × Nat,
    (forIn l s (fun _ (s : Nat × Nat) =>
        if findNewline b s.fst < b.size then ForInStep.yield (findNewline b s.fst + 1, s.snd + 1)
        else ForInStep.done (b.size, s.snd)) : Id (Nat × Nat)) =
      ((cutAfterR b l.length s.1).1, (cutAfterR b l.length s.1).2 + s.2) := by
  induction l with
  | nil => intro s; simp only [List.forIn_nil, List.length_nil, cutAfterR]; show s = _; simp
  | cons x xs ih =>
    intro s
    rw [List.forIn_cons]
    by_cases h : findNewline b s.fst < b.size
    · simp only [h, ite_true]
      show forIn xs _ _ = _
      rw [ih]
      simp only [List.length_cons, cutAfterR, h, ite_true]
      ext <;> simp [Nat.add_assoc, Nat.add_comm]
    · rw [if_neg h]
      simp only [List.length_cons, cutAfterR, if_neg h]
      show (b.size, s.snd) = _
      simp

-- THE loop of Spec/Shim.lean is the recursion
theorem cutAfter_eq (b : ByteArray) (i n : Nat) : Pipe.cutAfter b i n = cutAfterR b n i := by
  unfold Pipe.cutAfter
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Id.run, bind, pure]
  have := loop_eq b (List.range' 0 [:n].size) (i, 0)
  simp only [] at this
  simp [Std.Legacy.Range.size] at this ⊢
  rw [this]

theorem take_cut (c R : List UInt8) (m : Nat) : (c ++ newline :: R).take (c.length + 1 + m) = c ++ newline :: R.take m := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  rw [show c.length + 1 + m - c.length = m + 1 by omega, List.take_succ_cons]

-- the recursion cuts the bytes of `b` from `i` on exactly like `cutLines`
theorem cutLines_cutAfterR (b : ByteArray) : ∀ n i, i ≤ b.size →
    cutLines n (L b i) = if (cutAfterR b n i).2 = n then some ((L b i).take ((cutAfterR b n i).1 - i), L b (cutAfterR b n i).1) else none
  | 0, i, h => by simp [cutLines, cutAfterR]
  | n + 1, i, h => by
    have hs := findNewlineGo_spec b (b.size - i) i h (Nat.le_refl _)
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hj : findNewline b i = findNewlineGo b (b.size - i) i := rfl
    rw [← hj] at h1 h2 h3 h4
    unfold cutAfterR
    by_cases hlt : findNewline b i < b.size
    · have hL := h4 hlt
      have hsplit : L b i = (L b i).take (findNewline b i - i) ++ newline :: L b (findNewline b i + 1) := by
        rw [← hL]; exact L_split b i _ h1
      have hsn : splitNl (L b i) = some ((L b i).take (findNewline b i - i), L b (findNewline b i + 1)) := by
        have := splitNl_append ((L b i).take (findNewline b i - i)) (L b (findNewline b i + 1)) h3
        rw [← hsplit] at this
        exact this
      have ih := cutLines_cutAfterR b n (findNewline b i + 1) (by omega)
      have hge := cutAfterR_ge b n (findNewline b i + 1) (by omega)
      have hlen : ((L b i).take (findNewline b i - i)).length = findNewline b i - i := by
        simp [L]; omega
      rw [if_pos hlt]
      simp only [cutLines, hsn, Option.bind_some, ih]
      by_cases hf : (cutAfterR b n (findNewline b i + 1)).2 = n
      · simp only [hf, if_true, Option.map_some]
        congr 2
        generalize hc : (L b i).take (findNewline b i - i) = c at hsplit hlen
        have key := take_cut c (L b (findNewline b i + 1)) ((cutAfterR b n (findNewline b i + 1)).1 - (findNewline b i + 1))
        rw [hlen, show findNewline b i - i + 1 + ((cutAfterR b n (findNewline b i + 1)).1 - (findNewline b i + 1)) =
          (cutAfterR b n (findNewline b i + 1)).1 - i by omega, ← hsplit] at key
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

-- what the reader uses: if the loop found all `n` newlines, the bytes up to `p` are `cutLines`' prefix
theorem cutAfter_cutLines (b : ByteArray) (i n p : Nat) (hi : i ≤ b.size) (h : Pipe.cutAfter b i n = (p, n)) :
    cutLines n (L b i) = some ((L b i).take (p - i), L b p) := by
  rw [cutAfter_eq] at h
  rw [cutLines_cutAfterR b n i hi, h]
  simp

-- and if it found fewer, `cutLines` finds none: the rest of the buffer has fewer than `n` newlines
theorem cutAfter_none (b : ByteArray) (i n p f : Nat) (hi : i ≤ b.size) (h : Pipe.cutAfter b i n = (p, f)) (hf : f ≠ n) :
    cutLines n (L b i) = none := by
  rw [cutAfter_eq] at h
  rw [cutLines_cutAfterR b n i hi, h]
  simp [hf]

#print axioms cutAfter_eq
#print axioms cutAfter_cutLines
#print axioms cutAfter_none


/-! ## Part 3: the reader loop as a pure function of the blocks `readBig` returns -/

-- the slices (copy of FastqSlices.lean)
def sliceAt (n : Nat) (l : List UInt8) : List (List UInt8) :=
  if l = [] then [] else
  match hc : cutLines n l with
  | some (pre, post) => if hp : pre = [] then [l] else pre :: sliceAt n post
  | none => [l]
termination_by l.length
decreasing_by
  have h1 := cutLines_spec n l pre post hc
  have h2 : 0 < pre.length := List.length_pos_iff.2 hp
  rw [h1, List.length_append]; omega

theorem splitNl_nl_free : ∀ (l c r : List UInt8), splitNl l = some (c, r) → newline ∉ c
  | [], c, r, h => by simp [splitNl] at h
  | x :: xs, c, r, h => by
    unfold splitNl at h
    split at h
    · obtain ⟨rfl, rfl⟩ := by simpa using h
      simp
    · rename_i hx
      cases hr : splitNl xs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨c', r'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := splitNl_nl_free xs c' r' hr
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hx e.symm, this⟩

theorem splitNl_noNl_append (P Q : List UInt8) (h : newline ∉ P) :
    splitNl (P ++ Q) = (splitNl Q).map fun (c, r) => (P ++ c, r) := by
  induction P with
  | nil => cases hq : splitNl Q <;> simp [hq]
  | cons x xs ih =>
    have hx : x ≠ newline := fun e => h (by simp [e])
    have := ih (fun e => h (List.mem_cons_of_mem _ e))
    simp only [List.cons_append, splitNl, hx, if_false, this]
    cases hq : splitNl Q <;> simp [hq]

theorem splitNl_of_mem : ∀ l : List UInt8, newline ∈ l → ∃ c r, splitNl l = some (c, r)
  | [], h => by simp at h
  | x :: xs, h => by
    unfold splitNl
    by_cases hx : x = newline
    · exact ⟨[], xs, by simp [hx]⟩
    · have : newline ∈ xs := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hx
        · exact e
      obtain ⟨c, r, hr⟩ := splitNl_of_mem xs this
      exact ⟨x :: c, r, by simp [hx, hr]⟩

theorem cutLines_none_of_count : ∀ (n : Nat) (l : List UInt8), l.count newline < n → cutLines n l = none
  | 0, l, h => by omega
  | n + 1, l, h => by
    unfold cutLines
    cases hs : splitNl l with
    | none => simp
    | some p =>
      obtain ⟨c, r⟩ := p
      have e := splitNl_spec l c r hs
      have hc := splitNl_nl_free l c r hs
      have hcc : c.count newline = 0 := List.count_eq_zero.2 hc
      rw [e, List.count_append, List.count_cons_self, hcc] at h
      have := cutLines_none_of_count n r (by omega)
      simp [this]

theorem cutLines_extend : ∀ (n : Nat) (l pre post R : List UInt8), cutLines n l = some (pre, post) →
    cutLines n (l ++ R) = some (pre, post ++ R)
  | 0, l, pre, post, R, h => by
    simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; simp [cutLines]
  | n + 1, l, pre, post, R, h => by
    unfold cutLines at h ⊢
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      have e := splitNl_spec l c rest hs
      have hc := splitNl_nl_free l c rest hs
      cases hr : cutLines n rest with
      | none => simp [hs, hr] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hsn : splitNl (l ++ R) = some (c, rest ++ R) := by
          rw [e, List.append_assoc, List.cons_append]; exact splitNl_append c _ hc
        simp [hsn, cutLines_extend n rest p1 p2 R hr]

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

theorem cutAfterR_le (b : ByteArray) : ∀ n p, (cutAfterR b n p).2 ≤ n
  | 0, p => by simp [cutAfterR]
  | n + 1, p => by
    unfold cutAfterR; split
    · have := cutAfterR_le b n (findNewline b p + 1); simp only []; omega
    · simp

-- fewer than `n` newlines found: the loop scanned to the end and counted every newline there
theorem cutAfterR_count (b : ByteArray) : ∀ n i, i ≤ b.size → (cutAfterR b n i).2 < n →
    (cutAfterR b n i).2 = (L b i).count newline ∧ (cutAfterR b n i).1 = b.size
  | 0, i, _, h => by simp [cutAfterR] at h
  | n + 1, i, hi, h => by
    obtain ⟨hs1, hs2⟩ := findNewline_split b i hi
    unfold cutAfterR at h ⊢
    by_cases hlt : findNewline b i < b.size
    · obtain ⟨hge, hsp, hnc⟩ := hs1 hlt
      rw [if_pos hlt] at h ⊢
      simp only [] at h ⊢
      have ih := cutAfterR_count b n (findNewline b i + 1) (by omega) (by omega)
      have hcz : ((L b i).take (findNewline b i - i)).count newline = 0 := List.count_eq_zero.2 hnc
      refine ⟨?_, ih.2⟩
      have e := congrArg (List.count newline) hsp
      rw [List.count_append, List.count_cons_self, hcz] at e
      omega
    · rw [if_neg hlt] at h ⊢
      simp [List.count_eq_zero.2 (hs2 hlt)]

theorem data_toList_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

-- ## the reader loop of Spec/Shim.lean, as a pure function of the blocks `readBig` returns (nonempty, in order; then it returns empty)
-- (state: carry buffer, scan position, newlines counted so far, blocks still to come, end of input seen); `fuel` only makes it total
def readerGo (need : Nat) : Nat → ByteArray → Nat → Nat → List ByteArray → Bool → List ByteArray
  | 0, _, _, _, _, _ => []
  | fuel + 1, carry, scan, lines, blocks, eof =>
    match Pipe.cutAfter carry scan (need - lines) with
    | (p, f) =>
      if lines + f = need then
        carry.extract 0 p :: readerGo need fuel (carry.extract p carry.size) 0 0 blocks eof
      else if eof then (if 0 < carry.size then [carry] else [])
      else match blocks with
        | [] => readerGo need fuel carry carry.size (lines + f) [] true
        | blk :: rest => readerGo need fuel (carry ++ blk) carry.size (lines + f) rest false

def flat (bs : List ByteArray) : List UInt8 := bs.flatMap (·.data.toList)
def total (bs : List ByteArray) : Nat := (bs.map (·.size)).sum
def pot (carry : ByteArray) (bs : List ByteArray) (eof : Bool) : Nat :=
  2 * (carry.size + total bs) + 2 * bs.length + (if eof then 0 else 1)

theorem sliceAt_nil (n : Nat) : sliceAt n [] = [] := by rw [sliceAt]; simp

theorem sliceAt_none (n : Nat) (l : List UInt8) (hl : l ≠ []) (hn : cutLines n l = none) : sliceAt n l = [l] := by
  rw [sliceAt, if_neg hl]
  split
  · rename_i pre post h; rw [hn] at h; cases h
  · rfl

theorem sliceAt_some (n : Nat) (l pre post : List UInt8) (h : cutLines n l = some (pre, post)) (hp : pre ≠ []) :
    sliceAt n l = pre :: sliceAt n post := by
  have hl : l ≠ [] := by
    intro hh; rw [hh] at h
    have := cutLines_spec n [] pre post h
    exact hp (List.append_eq_nil_iff.1 this.symm).1
  rw [sliceAt, if_neg hl]
  split
  · rename_i pre' post' h'; rw [h] at h'; cases h'; simp [hp]
  · rename_i h'; rw [h] at h'; cases h'

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := (Array.length_toList).symm

theorem pot_cut (carry : ByteArray) (p : Nat) (bs : List ByteArray) (eof : Bool) (h1 : 0 < p) (h2 : p ≤ carry.size) :
    pot (carry.extract p carry.size) bs eof < pot carry bs eof := by
  unfold pot; rw [ByteArray.size_extract]; omega

theorem reader_eq (need : Nat) (hneed : 0 < need) : ∀ (fuel : Nat) (carry : ByteArray) (scan lines : Nat)
    (bs : List ByteArray) (eof : Bool), pot carry bs eof < fuel → scan ≤ carry.size →
    (carry.data.toList.take scan).count newline = lines → lines < need → (eof = true → bs = []) →
    (readerGo need fuel carry scan lines bs eof).map (·.data.toList) = sliceAt need (carry.data.toList ++ flat bs)
  | 0, carry, scan, lines, bs, eof, hp, _, _, _, _ => by omega
  | fuel + 1, carry, scan, lines, bs, eof, hp, hscan, hcount, hlines, heof => by
    unfold readerGo
    cases hca : Pipe.cutAfter carry scan (need - lines) with
    | mk p f =>
    simp only []
    have hca' := hca
    rw [cutAfter_eq] at hca'
    have hlist : carry.data.toList = carry.data.toList.take scan ++ L carry scan := by
      simp [L]
    by_cases hcut : lines + f = need
    · have hfn : f = need - lines := by omega
      subst hfn
      rw [if_pos hcut]
      have hc := cutAfter_cutLines carry scan (need - lines) p hscan hca
      have hge := cutAfterR_ge carry (need - lines) scan hscan
      rw [hca'] at hge
      simp only [] at hge
      have hext := cutLines_extend _ _ _ _ (flat bs) hc
      have happ := cutLines_append_count _ (carry.data.toList.take scan) (L carry scan ++ flat bs) need rfl (by omega)
      rw [hcount, hext] at happ
      simp only [Option.map_some] at happ
      have hpos : ((L carry scan).take (p - scan)) ≠ [] := by
        obtain ⟨m, hm⟩ : ∃ m, need - lines = m + 1 := ⟨need - lines - 1, by omega⟩
        rw [hm] at hc
        exact cutLines_pos m _ _ _ hc
      have hpp : scan < p := by
        rcases Nat.lt_or_ge scan p with h | h
        · exact h
        · exfalso; apply hpos
          rw [show p - scan = 0 by omega]; simp
      have hT : carry.data.toList ++ flat bs = carry.data.toList.take scan ++ (L carry scan ++ flat bs) := by
        conv => lhs; rw [hlist]
        simp
      have hsl : sliceAt need (carry.data.toList ++ flat bs) =
          (carry.data.toList.take p) :: sliceAt need (L carry p ++ flat bs) := by
        have hne2 : carry.data.toList.take scan ++ (L carry scan).take (p - scan) ≠ [] := by
          intro hh; exact hpos (List.append_eq_nil_iff.1 hh).2
        have h5 : carry.data.toList.take scan ++ (L carry scan).take (p - scan) = carry.data.toList.take p := by
          obtain ⟨d, rfl⟩ : ∃ d, p = scan + d := ⟨p - scan, by omega⟩
          rw [List.take_add]; simp [L]
        rw [hT, sliceAt_some need _ _ _ happ hne2, h5]
      rw [hsl, List.map_cons]
      have hex : (carry.extract 0 p).data.toList = carry.data.toList.take p := by
        rw [extract_list]; simp [L]
      have hex2 : (carry.extract p carry.size).data.toList = L carry p := by
        rw [extract_list]; apply List.take_of_length_le; simp [L]
      rw [hex]
      congr 1
      have := reader_eq need hneed fuel (carry.extract p carry.size) 0 0 bs eof
        (by have := pot_cut carry p bs eof (by omega) hge.2; omega) (by omega) (by simp) hneed heof
      rw [hex2] at this
      exact this
    · rw [if_neg hcut]
      have hfl : f < need - lines := by
        have := cutAfterR_le carry (need - lines) scan
        rw [hca'] at this; simp only [] at this; omega
      have hcn := cutAfterR_count carry (need - lines) scan hscan (by rw [hca']; exact hfl)
      rw [hca'] at hcn
      simp only [] at hcn
      have hcnt : carry.data.toList.count newline = lines + f := by
        rw [hlist, List.count_append, hcount]; simp [L] at hcn ⊢; omega
      have hnone : ∀ R : List UInt8, R.count newline < need → cutLines need R = none := fun R h => cutLines_none_of_count need R h
      by_cases heof' : eof = true
      · rw [if_pos heof']
        have hb : bs = [] := heof heof'
        subst hb
        simp only [flat, List.flatMap_nil, List.append_nil]
        by_cases hz : carry.data.toList = []
        · have : carry.size = 0 := by rw [size_eq_length, hz]; rfl
          rw [hz, sliceAt_nil]; simp [this]
        · have : 0 < carry.size := by
            rw [size_eq_length]; exact List.length_pos_iff.2 hz
          have hn := hnone carry.data.toList (by omega)
          rw [sliceAt_none _ _ hz hn, if_pos this]; rfl
      · rw [if_neg heof']
        have heof'' : eof = false := by simpa using heof'
        have hlen : (carry.data.toList.take carry.size) = carry.data.toList :=
          List.take_of_length_le (by rw [← size_eq_length]; omega)
        cases bs with
        | nil =>
          have := reader_eq need hneed fuel carry carry.size (lines + f) [] true
            (by subst heof''; unfold pot at hp ⊢; simp [total] at hp ⊢; omega) (by omega)
            (by rw [hlen, hcnt]) (by omega) (fun _ => rfl)
          simpa using this
        | cons blk rest =>
          have hs : (carry ++ blk).size = carry.size + blk.size := ByteArray.size_append
          have := reader_eq need hneed fuel (carry ++ blk) carry.size (lines + f) rest false
            (by subst heof''; unfold pot at hp ⊢; simp [total] at hp ⊢; omega)
            (by omega)
            (by rw [data_toList_append, List.take_append_of_le_length (by rw [← size_eq_length]; omega), hlen, hcnt])
            (by omega) (by simp)
          rw [data_toList_append, List.append_assoc] at this
          simpa [flat] using this

-- THE statement: the reader emits exactly the slices of the concatenated blocks (blocks nonempty, as `readBig` returns them)
theorem reader_correct (k : Nat) (hk : 0 < k) (bs : List ByteArray) :
    (readerGo (4 * k) (pot ByteArray.empty bs false + 1) ByteArray.empty 0 0 bs false).map (·.data.toList) =
      sliceAt (4 * k) (flat bs) := by
  have := reader_eq (4 * k) (by omega) (pot ByteArray.empty bs false + 1) ByteArray.empty 0 0 bs false
    (by omega) (by simp) (by simp) (by omega) (by simp)
  simpa using this

#print axioms reader_correct

end Spec.FQ
