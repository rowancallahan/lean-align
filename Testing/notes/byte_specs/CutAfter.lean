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

end Spec.FQ
