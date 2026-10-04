import ReadWindowTrimmer
import ParStream

/-!
# Codec `trimRead`: the proved read-window trimmer on FASTQ bytes

Per base: Phred quality `q` (FASTQ byte − 33, at most 93) for A/C/G/T, scored
`q − 20` (Q20 is neutral, below it costs); any other letter (N) scores
`−1 000 000`.  The kept window is the best-scoring window of the frozen
contract (`get_best_window`, trimmer/ReadWindowTrimmer/Contract.lean), computed
by the packed trimmer (`getBestWindowPacked`).

    trimRead seq qual = get_best_window [] (scoresOf seq qual) (·.map perBase)
                                                          (trimRead_eq_contract)
    trimRead seq qual = some (s, e) → e ≤ seq.size ∧ s < e ∧
      ∀ i, s ≤ i → i < e → isACGT seq[i]! = true          (trimRead_acgt)

Reads with no A/C/G/T or longer than 10 000 letters are not trimmed (`none`).

Chunked output: the texts of the chunks, in order, are the text of the whole
input mapped (`chunks_text`), however the input is cut.
-/

namespace ReadTrim

open ReadWindow

def isACGT (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

/-- Encoded per-base value: quality for A/C/G/T, −1 otherwise. -/
@[inline] def enc (b qc : UInt8) : Int := if isACGT b then ((min (qc.toNat - 33) 93 : Nat) : Int) else -1

@[inline] def perBase (v : Int) : Int := if v < 0 then -1000000 else v - 20

def scoresOf (seq qual : ByteArray) : List Int := (List.range seq.size).map fun i => enc seq[i]! qual[i]!

/-- The kept window `[s, e)`, or `none` (nothing worth keeping). -/
def trimRead (seq qual : ByteArray) : Option (Nat × Nat) :=
  if seq.size ≤ 10000 && (List.range seq.size).any (fun i => isACGT seq[i]!) then
    getBestWindowPacked (scoresOf seq qual) perBase
  else none

/-! ## Proof -/

theorem enc_le (b qc : UInt8) : enc b qc ≤ 93 := by
  unfold enc; split <;> omega

theorem enc_nonneg (b qc : UInt8) : 0 ≤ enc b qc ↔ isACGT b = true := by
  unfold enc; split <;> simp_all

theorem perBase_neg (v : Int) (h : v < 0) : perBase v = -1000000 := by simp [perBase, h]
theorem perBase_pos (v : Int) (h : ¬ v < 0) : perBase v = v - 20 := by simp [perBase, h]

theorem sum_le (l : List Int) (h : ∀ x ∈ l, x ≤ 93) : (l.map perBase).sum ≤ 73 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    by_cases hx0 : x < 0
    · rw [perBase_neg x hx0]; omega
    · rw [perBase_pos x hx0]; omega

theorem sum_le_neg (l : List Int) (h : ∀ x ∈ l, x ≤ 93) (hn : ∃ x ∈ l, x < 0) :
    (l.map perBase).sum ≤ -1000000 + 73 * l.length := by
  induction l with
  | nil => simp at hn
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have h2 := sum_le xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx0 : x < 0
    · rw [perBase_neg x hx0]; omega
    · obtain ⟨y, hy, hy0⟩ := hn
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨y, hy, hy0⟩
        rw [perBase_pos x hx0]; omega

theorem trimRead_eq_contract (seq qual : ByteArray) (h : seq.size ≤ 10000)
    (ha : (List.range seq.size).any (fun i => isACGT seq[i]!) = true) :
    trimRead seq qual = get_best_window [] (scoresOf seq qual) (fun ws => ws.map perBase) := by
  unfold trimRead
  rw [if_pos (by simp [h, ha])]
  exact getBestWindowPacked_equals_frozen_get_best_window [] _ _

/-- **The kept window is inside the read, non-empty, and A/C/G/T only.** -/
theorem trimRead_acgt (seq qual : ByteArray) (s e : Nat) (ht : trimRead seq qual = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true := by
  unfold trimRead at ht
  split at ht
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at hc
    obtain ⟨hsz, j, hj, hjA⟩ := hc
    rw [getBestWindowPacked_equals_frozen_get_best_window []] at ht
    have hlen : (scoresOf seq qual).length = seq.size := by simp [scoresOf]
    have hget : ∀ i (hi : i < (scoresOf seq qual).length), (scoresOf seq qual)[i] = enc seq[i]! qual[i]! := by
      intro i hi; simp [scoresOf]
    have hv := get_best_window_returns_a_valid_window [] _ _ _ ht
    simp only at hv
    refine ⟨by omega, hv.1, fun i hsi hie => ?_⟩
    apply Classical.byContradiction; intro hnA
    have hmax := get_best_window_returns_a_maximum_score [] _ _ _ (j, j + 1) ht (by simp) (by simp; omega)
    unfold window_score at hmax
    simp only at hmax
    -- the single A/C/G/T base scores ≥ −20
    have h1 : (List.take (j + 1 - j) (List.drop j (scoresOf seq qual))) = [enc seq[j]! qual[j]!] := by
      rw [show j + 1 - j = 1 by omega, List.take_one, List.head?_drop, List.getElem?_eq_getElem (by omega),
        hget j (by omega)]
      rfl
    rw [h1] at hmax
    have h0 := (enc_nonneg seq[j]! qual[j]!).2 hjA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hmax
    -- the best window holds the non-A/C/G/T base: ≤ −1 000 000 + 73 · 10 000
    generalize hw : List.take (e - s) (List.drop s (scoresOf seq qual)) = w at hmax
    have hwl : w.length ≤ 10000 := by rw [← hw]; simp; omega
    have hw93 : ∀ x ∈ w, x ≤ 93 := by
      intro x hx
      rw [← hw] at hx
      have := List.mem_of_mem_take hx
      have := List.mem_of_mem_drop this
      simp only [scoresOf, List.mem_map] at this
      obtain ⟨k, -, rfl⟩ := this
      exact enc_le _ _
    have hneg : ∃ x ∈ w, x < 0 := by
      refine ⟨enc seq[i]! qual[i]!, ?_, ?_⟩
      · rw [← hw, List.mem_iff_getElem]
        refine ⟨i - s, by simp; omega, ?_⟩
        simp only [List.getElem_take, List.getElem_drop]
        rw [hget _ (by omega), show s + (i - s) = i by omega]
      · apply Classical.byContradiction; intro h0'
        exact hnA ((enc_nonneg seq[i]! qual[i]!).1 (by omega))
    have := sum_le_neg w hw93 hneg
    rw [perBase_pos _ (by omega)] at hmax
    omega
  · cases ht

end ReadTrim

namespace ParMap

/-- **Chunked output is the whole output**: for any cut of the input into
chunks, the chunks' texts in order are the text of the whole input mapped. -/
theorem chunks_text {α β : Type} (f : α → β) (fmt : β → String) (cs : List (Array α)) :
    String.join (cs.map fun c => formatAll fmt (c.map f)) = formatAll fmt ((cs.foldl (· ++ ·) #[]).map f) := by
  suffices h : ∀ acc, formatAll fmt (acc.map f) ++ String.join (cs.map fun c => formatAll fmt (c.map f)) =
      formatAll fmt ((cs.foldl (· ++ ·) acc).map f) by
    have := h #[]; simpa [formatAll] using this
  induction cs with
  | nil => intro acc; simp
  | cons c cs ih =>
    intro acc
    rw [List.map_cons, String.join_cons, ← String.append_assoc, ← formatAll_append, ← Array.map_append, ih]
    rfl

/-- Two stages (prep, then map) are their composition. -/
theorem stages_text {α β γ : Type} (p : α → β) (m : β → γ) (fmt : γ → String) (c : Array α) :
    formatAll fmt ((c.map p).map m) = formatAll fmt (c.map (m ∘ p)) := by
  rw [Array.map_map]

end ParMap

#print axioms ReadTrim.trimRead_eq_contract
#print axioms ReadTrim.trimRead_acgt
#print axioms ParMap.chunks_text
#print axioms ParMap.stages_text
