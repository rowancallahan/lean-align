import ReadWindowTrimmer
import ParStream

/-!
# Codec `trimRead`: the proved read-window trimmer on FASTQ bytes

Per base: Phred quality `q` (FASTQ byte − 33, at most 93) for A/C/G/T, scored
`q − Q` for a neutral quality `Q ≤ 93` (`trimReadQ Q`; below `Q` costs); any other
letter (N) scores `−1 000 000`.  `trimRead` is `trimReadQ defQ` (defQ = 25).  The kept window is the best-scoring window of the frozen
contract (`get_best_window`, trimmer/ReadWindowTrimmer/Contract.lean), computed
by the packed trimmer (`getBestWindowPacked`).

    trimReadQ Q seq qual = get_best_window [] (scoresOf seq qual) (·.map (perBase Q))
      for every Q ≤ 93 and read with an A/C/G/T letter    (trimRead_eq_contract)
    trimReadQ Q seq qual = some (s, e) → e ≤ seq.size ∧ s < e ∧
      ∀ i, s ≤ i → i < e → isACGT seq[i]! = true          (trimRead_acgt)

Reads with no A/C/G/T or longer than 10 000 letters give `none`.

Chunked output: the texts of the chunks, in order, are the text of the whole
input mapped (`chunks_text`), however the input is cut.
-/

namespace ReadTrim

open ReadWindow

def isACGT (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

/-- Encoded per-base value: quality for A/C/G/T, −1 otherwise. -/
@[inline] def enc (b qc : UInt8) : Int := if isACGT b then ((min (qc.toNat - 33) 93 : Nat) : Int) else -1

@[inline] def perBase (Q : Nat) (v : Int) : Int := if v < 0 then -1000000 else v - Q

def scoresOf (seq qual : ByteArray) : List Int := (List.range seq.size).map fun i => enc seq[i]! qual[i]!

/-- The packed trimmer's fold over `scoresOf`, run on the bytes from the end
(no list; `winLoop_eq`). -/
def winLoop (Q : Nat) (seq qual : ByteArray) : Nat → PackedFoldState → PackedFoldState
  | 0, st => st
  | i + 1, st => winLoop Q seq qual i (packedFoldStep (perBase Q) (enc seq[i]! qual[i]!) st)

/-- `winLoop` with the state's fields as arguments (no state allocated per base; `wl_eq`). -/
def wl (Q : Nat) (seq qual : ByteArray) : Nat → Nat → Bool → Nat → Int → Nat → Nat → Int → PackedFoldState
  | 0, ns, hr, pl, ps, bs, be, bsc => ⟨ns, hr, pl, ps, bs, be, bsc⟩
  | i + 1, ns, hr, pl, ps, bs, be, bsc =>
    let cs := ns - 1
    let f := perBase Q (enc seq[i]! qual[i]!)
    if hr then
      if 0 < ps then
        if bsc ≤ f + ps then wl Q seq qual i cs true (pl + 1) (f + ps) cs (cs + (pl + 1)) (f + ps)
        else wl Q seq qual i cs true (pl + 1) (f + ps) bs be bsc
      else if bsc ≤ f then wl Q seq qual i cs true 1 f cs (cs + 1) f
      else wl Q seq qual i cs true 1 f bs be bsc
    else wl Q seq qual i cs true 1 f cs (cs + 1) f

/-- The kept window `[s, e)`, or `none` (nothing worth keeping: the best window
starts with a non-A/C/G/T letter only when the read has no A/C/G/T at all). -/
def trimReadQ (Q : Nat) (seq qual : ByteArray) : Option (Nat × Nat) :=
  if seq.size ≤ 10000 then
    match (wl Q seq qual seq.size seq.size false 0 0 0 0 0).result.map
        (fun r => (r.bestStart, r.bestEnd)) with
    | some (s, e) => if isACGT seq[s]! then some (s, e) else none
    | none => none
  else none

/-! ## Proof -/

theorem enc_le (b qc : UInt8) : enc b qc ≤ 93 := by
  unfold enc; split <;> omega

theorem enc_nonneg (b qc : UInt8) : 0 ≤ enc b qc ↔ isACGT b = true := by
  unfold enc; split <;> simp_all

theorem perBase_neg (Q : Nat) (v : Int) (h : v < 0) : perBase Q v = -1000000 := by simp [perBase, h]
theorem perBase_pos (Q : Nat) (v : Int) (h : ¬ v < 0) : perBase Q v = v - Q := by simp [perBase, h]

theorem sum_le (Q : Nat) (hQ : Q ≤ 93) (l : List Int) (h : ∀ x ∈ l, x ≤ 93) :
    (l.map (perBase Q)).sum ≤ (93 - Q : Int) * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    rw [show ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 by omega, Int.mul_add, Int.mul_one]
    by_cases hx0 : x < 0
    · rw [perBase_neg Q x hx0]; omega
    · rw [perBase_pos Q x hx0]; omega

theorem sum_le_neg (Q : Nat) (hQ : Q ≤ 93) (l : List Int) (h : ∀ x ∈ l, x ≤ 93) (hn : ∃ x ∈ l, x < 0) :
    (l.map (perBase Q)).sum ≤ -1000000 + (93 - Q : Int) * l.length := by
  induction l with
  | nil => simp at hn
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [show ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 by omega, Int.mul_add, Int.mul_one]
    have hx := h x List.mem_cons_self
    have h2 := sum_le Q hQ xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx0 : x < 0
    · rw [perBase_neg Q x hx0]; omega
    · obtain ⟨y, hy, hy0⟩ := hn
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨y, hy, hy0⟩
        rw [perBase_pos Q x hx0]; omega

theorem winLoop_eq (Q : Nat) (seq qual : ByteArray) (k : Nat) (st : PackedFoldState) :
    winLoop Q seq qual k st =
      ((List.range k).map (fun i => enc seq[i]! qual[i]!)).foldr (packedFoldStep (perBase Q)) st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => rw [winLoop, ih, List.range_succ]; simp

theorem wl_eq (Q : Nat) (seq qual : ByteArray) (i ns : Nat) (hr : Bool) (pl : Nat) (ps : Int) (bs be : Nat)
    (bsc : Int) : wl Q seq qual i ns hr pl ps bs be bsc = winLoop Q seq qual i ⟨ns, hr, pl, ps, bs, be, bsc⟩ := by
  induction i generalizing ns hr pl ps bs be bsc with
  | zero => rfl
  | succ i ih =>
    simp only [wl, winLoop, packedFoldStep]
    cases hr <;> simp only [Bool.false_eq_true, if_false, if_true] <;> (try split) <;> (try split) <;> rw [ih]

theorem winLoop_packed (Q : Nat) (seq qual : ByteArray) :
    (winLoop Q seq qual seq.size (initialPackedFoldState seq.size)).result.map (fun r => (r.bestStart, r.bestEnd)) =
      getBestWindowPacked (scoresOf seq qual) (perBase Q) := by
  rw [winLoop_eq]; unfold getBestWindowPacked scoresOf; simp

/-- The contract's best window, when the read has an A/C/G/T letter: inside the
read, non-empty, A/C/G/T only. -/
theorem best_acgt (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (s e : Nat) (hsz : seq.size ≤ 10000) (j : Nat)
    (hj : j < seq.size) (hjA : isACGT seq[j]! = true)
    (ht : get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true := by
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
    -- the single A/C/G/T base scores ≥ −Q ≥ −93
    have h1 : (List.take (j + 1 - j) (List.drop j (scoresOf seq qual))) = [enc seq[j]! qual[j]!] := by
      rw [show j + 1 - j = 1 by omega, List.take_one, List.head?_drop, List.getElem?_eq_getElem (by omega),
        hget j (by omega)]
      rfl
    rw [h1] at hmax
    have h0 := (enc_nonneg seq[j]! qual[j]!).2 hjA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hmax
    -- the best window holds the non-A/C/G/T base: ≤ −1 000 000 + (93 − Q) · 10 000
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
    have := sum_le_neg Q hQ w hw93 hneg
    have hwl' : (w.length : Int) ≤ 10000 := by omega
    have hprod : (93 - Q : Int) * w.length ≤ 93 * 10000 :=
      Int.mul_le_mul (by omega) hwl' (by omega) (by omega)
    rw [perBase_pos Q _ (by omega)] at hmax
    omega

theorem trimRead_packed (Q : Nat) (seq qual : ByteArray) (s e : Nat) (ht : trimReadQ Q seq qual = some (s, e)) :
    seq.size ≤ 10000 ∧ isACGT seq[s]! = true ∧
      get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) = some (s, e) := by
  unfold trimReadQ at ht
  split at ht
  · next hsz =>
    split at ht
    · next s' e' hw =>
      split at ht
      · next hA =>
        cases ht
        rw [wl_eq, ← initialPackedFoldState, winLoop_packed, getBestWindowPacked_equals_frozen_get_best_window []] at hw
        exact ⟨hsz, hA, hw⟩
      · cases ht
    · cases ht
  · cases ht

/-- **The kept window is inside the read, non-empty, and A/C/G/T only** (any `Q ≤ 93`). -/
theorem trimRead_acgt (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (s e : Nat)
    (ht : trimReadQ Q seq qual = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true := by
  obtain ⟨hsz, hA, hw⟩ := trimRead_packed Q seq qual s e ht
  have hv := get_best_window_returns_a_valid_window [] _ _ _ hw
  simp only [scoresOf, List.length_map, List.length_range] at hv
  exact best_acgt Q hQ seq qual s e hsz s (by omega) hA hw

/-- **The trimmer is the frozen contract** for every neutral quality `Q ≤ 93` and
every read with an A/C/G/T letter (at most 10 000 letters). -/
theorem trimRead_eq_contract (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (h : seq.size ≤ 10000) (j : Nat)
    (hj : j < seq.size) (hjA : isACGT seq[j]! = true) :
    trimReadQ Q seq qual = get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) := by
  have hc := (winLoop_packed Q seq qual).trans (getBestWindowPacked_equals_frozen_get_best_window [] _ _)
  rw [initialPackedFoldState, ← wl_eq] at hc
  unfold trimReadQ
  rw [if_pos h, hc]
  cases hw : get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) with
  | none => rfl
  | some w =>
    obtain ⟨s, e⟩ := w
    have := best_acgt Q hQ seq qual s e h j hj hjA hw
    simp [this.2.2 s (Nat.le_refl _) this.2.1]

/-- The default neutral quality. -/
def defQ : Nat := 25

/-- The trimmer at the default neutral quality. -/
def trimRead (seq qual : ByteArray) : Option (Nat × Nat) := trimReadQ defQ seq qual

theorem trimRead_def_eq_contract (seq qual : ByteArray) (h : seq.size ≤ 10000) (j : Nat) (hj : j < seq.size)
    (hjA : isACGT seq[j]! = true) :
    trimRead seq qual = get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase defQ)) :=
  trimRead_eq_contract defQ (by decide) seq qual h j hj hjA

theorem trimRead_def_acgt (seq qual : ByteArray) (s e : Nat) (ht : trimRead seq qual = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true :=
  trimRead_acgt defQ (by decide) seq qual s e ht

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
#print axioms ReadTrim.trimRead_def_eq_contract
#print axioms ReadTrim.trimRead_def_acgt
#print axioms ParMap.chunks_text
#print axioms ParMap.stages_text
