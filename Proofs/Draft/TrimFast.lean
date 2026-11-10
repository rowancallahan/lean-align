import Proofs.Draft.Trim

/-! # The spec's cut and trim are the fast byte code

* `cut_eq`: `Spec.Trim.cut` is `AdapterTrim.cutTruSeq` (whose compiled code is the machine-word adapter scan):
  the spec's first position where the adapter (≤ 1 mismatch) or a prefix of it (≥ 6 letters, exact) starts is
  `AdapterTrim.cutPos truSeq 6 1`.
* `trimB_eq`: `TrimCore.trimB` (cut, best window, minimum length, all on `ByteArray`s) gives the letters and qualities
  of `trim (cut r)`, so the spec's `List` code never has to run. -/

namespace Spec.Trim
open Spec.FQ

/-! ## Lists -/

theorem zip_filter_length : ∀ (a r : List UInt8),
    ((a.zip r).filter fun (x : UInt8 × UInt8) => x.1 != x.2).length =
      ((List.range (min a.length r.length)).filter fun j => r[j]! != a[j]!).length
  | [], r => by simp
  | x :: a, [] => by simp
  | x :: a, y :: r => by
    have ih := zip_filter_length a r
    rw [List.zip_cons_cons, List.length_cons, List.length_cons,
      show min (a.length + 1) (r.length + 1) = min a.length r.length + 1 by omega, List.range_succ_eq_map,
      List.filter_cons, List.filter_cons]
    by_cases h : x = y
    · subst h; simp [ih, List.filter_map, Function.comp_def]
    · simp [h, Ne.symm h, ih, List.filter_map, Function.comp_def]

theorem zip_filter_zero : ∀ (a r : List UInt8), r.length ≤ a.length →
    (((a.zip r).filter fun (x : UInt8 × UInt8) => x.1 != x.2).length = 0 ↔ r = a.take r.length)
  | _, [], _ => by simp
  | [], y :: r, h => by simp at h
  | x :: a, y :: r, h => by
    simp only [List.length_cons] at h
    rw [List.zip_cons_cons, List.filter_cons]
    by_cases e : x = y
    · subst e; simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.length_cons, List.take_succ_cons]
      rw [zip_filter_zero a r (by omega)]; simp
    · have : (x != y) = true := by simp [e]
      simp only [this, if_true, List.length_cons, List.take_succ_cons]
      simp only [Nat.add_one_ne_zero, false_iff]
      intro h2; injection h2 with h3; exact e h3.symm

theorem find_range (p : Nat → Bool) (n c : Nat) (hc : c ≤ n) (h1 : ∀ j, j < c → p j = false)
    (h2 : c < n → p c = true) : ((List.range n).find? p).getD n = c := by
  by_cases hcn : c < n
  · have : (List.range n).find? p = some c := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨h2 hcn, c, by simpa using hcn, by simp, fun j hj => ?_⟩
      simp only [List.getElem_range]; rw [h1 j hj]; simp
    rw [this]; rfl
  · have : (List.range n).find? p = none := by
      rw [List.find?_eq_none]
      intro x hx; simp only [List.mem_range] at hx; rw [h1 x (by omega)]; simp
    rw [this]; simp; omega

/-! ## The adapter test -/

/-- The spec's adapter test at `i` (the `adapterAt` of `cut`). -/
def adapterAtS (s : List UInt8) (i : Nat) : Bool :=
  let rest := s.extract i
  match decide (adapter.length ≤ rest.length) with
  | true =>
    ((adapter.zip rest).filter fun (a, b) => a != b).length ≤ 1
  | false =>
    6 ≤ rest.length && rest == adapter.extract 0 rest.length

theorem cut_eq_find (r : FQ.Read) :
    cut r = let c := ((List.range r.sequence.length).find? (adapterAtS r.sequence)).getD r.sequence.length
      ⟨r.name, r.sequence.extract 0 c, r.quality.extract 0 c⟩ := rfl

theorem adapter_eq : adapter = AdapterTrim.truSeq.data.toList := by decide +kernel

theorem adapter_length : adapter.length = 13 := by decide +kernel

theorem bget! (b : ByteArray) (k : Nat) : b[k]! = b.data.toList[k]! := by
  have hs : b.size = b.data.toList.length := by rw [Array.length_toList]; rfl
  by_cases h : k < b.size
  · rw [getElem!_pos b k h, getElem!_pos _ k (by rw [← hs]; exact h)]
    try rfl
    try simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg b k h, getElem!_neg _ k (by rw [← hs]; exact h)]
    try rfl

theorem ba_get! (l : List UInt8) (k : Nat) : (⟨l.toArray⟩ : ByteArray)[k]! = l[k]! := by
  rw [bget!]
  try rfl

theorem truSeq_get! (j : Nat) : AdapterTrim.truSeq[j]! = adapter[j]! := by
  rw [adapter_eq, bget!]

theorem drop_get! (s : List UInt8) (i j : Nat) : (s.drop i)[j]! = s[i + j]! := by
  by_cases h : i + j < s.length
  · rw [getElem!_pos _ j (by simp; omega), getElem!_pos s (i + j) h, List.getElem_drop]
  · rw [getElem!_neg _ j (by simp; omega), getElem!_neg s (i + j) h]

/-- The spec's adapter test is `AdapterTrim.matchesAt truSeq 6 1` at every position of the read. -/
theorem adapterAtS_eq (s : List UInt8) (i : Nat) (hi : i < s.length) :
    adapterAtS s i = AdapterTrim.matchesAt AdapterTrim.truSeq 6 1 ⟨s.toArray⟩ i := by
  have hts : AdapterTrim.truSeq.size = 13 := by decide
  have hcount : ∀ len, len ≤ 13 → len ≤ s.length - i →
      AdapterTrim.mismatches AdapterTrim.truSeq ⟨s.toArray⟩ i len =
        ((List.range len).filter fun j => (s.drop i)[j]! != adapter[j]!).length := by
    intro len h1 h2
    unfold AdapterTrim.mismatches
    congr 2; funext j
    rw [ba_get!, truSeq_get!, drop_get!]
  have hex : s.extract i = s.drop i := by simp [List.extract, List.take_of_length_le]
  have hd : (s.drop i).length = s.length - i := by simp
  have hadx : adapter.extract 0 (s.length - i) = adapter.take (s.length - i) := by simp [List.extract]
  unfold adapterAtS AdapterTrim.matchesAt
  simp only [hex, hd, hadx, hts, ba_size]
  by_cases hbig : 13 ≤ s.length - i
  · have h1 : decide (adapter.length ≤ s.length - i) = true := by simp [adapter_length]; omega
    simp only [h1]
    rw [Nat.min_eq_left hbig, if_pos rfl, hcount 13 (Nat.le_refl _) hbig]
    have hz := zip_filter_length adapter (s.drop i)
    rw [adapter_length, hd, Nat.min_eq_left hbig] at hz
    rw [show (fun (x : UInt8 × UInt8) => match x with | (a, b) => a != b) = (fun x => x.1 != x.2) from rfl, hz]
    simp [hi]
  · have h1 : decide (adapter.length ≤ s.length - i) = false := by simp [adapter_length]; omega
    simp only [h1]
    rw [Nat.min_eq_right (by omega), if_neg (by omega), hcount _ (by omega) (Nat.le_refl _)]
    have hz := zip_filter_zero adapter (s.drop i) (by rw [hd, adapter_length]; omega)
    have hz2 := zip_filter_length adapter (s.drop i)
    rw [adapter_length, hd, Nat.min_eq_right (by omega)] at hz2
    rw [hz2, hd] at hz
    by_cases h6 : 6 ≤ s.length - i
    · simp only [h6, hi, decide_true, Bool.true_and, Nat.le_zero]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hz]
    · simp [h6]

/-! ## `cut` is `cutTruSeq` -/

theorem cutPos_le (s : List UInt8) : AdapterTrim.cutPos AdapterTrim.truSeq 6 1 ⟨s.toArray⟩ ≤ s.length := by
  have := AdapterTrim.cut_le AdapterTrim.truSeq 6 1 ⟨s.toArray⟩; rwa [ba_size] at this

theorem cut_pos (s : List UInt8) :
    ((List.range s.length).find? (adapterAtS s)).getD s.length = AdapterTrim.cutPos AdapterTrim.truSeq 6 1 ⟨s.toArray⟩ := by
  apply find_range _ _ _ (cutPos_le s)
  · intro j hj
    rw [adapterAtS_eq s j (by have := cutPos_le s; omega)]
    exact AdapterTrim.cut_first _ _ _ _ j hj
  · intro hc
    rw [adapterAtS_eq s _ hc]
    exact AdapterTrim.cut_matches _ _ _ _ (by rw [ba_size]; exact hc)

theorem ba_extract_list (l : List UInt8) (a b : Nat) :
    ((⟨l.toArray⟩ : ByteArray).extract a b).data.toList = l.extract a b := by
  simp [ByteArray.data_extract, List.extract]

/-- **The spec's cut is the fast adapter cut** (`AdapterTrim.cutTruSeq`). -/
theorem cut_eq (r : FQ.Read) :
    cut r = ⟨r.name, (AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).1.data.toList,
      (AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).2.data.toList⟩ := by
  rw [cut_eq_find, cut_pos]
  show _ = (⟨r.name, ((⟨r.sequence.toArray⟩ : ByteArray).extract 0 (AdapterTrim.cutPos AdapterTrim.truSeq 6 1 ⟨r.sequence.toArray⟩)).data.toList,
    ((⟨r.quality.toArray⟩ : ByteArray).extract 0 (AdapterTrim.cutPos AdapterTrim.truSeq 6 1 ⟨r.sequence.toArray⟩)).data.toList⟩ : FQ.Read)
  rw [ba_extract_list, ba_extract_list]

/-- `cut` as the compiled code runs it: the machine-word adapter scan on the read's bytes (`cut_eq`). -/
def cutF (r : FQ.Read) : FQ.Read :=
  let c := AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
  ⟨r.name, c.1.data.toList, c.2.data.toList⟩

@[csimp] theorem cut_eq_cutF : @cut = @cutF := by
  funext r; exact cut_eq r

theorem toArray_ba (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  apply ByteArray.ext; simp

/-- **`trimB` is the spec's `trim ∘ cut`**: on a read's bytes it gives the letters and qualities of
`trim (cut r)`. -/
theorem trimB_eq (r : FQ.Read) :
    let t := TrimCore.trimB ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
    (t.1.data.toList, t.2.data.toList) = ((trim (cut r)).sequence, (trim (cut r)).quality) := by
  rw [cut_eq]
  unfold trim TrimCore.trimB
  simp only [toArray_ba]
  rfl

end Spec.Trim

#print axioms Spec.Trim.cut_eq
#print axioms Spec.Trim.cut_eq_cutF
#print axioms Spec.Trim.trimB_eq
