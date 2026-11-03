import Proofs.Fastq

/-! # `trimRecord` composes: what the FASTQ glue's trimming guarantees

`Spec.trimRecord` (Spec/Fastq.lean, mirrored in Proofs/Fastq.lean) is the adapter cut, then `ReadTrim.trimRead`, then
`AdapterTrim.dropShort minLength`. The pieces are proved in `AdapterTrim` (`cut_*`, `dropShort_size`) and `ReadTrim`
(`trimRead_acgt`); this file proves what their composition gives, about the letters and the quality BYTES
(`trimBytes`); the quality String is `String.fromUTF8!` of those bytes.

* `trimRecord_window`: the output letters and qualities are the same window `[a, b)` of the input letters / qualities.
* `trimRecord_acgt`: every output letter is A, C, G or T.
* `trimRecord_size`: the output is empty or has at least `minLength` letters.
* `trimRecord_cut`: the window ends at or before the adapter cut `c`; when the cut fires (`c < |letters|`), the adapter
  matches at `c` and at no earlier position. -/

namespace Spec

/-- `trimRecord`'s letters and quality bytes, before the quality bytes become a String. -/
def trimBytes (letters qual : ByteArray) : ByteArray × ByteArray :=
  let (letters, qual) := AdapterTrim.cutTruSeq letters qual
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  AdapterTrim.dropShort minLength letters qual

theorem trimRecord_eq (record : FastqRecord) :
    trimRecord record = { record with letters := (trimBytes record.letters record.quality.toUTF8).1,
                                      quality := String.fromUTF8! (trimBytes record.letters record.quality.toUTF8).2 } := by
  unfold trimRecord trimBytes
  simp only []
  rfl

/-- the adapter cut's position (the setting used by the reader: TruSeq, 6, 1) -/
def cutAt (letters : ByteArray) : Nat := AdapterTrim.cutPos AdapterTrim.truSeq 6 1 letters

theorem extract_extract_ba (x : ByteArray) (i j k l : Nat) :
    (x.extract i j).extract k l = x.extract (i + k) (min (i + l) j) := by
  apply ByteArray.ext
  simp [Array.extract_extract]

/-- (a) + (d): both outputs are the window `[a, b)` of the inputs, and `b` is at most the adapter cut. -/
theorem trimBytes_window (letters qual : ByteArray) :
    ∃ a b, a ≤ b ∧ b ≤ cutAt letters ∧ cutAt letters ≤ letters.size ∧
      (trimBytes letters qual).1 = letters.extract a b ∧ (trimBytes letters qual).2 = qual.extract a b := by
  have hc : cutAt letters ≤ letters.size := AdapterTrim.cut_le _ _ _ _
  have hl1 : (AdapterTrim.cutTruSeq letters qual).1 = letters.extract 0 (cutAt letters) := rfl
  have hq1 : (AdapterTrim.cutTruSeq letters qual).2 = qual.extract 0 (cutAt letters) := rfl
  unfold trimBytes
  simp only [hl1, hq1]
  split
  · rename_i s e hse
    have h := ReadTrim.trimRead_def_acgt _ _ s e hse
    have hsz : (letters.extract 0 (cutAt letters)).size = cutAt letters := by
      rw [ByteArray.size_extract]; omega
    have hec : e ≤ cutAt letters := by omega
    have hdrop : ∀ (l q : ByteArray), AdapterTrim.dropShort minLength l q = (l, q) ∨
        AdapterTrim.dropShort minLength l q = (ByteArray.empty, ByteArray.empty) := by
      intro l q; unfold AdapterTrim.dropShort; split <;> simp
    have e1 : (letters.extract 0 (cutAt letters)).extract s e = letters.extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt letters) = e by omega]; simp
    have e2 : (qual.extract 0 (cutAt letters)).extract s e = qual.extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt letters) = e by omega]; simp
    rcases hdrop ((letters.extract 0 (cutAt letters)).extract s e) ((qual.extract 0 (cutAt letters)).extract s e) with h1 | h1
    · refine ⟨s, e, by omega, hec, hc, ?_, ?_⟩ <;> rw [h1] <;> simp [e1, e2]
    · refine ⟨0, 0, Nat.le_refl _, by omega, hc, ?_, ?_⟩ <;> rw [h1] <;> (apply ByteArray.ext; simp)
  · refine ⟨0, 0, Nat.le_refl _, by omega, hc, ?_, ?_⟩ <;>
      (unfold AdapterTrim.dropShort; split <;> (apply ByteArray.ext; simp))

/-- (b) every output letter is A, C, G or T. -/
theorem trimBytes_acgt (letters qual : ByteArray) :
    ∀ x ∈ (trimBytes letters qual).1.data, ReadTrim.isACGT x = true := by
  have hl1 : (AdapterTrim.cutTruSeq letters qual).1 = letters.extract 0 (cutAt letters) := rfl
  have hq1 : (AdapterTrim.cutTruSeq letters qual).2 = qual.extract 0 (cutAt letters) := rfl
  unfold trimBytes
  simp only [hl1, hq1]
  split
  · rename_i s e hse
    have h := ReadTrim.trimRead_def_acgt _ _ s e hse
    intro x hx
    have hx' : x ∈ ((letters.extract 0 (cutAt letters)).extract s e).data := by
      unfold AdapterTrim.dropShort at hx
      split at hx
      · simp at hx
      · exact hx
    rw [ByteArray.data_extract, Array.mem_extract_iff_getElem] at hx'
    obtain ⟨k, hk, rfl⟩ := hx'
    have hlt : s + k < (letters.extract 0 (cutAt letters)).size := by simp at hk; omega
    have := h.2.2 (s + k) (by omega) (by omega)
    have e : (letters.extract 0 (cutAt letters))[s + k]! = (letters.extract 0 (cutAt letters))[s + k] :=
      getElem!_pos (letters.extract 0 (cutAt letters)) (s + k) hlt
    rw [e] at this
    exact this
  · intro x hx
    unfold AdapterTrim.dropShort at hx
    split at hx <;> simp at hx

/-- (c) the output is empty or has at least `minLength` letters. -/
theorem trimBytes_size (letters qual : ByteArray) :
    (trimBytes letters qual).1.size = 0 ∨ minLength ≤ (trimBytes letters qual).1.size :=
  AdapterTrim.dropShort_size _ _ _

/-- (d) the cut: if it fires at `c`, the adapter matches at `c` and at no earlier position. -/
theorem cutAt_spec (letters : ByteArray) :
    (cutAt letters < letters.size → AdapterTrim.matchesAt AdapterTrim.truSeq 6 1 letters (cutAt letters) = true) ∧
    ∀ j, j < cutAt letters → AdapterTrim.matchesAt AdapterTrim.truSeq 6 1 letters j = false :=
  ⟨AdapterTrim.cut_matches _ _ _ _, AdapterTrim.cut_first _ _ _ _⟩

/-- The quality String of `trimRecord` has the window's bytes, when they are valid UTF-8
(they are, for ASCII qualities, which `Spec.readFastqRecord` checks in the patch of audit/medium-fixes only). -/
theorem fromUTF8!_toUTF8 (b : ByteArray) (h : b.IsValidUTF8) : (String.fromUTF8! b).toUTF8 = b := by
  unfold String.fromUTF8!
  rw [dif_pos h]
  simp [String.fromUTF8]

theorem trimRecord_quality_bytes (record : FastqRecord)
    (h : (trimBytes record.letters record.quality.toUTF8).2.IsValidUTF8) :
    (trimRecord record).quality.toUTF8 = (trimBytes record.letters record.quality.toUTF8).2 := by
  rw [trimRecord_eq]
  generalize trimBytes record.letters record.quality.toUTF8 = p at h ⊢
  exact fromUTF8!_toUTF8 p.2 h

/-- **`trimRecord`, stated on the record** (a)-(d): with `cutAt` the adapter cut of the input letters,
the output letters are the window `[a, b)` of the input letters, the output quality bytes (before `String.fromUTF8!`)
the same window of the input quality bytes, `b ≤ cutAt`, every output letter is A/C/G/T, and the output has no
letters or at least `minLength`. -/
theorem trimRecord_correct (record : FastqRecord) :
    ∃ a b, a ≤ b ∧ b ≤ cutAt record.letters ∧ cutAt record.letters ≤ record.letters.size ∧
      (trimRecord record).letters = record.letters.extract a b ∧
      (trimBytes record.letters record.quality.toUTF8).2 = record.quality.toUTF8.extract a b ∧
      (∀ x ∈ (trimRecord record).letters.data, ReadTrim.isACGT x = true) ∧
      ((trimRecord record).letters.size = 0 ∨ minLength ≤ (trimRecord record).letters.size) := by
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := trimBytes_window record.letters record.quality.toUTF8
  have hl : (trimRecord record).letters = (trimBytes record.letters record.quality.toUTF8).1 := by
    rw [trimRecord_eq]
  refine ⟨a, b, h1, h2, h3, ?_, h5, ?_, ?_⟩
  · rw [hl, h4]
  · rw [hl]; exact trimBytes_acgt _ _
  · rw [hl]; exact trimBytes_size _ _

end Spec

#print axioms Spec.trimRecord_correct

#print axioms Spec.trimBytes_window
#print axioms Spec.trimBytes_acgt
#print axioms Spec.trimBytes_size
#print axioms Spec.cutAt_spec
#print axioms Spec.trimRecord_quality_bytes
