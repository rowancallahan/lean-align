import Proofs.Fastq
import TrimBytes

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

/-- The byte-list trimmer (`TrimBytes.trimSQ`, for the byte-level FASTQ spec) runs the same three steps. -/
theorem trimBytes_eq_trimBA (letters qual : ByteArray) : trimBytes letters qual = TrimBytes.trimBA minLength letters qual := rfl

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

theorem ascii_single (x : UInt8) (h : x < 128) :
    [Char.ofNat x.toNat].utf8Encode = ByteArray.mk #[x] := by
  have hx : x.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h
  have hvalid : x.toNat.isValidChar := by unfold Nat.isValidChar; omega
  have hv : (Char.ofNat x.toNat).val.toNat = x.toNat := by
    rw [Char.ofNat, dite_cond_eq_true (eq_true hvalid)]
    exact UInt32.toNat_ofNatLT
  rw [List.utf8Encode_singleton]
  unfold String.utf8EncodeChar
  simp only [hv, if_pos (show x.toNat ≤ 127 by omega), UInt8.ofNat_toNat]
  rfl

theorem ascii_encode : ∀ (l : List UInt8), (∀ x ∈ l, x < 128) →
    (l.map fun x => Char.ofNat x.toNat).utf8Encode = ByteArray.mk l.toArray
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.utf8Encode_cons, ascii_single x (h x (by simp)),
      ascii_encode l (fun y hy => h y (by simp [hy]))]
    apply ByteArray.ext
    simp [ByteArray.data_append]

theorem ascii_valid (b : ByteArray) (h : ∀ x ∈ b.data, x < 128) : b.IsValidUTF8 := by
  refine .intro (b.data.toList.map fun x => Char.ofNat x.toNat) ?_
  rw [ascii_encode _ (fun x hx => h x (by simpa using hx))]

theorem nat_all_true : ∀ (n : Nat) (f : (i : Nat) → i < n → Bool), Nat.all n f = true →
    ∀ i (h : i < n), f i h = true
  | 0, _, _, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, f, hall, i, h => by
    rw [Nat.all_succ] at hall
    simp only [Bool.and_eq_true] at hall
    by_cases hi : i = n
    · subst hi; exact hall.2
    · exact nat_all_true n _ hall.1 i (by omega)

theorem allBytes_mem (p : UInt8 → Bool) (bytes : ByteArray) (h : allBytes p bytes = true) :
    ∀ x ∈ bytes.data, p x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have := nat_all_true _ _ h i hi
  have e : bytes[i]! = bytes[i] := getElem!_pos bytes i hi
  simp only [e] at this
  exact this

theorem extract_mem (b : ByteArray) (i j : Nat) : ∀ x ∈ (b.extract i j).data, x ∈ b.data := by
  intro x hx
  rw [ByteArray.data_extract] at hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.mp hx
  exact Array.getElem_mem _

/-- The reader's check discharges the UTF-8 hypothesis: for every record `parseRecord` returns (the reader
returns exactly these), the trimmed quality bytes are valid UTF-8 and the quality String of `trimRecord` is
exactly those bytes. -/
theorem parseRecord_trim_quality {header letters plus quality : ByteArray} {record : FastqRecord}
    (h : parseRecord header letters plus quality = .ok record) :
    (trimBytes record.letters record.quality.toUTF8).2.IsValidUTF8 ∧
    (trimRecord record).quality.toUTF8 = (trimBytes record.letters record.quality.toUTF8).2 := by
  have hq : allBytes (fun b => 33 ≤ b && b ≤ 126) quality = true ∧ record.quality = String.fromUTF8! quality := by
    unfold parseRecord at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    rename_i _ _ _ h4
    simp only [Bool.not_eq_true', Bool.not_eq_false'] at h4
    cases h
    exact ⟨by simpa using h4, rfl⟩
  obtain ⟨hall, hrec⟩ := hq
  have hqa : ∀ x ∈ quality.data, x < 128 := by
    intro x hx
    have := allBytes_mem _ _ hall x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact UInt8.lt_iff_toNat_lt.mpr (by have := this.2; simp [UInt8.le_iff_toNat_le] at this; show x.toNat < 128; omega)
  have hvalid : quality.IsValidUTF8 := ascii_valid quality hqa
  have hbytes : record.quality.toUTF8 = quality := by rw [hrec]; exact fromUTF8!_toUTF8 quality hvalid
  obtain ⟨a, b, -, -, -, -, h5⟩ := trimBytes_window record.letters record.quality.toUTF8
  have hv : (trimBytes record.letters record.quality.toUTF8).2.IsValidUTF8 := by
    apply ascii_valid
    intro x hx
    rw [h5, hbytes] at hx
    exact hqa x (extract_mem _ _ _ x hx)
  exact ⟨hv, trimRecord_quality_bytes record hv⟩

/-! ## Trimming a chunk in parallel -/

theorem trimChunk_prefix (chunk : Array (FastqRecord × FastqRecord)) (size : Nat)
    (f : FastqRecord × FastqRecord → FastqRecord × FastqRecord) (m : Nat) :
    ((List.range m).map fun part => Task.spawn fun _ => (chunk.extract (part * size) ((part + 1) * size)).map f).foldl
      (fun out task => out ++ task.get) #[] = (chunk.extract 0 (m * size)).map f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    change _ ++ Array.map f (chunk.extract (m * size) ((m + 1) * size)) = _
    rw [← Array.map_append, Array.extract_append_extract]
    congr 2
    rw [Nat.succ_mul]; omega

/-- `trimChunk` is `trimRecord` on both mates of every pair, in order, however many parts it uses. -/
theorem trimChunk_eq (chunk : Array (FastqRecord × FastqRecord)) (parts : Nat) (hparts : 0 < parts) :
    trimChunk chunk parts = chunk.map fun (record1, record2) => (trimRecord record1, trimRecord record2) := by
  unfold trimChunk
  simp only []
  rw [trimChunk_prefix]
  have h := Nat.lt_div_mul_add (a := chunk.size + parts - 1) hparts
  generalize (chunk.size + parts - 1) / parts = q at h ⊢
  rw [Array.extract_eq_self_of_le (by rw [Nat.mul_comm]; omega)]

end Spec

#print axioms Spec.trimRecord_correct
#print axioms Spec.parseRecord_trim_quality

#print axioms Spec.trimBytes_window
#print axioms Spec.trimBytes_acgt
#print axioms Spec.trimBytes_size
#print axioms Spec.cutAt_spec
#print axioms Spec.trimRecord_quality_bytes
#print axioms Spec.trimChunk_eq
#print axioms Spec.trimBytes_eq_trimBA
