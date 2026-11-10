import Proofs.SamBytes

/-! # Trimming a read: what `trimRead` guarantees (and the QNAME rule on bytes)

`Spec.trimRead` (Spec/Sam.lean, mirrored in Proofs/Sam.lean) is `trimBytes` on the read's letters and quality: the
adapter cut, then `ReadTrim.trimRead`, then `AdapterTrim.dropShort minLength`. The pieces are proved in `AdapterTrim`
(`cut_*`, `dropShort_size`) and `ReadTrim` (`trimRead_acgt`); this file proves what their composition gives.

* `trimBytes_window`: the output letters and qualities are the same window `[a, b)` of the input letters / qualities.
* `trimBytes_acgt`: every output letter is A, C, G or T.
* `trimBytes_size`: the output is empty or has at least `minLength` letters.
* `cutAt_spec`: the window ends at or before the adapter cut `c`; when the cut fires (`c < |letters|`), the adapter
  matches at `c` and at no earlier position.
* `trimRead_correct`: the same, stated on the read (`FQ.Read`); `trimReadB_toRead`: the shim's `trimReadB` is
  `trimRead`; `parse_trim_quality`: every quality byte of a trimmed read that `FQ.parse` returned is in '!'..'~'.
* `trimRead_contract` (from `trimRead_best` / `trimRead_best_none`): for every read of ≤ 10 000 letters, the kept window is the frozen contract's `get_best_window` window of the read cut at the adapter
  (`keepWindow`); `trimRead_valid` / `parse_trim_valid`: a trimmed valid read (every read `FQ.parse` returns) is the
  read of a valid record.
* `trimChunk_eq`: trimming a chunk in parallel is `trimReadB` on both mates of every pair, in order. -/

namespace Spec

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

theorem fromUTF8!_toUTF8 (b : ByteArray) (h : b.IsValidUTF8) : (String.fromUTF8! b).toUTF8 = b := by
  unfold String.fromUTF8!
  rw [dif_pos h]
  simp [String.fromUTF8]

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

/-! ## Stated on the read -/

theorem toArray_ba (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  apply ByteArray.ext; simp

/-- the shim's trimming (on `ReadB`) is the spec's (on `FQ.Read`) -/
theorem trimReadB_toRead (r : ReadB) : (trimReadB r).toRead = trimRead r.toRead := by
  unfold trimReadB trimRead ReadB.toRead
  simp only [toArray_ba]

/-- `trimRead`'s quality is the quality bytes `trimBytes` gives -/
theorem trimRead_quality_bytes (r : FQ.Read) :
    (trimRead r).quality = (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).2.data.toList := rfl

/-- **`trimRead`, stated on the read** (a)-(d): with `cutAt` the adapter cut of the input letters, the output
letters are the window `[a, b)` of the input letters, the output qualities the same window of the input qualities,
`b ≤ cutAt`, every output letter is A/C/G/T, and the output has no letters or at least `minLength`. -/
theorem trimRead_correct (r : FQ.Read) :
    ∃ a b, a ≤ b ∧ b ≤ cutAt ⟨r.sequence.toArray⟩ ∧ cutAt ⟨r.sequence.toArray⟩ ≤ r.sequence.length ∧
      (trimRead r).sequence = (r.sequence.drop a).take (b - a) ∧
      (trimRead r).quality = (r.quality.drop a).take (b - a) ∧
      (∀ x ∈ (trimRead r).sequence, ReadTrim.isACGT x = true) ∧
      ((trimRead r).sequence = [] ∨ minLength ≤ (trimRead r).sequence.length) := by
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := trimBytes_window ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩
  have hl : (trimRead r).sequence = (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).1.data.toList := rfl
  refine ⟨a, b, h1, h2, (by have := h3; simp only [ByteArray.size, List.size_toArray] at this; exact this), ?_, ?_, ?_, ?_⟩
  · rw [hl, h4, ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take]
  · rw [trimRead_quality_bytes, h5, ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take]
  · rw [hl]; intro x hx; exact trimBytes_acgt _ _ x (by simpa using hx)
  · rw [hl]
    rcases trimBytes_size ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ with h | h
    · left; apply List.eq_nil_of_length_eq_zero; simpa using h
    · right; simpa using h

/-- For every read `FQ.parse` returns, the trimmed qualities are quality bytes ('!'..'~'). -/
theorem parse_trim_quality (bytes : List UInt8) (reads : List FQ.Read) (h : FQ.parse bytes = some reads) :
    ∀ r ∈ reads, ∀ x ∈ (trimRead r).quality, FQ.qualityByte x = true := by
  obtain ⟨records, hv, -, hr⟩ := FQ.parse_some bytes reads h
  intro r hr' x hx
  rw [← hr] at hr'
  obtain ⟨rec, hrec, rfl⟩ := List.mem_map.mp hr'
  obtain ⟨a, b, -, -, -, -, h5⟩ := trimBytes_window ⟨rec.sequence.toArray⟩ ⟨rec.quality.toArray⟩
  simp only [FQ.toRead] at hx
  rw [trimRead_quality_bytes, h5] at hx
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take] at hx
  exact (hv rec hrec).2.2.2.2.2.2.2.2.2.2.1 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-! ## The kept window is the frozen contract's best window; a trimmed valid read is valid -/

/-- the read's letters and qualities up to the adapter cut: what the quality trimmer sees -/
def preCut (r : FQ.Read) : ByteArray × ByteArray := AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩

/-- the read with the window `[s, e)` of its letters and qualities kept (none kept when there is no window or it is
shorter than `minLength`); the name is kept -/
def keepWindow (r : FQ.Read) : Option (Nat × Nat) → FQ.Read
  | some (s, e) => if e - s < minLength then ⟨r.name, [], []⟩
      else ⟨r.name, (r.sequence.drop s).take (e - s), (r.quality.drop s).take (e - s)⟩
  | none => ⟨r.name, [], []⟩

theorem ba_extract_list (l : List UInt8) (a b : Nat) :
    ((⟨l.toArray⟩ : ByteArray).extract a b).data.toList = (l.drop a).take (b - a) := by
  simp [ByteArray.data_extract, List.extract]

/-- **The kept window is the frozen contract's best window** of the read cut at the TruSeq adapter: for a read of at
most 10 000 letters whose cut part has an A/C/G/T letter, `trimRead` keeps exactly `get_best_window`'s window `[s, e)`
of the letters and qualities (via `ReadTrim.trimRead_def_eq_contract`), or nothing (no window, or shorter than
`minLength`). -/
theorem trimRead_best (r : FQ.Read) (h : r.sequence.length ≤ 10000) (j : Nat) (hj : j < (preCut r).1.size)
    (hjA : ReadTrim.isACGT (preCut r).1[j]! = true) :
    trimRead r = keepWindow r (get_best_window [] (ReadTrim.scoresOf (preCut r).1 (preCut r).2)
      (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ))) := by
  have hl1 : (preCut r).1 = (⟨r.sequence.toArray⟩ : ByteArray).extract 0 (cutAt ⟨r.sequence.toArray⟩) := rfl
  have hq1 : (preCut r).2 = (⟨r.quality.toArray⟩ : ByteArray).extract 0 (cutAt ⟨r.sequence.toArray⟩) := rfl
  have hcut : cutAt ⟨r.sequence.toArray⟩ ≤ r.sequence.length := by
    have := AdapterTrim.cut_le AdapterTrim.truSeq 6 1 ⟨r.sequence.toArray⟩
    simpa [ByteArray.size, cutAt] using this
  have hs : (preCut r).1.size ≤ 10000 := by
    rw [hl1, ByteArray.size_extract]; simp only [ByteArray.size, List.size_toArray]; omega
  have hc := ReadTrim.trimRead_def_eq_contract _ (preCut r).2 hs j hj hjA
  have hb : trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ =
      match ReadTrim.trimRead (preCut r).1 (preCut r).2 with
      | some (s, e) => AdapterTrim.dropShort minLength ((preCut r).1.extract s e) ((preCut r).2.extract s e)
      | none => AdapterTrim.dropShort minLength ByteArray.empty ByteArray.empty := by
    unfold trimBytes preCut
    rcases AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ with ⟨l, q⟩
    dsimp only
    generalize ReadTrim.trimRead l q = o
    rcases o with _ | ⟨s, e⟩ <;> rfl
  have ht : trimRead r = ⟨r.name, (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).1.data.toList,
      (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).2.data.toList⟩ := rfl
  rw [ht, hb, hc]
  unfold keepWindow
  split
  · rename_i s e hse
    have ha := ReadTrim.trimRead_def_acgt _ _ s e (hc.trans hse)
    rw [hl1, ByteArray.size_extract] at ha
    simp only [ByteArray.size, List.size_toArray] at ha
    have hsz : ((⟨r.sequence.toArray⟩ : ByteArray).extract 0 (cutAt ⟨r.sequence.toArray⟩)).extract s e =
        (⟨r.sequence.toArray⟩ : ByteArray).extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt ⟨r.sequence.toArray⟩) = e by omega]; simp
    have hqz : ((⟨r.quality.toArray⟩ : ByteArray).extract 0 (cutAt ⟨r.sequence.toArray⟩)).extract s e =
        (⟨r.quality.toArray⟩ : ByteArray).extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt ⟨r.sequence.toArray⟩) = e by omega]; simp
    simp only [hl1, hq1, hsz, hqz, AdapterTrim.dropShort, ByteArray.size_extract]
    simp only [ByteArray.size, List.size_toArray]
    split <;> split <;> first | omega | simp [ba_extract_list]
  · simp [AdapterTrim.dropShort, ByteArray.size]

theorem sum_const (l : List Int) (c : Int) (h : ∀ x ∈ l, x = c) : l.sum = c * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons, ih (fun y hy => h y (by simp [hy])), h x (by simp), List.length_cons]
    push_cast; rw [Int.mul_add, Int.mul_one, Int.add_comm]

/-- **No A/C/G/T before the TruSeq cut** (all N, or the cut leaves nothing): `trimRead` keeps nothing, and so does the
frozen contract's answer: its best window is a single base (every base scores −1 000 000), shorter than `minLength`. -/
theorem trimRead_best_none (r : FQ.Read) (hno : ∀ j, j < (preCut r).1.size → ReadTrim.isACGT (preCut r).1[j]! = false) :
    trimRead r = keepWindow r (get_best_window [] (ReadTrim.scoresOf (preCut r).1 (preCut r).2)
      (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ))) := by
  have hb : trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ =
      match ReadTrim.trimRead (preCut r).1 (preCut r).2 with
      | some (s, e) => AdapterTrim.dropShort minLength ((preCut r).1.extract s e) ((preCut r).2.extract s e)
      | none => AdapterTrim.dropShort minLength ByteArray.empty ByteArray.empty := by
    unfold trimBytes preCut
    rcases AdapterTrim.cutTruSeq ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩ with ⟨l, q⟩
    dsimp only
    generalize ReadTrim.trimRead l q = o
    rcases o with _ | ⟨s, e⟩ <;> rfl
  have htn : ReadTrim.trimRead (preCut r).1 (preCut r).2 = none := by
    cases ht : ReadTrim.trimRead (preCut r).1 (preCut r).2 with
    | none => rfl
    | some w =>
      obtain ⟨s, e⟩ := w
      have ha := ReadTrim.trimRead_def_acgt _ _ s e ht
      have := ha.2.2 s (Nat.le_refl _) ha.2.1
      rw [hno s (by omega)] at this; cases this
  have ht : trimRead r = ⟨r.name, (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).1.data.toList,
      (trimBytes ⟨r.sequence.toArray⟩ ⟨r.quality.toArray⟩).2.data.toList⟩ := rfl
  have hl : trimRead r = ⟨r.name, [], []⟩ := by
    rw [ht, hb, htn]; simp [AdapterTrim.dropShort, ByteArray.size]
  rw [hl]
  generalize hw : get_best_window [] (ReadTrim.scoresOf (preCut r).1 (preCut r).2)
    (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) = w
  rcases w with _ | ⟨s, e⟩
  · rfl
  · have hv := get_best_window_returns_a_valid_window _ _ _ _ hw
    simp only at hv
    have hm := get_best_window_returns_a_maximum_score _ _ _ _ (s, s + 1) hw (by simp) (by simp only; omega)
    have hlen : (ReadTrim.scoresOf (preCut r).1 (preCut r).2).length = (preCut r).1.size := by
      simp [ReadTrim.scoresOf]
    have hall : ∀ x ∈ (ReadTrim.scoresOf (preCut r).1 (preCut r).2).map (ReadTrim.perBase ReadTrim.defQ),
        x = -1000000 := by
      intro x hx
      simp only [ReadTrim.scoresOf, List.map_map, List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp [ReadTrim.perBase, ReadTrim.enc, hno i hi]
    have hws : ∀ a b, a < b → b ≤ (preCut r).1.size →
        window_score (ReadTrim.scoresOf (preCut r).1 (preCut r).2)
          (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ)) (a, b) = -1000000 * ((b - a : Nat) : Int) := by
      intro a b hab hb'
      generalize ReadTrim.scoresOf (preCut r).1 (preCut r).2 = S at hall hlen ⊢
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
    have : e - s < minLength := by unfold minLength; omega
    simp [keepWindow, this]

/-- **`trimRead` is the frozen contract** after the TruSeq cut, for every read of at most 10 000 letters: it keeps
`get_best_window`'s window of the cut read when that is at least `minLength` long, else nothing. -/
theorem trimRead_contract (r : FQ.Read) (h : r.sequence.length ≤ 10000) :
    trimRead r = keepWindow r (get_best_window [] (ReadTrim.scoresOf (preCut r).1 (preCut r).2)
      (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ))) := by
  by_cases hA : ∃ j, j < (preCut r).1.size ∧ ReadTrim.isACGT (preCut r).1[j]! = true
  · obtain ⟨j, hj, hjA⟩ := hA
    exact trimRead_best r h j hj hjA
  · exact trimRead_best_none r (fun j hj => by
      cases e : ReadTrim.isACGT (preCut r).1[j]!
      · rfl
      · exact absurd ⟨j, hj, e⟩ hA)

theorem isACGT_base (x : UInt8) (h : ReadTrim.isACGT x = true) : x ∈ FQ.bases := by
  simp only [ReadTrim.isACGT, Bool.or_eq_true, beq_iff_eq] at h
  simp only [FQ.bases, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ((h | h) | h) | h <;> simp [h]

/-- **A trimmed valid read is the read of a valid record**: same name and `+` line, letters and qualities the trimmed
ones (letters still in A C G T N, at most 1000, qualities still quality bytes, the two lengths still equal). -/
theorem trimRead_valid (r : FQ.Record) (h : r.valid) :
    ∃ r' : FQ.Record, r'.valid ∧ FQ.toRead r' = trimRead (FQ.toRead r) := by
  obtain ⟨a, b, h1, h2, h3, hs, hq, hacgt, -⟩ := trimRead_correct (FQ.toRead r)
  unfold FQ.Record.valid at h
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := h
  simp only [FQ.toRead] at hs hq hacgt h3 ⊢
  refine ⟨⟨r.name, (trimRead (FQ.toRead r)).sequence, r.plus, (trimRead (FQ.toRead r)).quality⟩, ?_, ?_⟩
  · unfold FQ.Record.valid; dsimp only
    simp only [FQ.toRead] at *
    refine ⟨v1, v2, v3, v4, v5, v6, fun x hx => isACGT_base x (hacgt x hx), ?_, v9, v10, ?_, ?_⟩
    · rw [hs]; simp; omega
    · rw [hq]; exact fun x hx => v11 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    · rw [hs, hq]; simp [v12]
  · simp only [FQ.toRead]
    rfl

/-- For every read `FQ.parse` returns, the trimmed read is the read of a valid record. -/
theorem parse_trim_valid (bytes : List UInt8) (reads : List FQ.Read) (h : FQ.parse bytes = some reads) :
    ∀ r ∈ reads, ∃ r' : FQ.Record, r'.valid ∧ FQ.toRead r' = trimRead r := by
  obtain ⟨records, hv, -, hr⟩ := FQ.parse_some bytes reads h
  intro r hr'
  rw [← hr] at hr'
  obtain ⟨rec, hrec, rfl⟩ := List.mem_map.mp hr'
  exact trimRead_valid rec (hv rec hrec)

/-! ## Trimming a chunk in parallel -/

theorem trimChunk_prefix (chunk : Array (ReadB × ReadB)) (size : Nat)
    (f : ReadB × ReadB → ReadB × ReadB) (m : Nat) :
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

/-- `trimChunk` is `trimReadB` on both mates of every pair, in order, however many parts it uses. -/
theorem trimChunk_eq (chunk : Array (ReadB × ReadB)) (parts : Nat) (hparts : 0 < parts) :
    trimChunk chunk parts = chunk.map fun (read1, read2) => (trimReadB read1, trimReadB read2) := by
  unfold trimChunk
  simp only []
  rw [trimChunk_prefix]
  have h := Nat.lt_div_mul_add (a := chunk.size + parts - 1) hparts
  generalize (chunk.size + parts - 1) / parts = q at h ⊢
  rw [Array.extract_eq_self_of_le (by rw [Nat.mul_comm]; omega)]

/-! ## The QNAME rule on bytes -/

theorem spaceAt_eq (n : ByteArray) : ∀ k i, i ≤ n.size → n.size - i ≤ k →
    spaceAt n k i = i + ((FQ.L n i).takeWhile (· != 32)).length
  | 0, i, h1, h2 => by
    have : i = n.size := by omega
    subst this; rw [spaceAt, FQ.L_size n _ (Nat.le_refl _)]; simp
  | k + 1, i, h1, h2 => by
    rw [spaceAt]
    by_cases hi : i < n.size
    · rw [FQ.L_cons n i hi, List.takeWhile_cons]
      by_cases hb : (n[i]! != 32) = true
      · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hi, hb⟩), if_pos hb,
          spaceAt_eq n k (i + 1) (by omega) (by omega)]; simp; omega
      · rw [if_neg (by simp [hb]), if_neg hb]; simp
    · rw [if_neg (by simp [hi]), FQ.L_size n i (by omega)]; simp

-- the last two bytes of a list of length at least 2
theorem drop_two (l : List UInt8) (h : 2 ≤ l.length) :
    l.drop (l.length - 2) = [l[l.length - 2]'(by omega), l[l.length - 1]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    show l.length - 2 + 1 + 1 = l.length by omega, List.drop_length]
  simp only [show l.length - 2 + 1 = l.length - 1 by omega]

theorem suffix_two (a b : UInt8) (l : List UInt8) :
    [a, b].isSuffixOf l = true ↔ ∃ h : 2 ≤ l.length, l[l.length - 2]'(by omega) = a ∧ l[l.length - 1]'(by omega) = b := by
  rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop]
  simp only [List.length_cons, List.length_nil]
  constructor
  · intro h
    have hl : 2 ≤ l.length := by
      have := congrArg List.length h; simp at this; omega
    refine ⟨hl, ?_⟩
    rw [drop_two l hl] at h
    simp only [List.cons.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  · rintro ⟨hl, h1, h2⟩
    rw [drop_two l hl, h1, h2]

theorem qnameB_eq (name : ByteArray) : (qnameB name).data.toList = qnameOf name.data.toList := by
  have hl : FQ.L name 0 = name.data.toList := by simp [FQ.L]
  have hs := spaceAt_eq name name.size 0 (Nat.zero_le _) (by omega)
  rw [hl, Nat.zero_add] at hs
  unfold qnameB qnameOf
  simp only []
  rw [hs]
  have e := @List.takeWhile_append_dropWhile _ (· != 32) name.data.toList
  have hlen : name.data.toList.length = name.size := by simp
  generalize name.data.toList.takeWhile (· != 32) = base at e ⊢
  generalize name.data.toList.dropWhile (· != 32) = rest at e
  have hpre : name.data.toList.take base.length = base := by rw [← e]; exact List.take_left' rfl
  have hle : base.length ≤ name.size := by rw [← hlen, ← e, List.length_append]; omega
  have hget : ∀ j (hj : j < base.length), name[j]! = base[j] := by
    intro j hj
    have hj' : j < name.data.toList.length := by omega
    rw [getElem!_pos name j (by omega), ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList hj',
      List.getElem_of_eq hpre.symm hj, List.getElem_take]
  have hx : ∀ e, e ≤ base.length → (name.extract 0 e).data.toList = base.take e := by
    intro e he
    rw [FQ.extract_list, hl, Nat.sub_zero, ← hpre, List.take_take, Nat.min_eq_left he]
  by_cases h2 : 2 ≤ base.length
  · have e2 := hget (base.length - 2) (by omega)
    have e1 := hget (base.length - 1) (by omega)
    have hdl : base.dropLast.dropLast = base.take (base.length - 2) := by
      rw [List.dropLast_eq_take, List.dropLast_eq_take, List.take_take, List.length_take]; congr 1; omega
    by_cases c : (base[base.length - 2]'(by omega) = 47) ∧
        (base[base.length - 1]'(by omega) = 49 ∨ base[base.length - 1]'(by omega) = 50)
    · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, e2, e1]; exact ⟨⟨h2, c.1⟩, c.2⟩),
        if_pos (by rw [Bool.or_eq_true, suffix_two, suffix_two]; rcases c.2 with c2 | c2
                   · exact Or.inl ⟨h2, c.1, c2⟩
                   · exact Or.inr ⟨h2, c.1, c2⟩), hdl, hx _ (by omega)]
    · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, e2, e1]
                     exact fun ⟨⟨_, a⟩, b⟩ => c ⟨a, b⟩),
        if_neg (by rw [Bool.or_eq_true, suffix_two, suffix_two]
                   rintro (⟨_, a, b⟩ | ⟨_, a, b⟩)
                   · exact c ⟨a, Or.inl b⟩
                   · exact c ⟨a, Or.inr b⟩),
        hx _ (Nat.le_refl _), List.take_length]
  · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega),
      if_neg (by rw [Bool.or_eq_true, suffix_two, suffix_two]; rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega),
      hx _ (Nat.le_refl _), List.take_length]

theorem qnameOkB_eq (q : ByteArray) : qnameOkB q = qnameOk q.data.toList := by
  unfold qnameOkB qnameOk
  have ha := FQ.allBytes_iff (fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)) q
  simp only [Array.length_toList, ByteArray.size_data]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [ha, List.all_eq_true]

/-- the shim's pairing name is the QNAME rule on the spec's read -/
theorem qnameB_toRead (r : ReadB) : (qnameB r.name).data.toList = qnameOf r.toRead.name := qnameB_eq r.name

end Spec

#print axioms Spec.trimRead_correct
#print axioms Spec.parse_trim_quality
#print axioms Spec.trimReadB_toRead
#print axioms Spec.trimRead_quality_bytes
#print axioms Spec.trimChunk_eq
#print axioms Spec.trimRead_best
#print axioms Spec.trimRead_best_none
#print axioms Spec.trimRead_contract
#print axioms Spec.trimRead_valid
#print axioms Spec.parse_trim_valid
#print axioms Spec.trimBytes_window
#print axioms Spec.trimBytes_acgt
#print axioms Spec.trimBytes_size
#print axioms Spec.cutAt_spec
#print axioms Spec.qnameB_eq
#print axioms Spec.qnameOkB_eq
