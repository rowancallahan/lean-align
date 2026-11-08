import ReadTrim
import AdapterTrim

/-! # The trimmer on byte lists (FASTQ reads as `List UInt8`)

`trimSQ minLen seq qual` is the read trimmer the FASTQ glue runs on every mate: the TruSeq adapter cut
(`AdapterTrim.cutTruSeq`), then the best quality window (`ReadTrim.trimRead`), then `AdapterTrim.dropShort minLen`.
It runs the existing `ByteArray` functions (so their `@[csimp]` loops are what executes) and converts at the ends.

* `trimSQ_correct`: both outputs are the same window `[a, b)` of `seq` / `qual`, `b` is at most the adapter cut,
  every output letter is A/C/G/T, and the output is empty or has at least `minLen` letters.
* `trimSQ_valid`: a byte predicate every quality byte satisfies still holds, equal lengths stay equal, and the letters
  stay within A C G T N.
* `trimChunkG_eq`: the parallel chunk trimmer is `map` of the per-mate trimmer, in order. -/

namespace TrimBytes

/-- A byte list as a `ByteArray`. -/
@[inline] def ba (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The three steps on `ByteArray`s. -/
def trimBA (minLen : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  let (letters, qual) := AdapterTrim.cutTruSeq letters qual
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  AdapterTrim.dropShort minLen letters qual

/-- The trimmer on byte lists: letters and qualities of one mate. -/
def trimSQ (minLen : Nat) (seq qual : List UInt8) : List UInt8 × List UInt8 :=
  let p := trimBA minLen (ba seq) (ba qual)
  (p.1.data.toList, p.2.data.toList)

/-- The adapter cut's position (TruSeq, 6, 1). -/
def cutAt (letters : ByteArray) : Nat := AdapterTrim.cutPos AdapterTrim.truSeq 6 1 letters

/-- Trim every pair of a chunk with `f`, in `parts` tasks running at once (`trimChunkG_eq`). -/
def trimChunkG {α : Type} (f : α → α) (chunk : Array (α × α)) (parts : Nat) : Array (α × α) :=
  let size := (chunk.size + parts - 1) / parts
  let tasks := (List.range parts).map fun part => Task.spawn fun _ =>
    (chunk.extract (part * size) ((part + 1) * size)).map fun (r1, r2) => (f r1, f r2)
  tasks.foldl (fun out task => out ++ task.get) #[]

/-! ## Proofs -/

theorem extract_extract_ba (x : ByteArray) (i j k l : Nat) :
    (x.extract i j).extract k l = x.extract (i + k) (min (i + l) j) := by
  apply ByteArray.ext
  simp [Array.extract_extract]

theorem dropShort_cases (m : Nat) (l q : ByteArray) :
    AdapterTrim.dropShort m l q = (l, q) ∨ AdapterTrim.dropShort m l q = (ByteArray.empty, ByteArray.empty) := by
  unfold AdapterTrim.dropShort; split <;> simp

/-- Both outputs are the window `[a, b)` of the inputs, `b` at most the adapter cut; the letters are A/C/G/T. -/
theorem trimBA_window (m : Nat) (letters qual : ByteArray) :
    ∃ a b, a ≤ b ∧ b ≤ cutAt letters ∧ cutAt letters ≤ letters.size ∧
      (trimBA m letters qual).1 = letters.extract a b ∧ (trimBA m letters qual).2 = qual.extract a b ∧
      ((trimBA m letters qual).1.size = 0 ∨ ∀ i, a ≤ i → i < b → ReadTrim.isACGT letters[i]! = true) := by
  have hc : cutAt letters ≤ letters.size := AdapterTrim.cut_le _ _ _ _
  have hl1 : (AdapterTrim.cutTruSeq letters qual).1 = letters.extract 0 (cutAt letters) := rfl
  have hq1 : (AdapterTrim.cutTruSeq letters qual).2 = qual.extract 0 (cutAt letters) := rfl
  unfold trimBA
  simp only [hl1, hq1]
  split
  · rename_i s e hse
    have h := ReadTrim.trimRead_def_acgt _ _ s e hse
    have hsz : (letters.extract 0 (cutAt letters)).size = cutAt letters := by
      rw [ByteArray.size_extract]; omega
    have hec : e ≤ cutAt letters := by omega
    have e1 : (letters.extract 0 (cutAt letters)).extract s e = letters.extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt letters) = e by omega]; simp
    have e2 : (qual.extract 0 (cutAt letters)).extract s e = qual.extract s e := by
      rw [extract_extract_ba, show min (0 + e) (cutAt letters) = e by omega]; simp
    have hacgt : ∀ i, s ≤ i → i < e → ReadTrim.isACGT letters[i]! = true := by
      intro i h1 h2
      have := h.2.2 i h1 h2
      rw [getElem!_pos _ i (by omega)] at this
      rw [getElem!_pos letters i (by omega)]
      simpa [ByteArray.getElem_extract] using this
    rcases dropShort_cases m ((letters.extract 0 (cutAt letters)).extract s e)
      ((qual.extract 0 (cutAt letters)).extract s e) with h1 | h1
    · refine ⟨s, e, by omega, hec, hc, ?_, ?_, Or.inr hacgt⟩ <;> rw [h1] <;> simp [e1, e2]
    · refine ⟨0, 0, Nat.le_refl _, by omega, hc, ?_, ?_, ?_⟩ <;> rw [h1] <;> first | (apply ByteArray.ext; simp) | simp
  · refine ⟨0, 0, Nat.le_refl _, by omega, hc, ?_, ?_, ?_⟩ <;>
      (unfold AdapterTrim.dropShort; split) <;> first | (apply ByteArray.ext; simp) | simp

theorem trimBA_size (m : Nat) (letters qual : ByteArray) :
    (trimBA m letters qual).1.size = 0 ∨ m ≤ (trimBA m letters qual).1.size :=
  AdapterTrim.dropShort_size _ _ _

theorem ba_size (l : List UInt8) : (ba l).size = l.length := by simp [ba, ByteArray.size]

theorem ba_extract (l : List UInt8) (a b : Nat) : ((ba l).extract a b).data.toList = (l.drop a).take (b - a) := by
  simp [ba, ByteArray.data_extract, List.extract]

theorem ba_get (l : List UInt8) (i : Nat) (h : i < l.length) : (ba l)[i]! = l[i] := by
  rw [getElem!_pos (ba l) i (by rw [ba_size]; exact h)]; rfl

/-- **The trimmer on byte lists**: with `c` the adapter cut of `seq`, the output letters and qualities are the window
`[a, b)` of `seq` and `qual` (`drop a` then `take (b - a)`), `b ≤ c ≤ |seq|`, every output letter is A/C/G/T, and the
output has no letters or at least `minLen`. -/
theorem trimSQ_correct (minLen : Nat) (seq qual : List UInt8) :
    ∃ a b, a ≤ b ∧ b ≤ cutAt (ba seq) ∧ cutAt (ba seq) ≤ seq.length ∧
      (trimSQ minLen seq qual).1 = (seq.drop a).take (b - a) ∧
      (trimSQ minLen seq qual).2 = (qual.drop a).take (b - a) ∧
      (∀ x ∈ (trimSQ minLen seq qual).1, ReadTrim.isACGT x = true) ∧
      ((trimSQ minLen seq qual).1.length = 0 ∨ minLen ≤ (trimSQ minLen seq qual).1.length) := by
  obtain ⟨a, b, h1, h2, h3, h4, h5, h6⟩ := trimBA_window minLen (ba seq) (ba qual)
  have hlen : ∀ p : ByteArray × ByteArray, p.1.data.toList.length = p.1.size := fun p => by rw [Array.length_toList]; rfl
  rw [ba_size] at h3
  refine ⟨a, b, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · simp only [trimSQ, h4, ba_extract]
  · simp only [trimSQ, h5, ba_extract]
  · intro x hx
    rcases h6 with h6 | h6
    · have e : (trimBA minLen (ba seq) (ba qual)).1.data.toList = [] := by
        rw [List.eq_nil_iff_length_eq_zero, hlen (trimBA minLen (ba seq) (ba qual)), h6]
      simp only [trimSQ, e] at hx; simp at hx
    · simp only [trimSQ, h4, ba_extract] at hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_take, List.length_drop] at hk
      have := h6 (a + k) (by omega) (by omega)
      rw [ba_get seq (a + k) (by omega)] at this
      simpa [List.getElem_take, List.getElem_drop] using this
  · simpa only [trimSQ, hlen] using trimBA_size minLen (ba seq) (ba qual)

/-- The letters A C G T N (the spec's `FQ.bases`) as a test. -/
def isBase (x : UInt8) : Bool := x == 0x41 || x == 0x43 || x == 0x47 || x == 0x54 || x == 0x4E

theorem acgt_base (x : UInt8) (h : ReadTrim.isACGT x = true) : isBase x = true := by
  simp only [ReadTrim.isACGT, isBase] at h ⊢; rw [h]; rfl

/-- **What a valid read keeps**: a byte predicate `P` true of every input quality stays true, equal lengths stay
equal, the letters stay A C G T N, and the read gets no longer. -/
theorem trimSQ_valid (minLen : Nat) (seq qual : List UInt8) (P : UInt8 → Prop) (hP : ∀ x ∈ qual, P x)
    (hlen : qual.length = seq.length) :
    (∀ x ∈ (trimSQ minLen seq qual).2, P x) ∧
    (trimSQ minLen seq qual).2.length = (trimSQ minLen seq qual).1.length ∧
    (∀ x ∈ (trimSQ minLen seq qual).1, isBase x = true) ∧
    (trimSQ minLen seq qual).1.length ≤ seq.length := by
  obtain ⟨a, b, h1, h2, h3, h4, h5, h6, -⟩ := trimSQ_correct minLen seq qual
  refine ⟨?_, ?_, fun x hx => acgt_base x (h6 x hx), ?_⟩
  · rw [h5]; exact fun x hx => hP x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · rw [h4, h5]; simp [hlen]
  · rw [h4]; simp; omega

theorem trimChunkG_prefix {α : Type} (chunk : Array (α × α)) (size : Nat) (f : α × α → α × α) (m : Nat) :
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

/-- **`trimChunkG` is `f` on both mates of every pair, in order**, however many parts it uses. -/
theorem trimChunkG_eq {α : Type} (f : α → α) (chunk : Array (α × α)) (parts : Nat) (hparts : 0 < parts) :
    trimChunkG f chunk parts = chunk.map fun (r1, r2) => (f r1, f r2) := by
  unfold trimChunkG
  simp only []
  rw [trimChunkG_prefix]
  have h := Nat.lt_div_mul_add (a := chunk.size + parts - 1) hparts
  generalize (chunk.size + parts - 1) / parts = q at h ⊢
  rw [Array.extract_eq_self_of_le (by rw [Nat.mul_comm]; omega)]

end TrimBytes

#print axioms TrimBytes.trimSQ_correct
#print axioms TrimBytes.trimSQ_valid
#print axioms TrimBytes.trimChunkG_eq
