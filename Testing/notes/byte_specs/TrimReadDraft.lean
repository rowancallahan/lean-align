import TrimBytes

namespace FQ

def atSign   : UInt8 := 0x40
def plusSign : UInt8 := 0x2B
def newline  : UInt8 := 0x0A
def carriageReturn : UInt8 := 0x0D
def bases    : List UInt8 := [0x41, 0x43, 0x47, 0x54, 0x4E]
def qualityByte (b : UInt8) : Bool := 0x21 ≤ b && b ≤ 0x7E
def ascii (b : UInt8) : Bool := b < 0x80

structure Record where
  name     : List UInt8
  sequence : List UInt8
  plus     : List UInt8
  quality  : List UInt8

structure Read where
  name     : List UInt8
  sequence : List UInt8
  quality  : List UInt8

def Record.valid (r : Record) : Prop :=
  r.name.head? = some atSign ∧
  10 ≤ r.name.length ∧
  r.name.length ≤ 501 ∧
  (∀ b ∈ r.name, ascii b) ∧
  newline ∉ r.name ∧
  carriageReturn ∉ r.name ∧
  (∀ b ∈ r.sequence, b ∈ bases) ∧
  r.sequence.length ≤ 1000 ∧
  r.plus.head? = some plusSign ∧
  (r.plus.tail = [] ∨ r.plus.tail = r.name.tail) ∧
  (∀ b ∈ r.quality, qualityByte b) ∧
  r.quality.length = r.sequence.length

def toBytes (r : Record) : List UInt8 :=
  r.name ++ [newline] ++
  r.sequence ++ [newline] ++
  r.plus ++ [newline] ++
  r.quality ++ [newline]

def toRead (r : Record) : Read := ⟨r.name.tail, r.sequence, r.quality⟩


-- ---- trimmer on Read (draft; becomes Spec/Proofs code once Spec/Fastq has `Read`) ----
def minLength : Nat := 25

def trimRecord (r : Read) : Read :=
  let p := TrimBytes.trimSQ minLength r.sequence r.quality
  { r with sequence := p.1, quality := p.2 }

def trimChunk (chunk : Array (Read × Read)) (parts : Nat) : Array (Read × Read) :=
  TrimBytes.trimChunkG trimRecord chunk parts

theorem trimRecord_correct (r : Read) :
    ∃ a b, a ≤ b ∧ b ≤ TrimBytes.cutAt (TrimBytes.ba r.sequence) ∧ TrimBytes.cutAt (TrimBytes.ba r.sequence) ≤ r.sequence.length ∧
      (trimRecord r).name = r.name ∧
      (trimRecord r).sequence = (r.sequence.drop a).take (b - a) ∧
      (trimRecord r).quality = (r.quality.drop a).take (b - a) ∧
      (∀ x ∈ (trimRecord r).sequence, ReadTrim.isACGT x = true) ∧
      ((trimRecord r).sequence.length = 0 ∨ minLength ≤ (trimRecord r).sequence.length) := by
  simp only [trimRecord]
  obtain ⟨a, b, h⟩ := TrimBytes.trimSQ_correct minLength r.sequence r.quality
  exact ⟨a, b, h.1, h.2.1, h.2.2.1, trivial, h.2.2.2⟩

theorem pair_eta {α β : Type} (p : α × β) : (p.1, p.2) = p := rfl

/-- **The kept window is the frozen contract's best window** of the read cut at the adapter (`TrimBytes.trimSQ_best`):
for a read of at most 10 000 letters whose cut part has an A/C/G/T letter, the trimmed read keeps its name and has
`get_best_window`'s window of the letters and qualities, or nothing (no window, or shorter than `minLength`). -/
theorem trimRecord_best (r : Read) (h : r.sequence.length ≤ 10000) (j : Nat)
    (hj : j < (TrimBytes.preCut r.sequence r.quality).1.size)
    (hjA : ReadTrim.isACGT (TrimBytes.preCut r.sequence r.quality).1[j]! = true) :
    (trimRecord r).name = r.name ∧
    ((trimRecord r).sequence, (trimRecord r).quality) =
      TrimBytes.keepWindow minLength r.sequence r.quality (get_best_window [] (ReadTrim.scoresOf
        (TrimBytes.preCut r.sequence r.quality).1 (TrimBytes.preCut r.sequence r.quality).2)
        (fun ws => ws.map (ReadTrim.perBase ReadTrim.defQ))) := by
  have hs : (TrimBytes.preCut r.sequence r.quality).1.size ≤ 10000 := by
    have := AdapterTrim.cut_le AdapterTrim.truSeq 6 1 (TrimBytes.ba r.sequence)
    have e : (TrimBytes.preCut r.sequence r.quality).1 =
      (TrimBytes.ba r.sequence).extract 0 (TrimBytes.cutAt (TrimBytes.ba r.sequence)) := rfl
    rw [e, ByteArray.size_extract, TrimBytes.ba_size]
    rw [TrimBytes.ba_size] at this; unfold TrimBytes.cutAt; omega
  have hb := TrimBytes.trimSQ_best minLength r.sequence r.quality hs j hj hjA
  simp only [trimRecord, true_and]
  rw [pair_eta, hb]

theorem isBase_mem (x : UInt8) (h : TrimBytes.isBase x = true) : x ∈ bases := by
  simp only [TrimBytes.isBase, Bool.or_eq_true, beq_iff_eq] at h
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with (((h | h) | h) | h) | h <;> simp [h]

/-- A trimmed valid read is still the read of a valid record: same name and `+` line. -/
theorem trimRecord_valid (r : Record) (h : r.valid) :
    ∃ r' : Record, r'.valid ∧ toRead r' = trimRecord (toRead r) := by
  unfold Record.valid at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  obtain ⟨v1, v2, v3, v4⟩ := TrimBytes.trimSQ_valid minLength r.sequence r.quality (fun b => qualityByte b = true) h11 h12
  refine ⟨⟨r.name, (TrimBytes.trimSQ minLength r.sequence r.quality).1, r.plus,
    (TrimBytes.trimSQ minLength r.sequence r.quality).2⟩, ?_, by simp only [trimRecord, toRead, List.tail]⟩
  unfold Record.valid; dsimp only
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, h9, h10, ?_, ?_⟩
  · exact fun x hx => isBase_mem x (v3 x hx)
  · exact Nat.le_trans v4 h8
  · exact v1
  · exact v2

theorem trimChunk_eq (chunk : Array (Read × Read)) (parts : Nat) (hparts : 0 < parts) :
    trimChunk chunk parts = chunk.map fun (r1, r2) => (trimRecord r1, trimRecord r2) :=
  TrimBytes.trimChunkG_eq _ _ _ hparts

end FQ

#print axioms FQ.trimRecord_correct
#print axioms FQ.trimRecord_valid
#print axioms FQ.trimRecord_best
#print axioms FQ.trimChunk_eq
