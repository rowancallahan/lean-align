/-! # FASTQ bytes for the shim (not part of Spec/)

* `FastqReader`: a file read in blocks, line by line (the FASTA reader uses it).
* `ReadB`: a read as bytes (name without '@', letters, quality); `ReadB.toRead` (Spec/Sam.lean) is the spec's `FQ.Read`.
* `parseFastqB`: the byte parser the shim runs on each slice of a FASTQ file. Proved equal to the spec's parser:
  `(parseFastqB b).toOption.map (·.toList.map ReadB.toRead) = FQ.parse b.toList` (`parseFastqB_eq`,
  Proofs/Fastq.lean), and `FQ.parse` itself runs through it (`parse_eq`, `@[csimp]`).

Every loop is a structural or well-founded recursion; the byte loops read by `uget` with the bound as a proof
argument (`findNewlineU`, `allBytesU`), each proved equal to its plain version (`@[csimp]`). -/

namespace Spec

/-! ## Byte scans -/

theorem usize_le (a : ByteArray) : a.usize.toNat ≤ a.size := by
  show a.size.toUSize.toNat ≤ a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

theorem usize_eq (a : ByteArray) (h : a.size < 4294967296) : a.usize.toNat = a.size := by
  show a.size.toUSize.toNat = a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)]

theorem toNat_toUSize (n : Nat) (h : n < 4294967296) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)]

theorem toNat_sub1 (a : USize) (h : a ≠ 0) : (a - 1).toNat = a.toNat - 1 := by
  have : a.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ a.toNat; rw [USize.toNat_one]; omega), USize.toNat_one]

theorem toNat_add1 (a : USize) (h : a.toNat < 4294967295) : (a + 1).toNat = a.toNat + 1 := by
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]

-- the first newline byte at or after `i` (or `bytes.size` when there is none), within `fuel` steps
def findNewlineGo (bytes : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | fuel + 1, i => if i < bytes.size && bytes[i]! != 10 then findNewlineGo bytes fuel (i + 1) else i

-- the first newline byte at or after `i` (or `bytes.size` when there is none)
def findNewline (bytes : ByteArray) (i : Nat) : Nat := findNewlineGo bytes (bytes.size - i) i

-- `findNewlineGo` by `uget`
def findNewlineU (bytes : @& ByteArray) (hs : bytes.size < 4294967296) (j : USize) (_hj : j.toNat ≤ bytes.size) : USize :=
  if h : j < bytes.usize then
    have hl : j.toNat < bytes.size := Nat.lt_of_lt_of_le h (usize_le bytes)
    if bytes.uget j hl != 10 then findNewlineU bytes hs (j + 1) (by rw [toNat_add1 j (by omega)]; omega) else j
  else j
termination_by bytes.size - j.toNat
decreasing_by
  rw [toNat_add1 j (by omega)]; omega

theorem findNewlineU_eq (bytes : ByteArray) (hs : bytes.size < 4294967296) : ∀ k (j : USize) hj,
    bytes.size - j.toNat = k → (findNewlineU bytes hs j hj).toNat = findNewlineGo bytes k j.toNat
  | 0, j, hj, hk => by
    rw [findNewlineU, dif_neg (fun h => by have : j.toNat < bytes.usize.toNat := h; rw [usize_eq bytes hs] at this; omega)]
    rfl
  | k + 1, j, hj, hk => by
    have hl : j.toNat < bytes.size := by omega
    rw [findNewlineU, dif_pos (show j < bytes.usize from show j.toNat < bytes.usize.toNat by rw [usize_eq bytes hs]; exact hl),
      findNewlineGo, getElem!_pos bytes j.toNat hl]
    dsimp only
    have hg : ∀ hl', bytes.uget j hl' = bytes[j.toNat] := fun _ => rfl
    simp only [hg]
    by_cases hb : (bytes[j.toNat] != 10) = true
    · rw [if_pos hb, if_pos (by simp [hl, hb]), findNewlineU_eq bytes hs k (j + 1) _ (by rw [toNat_add1 j (by omega)]; omega),
        toNat_add1 j (by omega)]
    · rw [if_neg hb, if_neg (by simp [hb])]

@[inline] def findNewlineF (bytes : ByteArray) (i : Nat) : Nat :=
  if h : i ≤ bytes.size ∧ bytes.size ≤ 4294967295 then
    (findNewlineU bytes (Nat.lt_succ_of_le h.2) i.toUSize (by rw [toNat_toUSize i (by omega)]; exact h.1)).toNat
  else findNewlineGo bytes (bytes.size - i) i

@[csimp] theorem findNewline_eq : @findNewline = @findNewlineF := by
  funext bytes i
  unfold findNewline findNewlineF
  split
  · rename_i h
    rw [findNewlineU_eq bytes (Nat.lt_succ_of_le h.2) (bytes.size - i) _ _ (by rw [toNat_toUSize i (by omega)]), toNat_toUSize i (by omega)]
  · rfl

-- every byte satisfies `p`
def allBytes (p : UInt8 → Bool) (bytes : ByteArray) : Bool := Nat.all bytes.size fun i _ => p bytes[i]!

-- `allBytes` as one loop over the bytes, last first
@[specialize] def allBytesGo (p : UInt8 → Bool) (bytes : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => p bytes[n]! && allBytesGo p bytes n

theorem allBytesGo_eq (p : UInt8 → Bool) (bytes : ByteArray) :
    ∀ n, allBytesGo p bytes n = Nat.all n fun i _ => p bytes[i]!
  | 0 => by simp [allBytesGo]
  | n + 1 => by rw [allBytesGo, Nat.all_succ, allBytesGo_eq p bytes n, Bool.and_comm]

-- `allBytesGo` by `uget`
@[specialize] def allBytesU (p : UInt8 → Bool) (bytes : ByteArray) (i : USize) (h : i.toNat ≤ bytes.size) : Bool :=
  if h0 : i = 0 then true
  else
    have hj : (i - 1).toNat = i.toNat - 1 := toNat_sub1 i h0
    have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
    p (bytes.uget (i - 1) (by omega)) && allBytesU p bytes (i - 1) (by omega)
termination_by i.toNat
decreasing_by
  have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [toNat_sub1 i h0]; omega

theorem allBytesU_eq (p : UInt8 → Bool) (bytes : ByteArray) : ∀ n (i : USize) h, i.toNat = n →
    allBytesU p bytes i h = allBytesGo p bytes n
  | 0, i, h, hi => by
    have h0 : i = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [allBytesU, dif_pos h0, allBytesGo]
  | n + 1, i, h, hi => by
    have h0 : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (i - 1).toNat = n := by rw [toNat_sub1 i h0, hi]; rfl
    rw [allBytesU, dif_neg h0, allBytesGo]
    dsimp only
    rw [allBytesU_eq p bytes n (i - 1) _ ej, getElem!_pos bytes n (by omega)]
    congr 2
    show bytes[(i - 1).toNat] = _
    simp only [ej]

@[inline] def allBytesF (p : UInt8 → Bool) (bytes : ByteArray) : Bool :=
  if bytes.size ≤ 4294967295 then allBytesU p bytes bytes.usize (usize_le bytes) else allBytesGo p bytes bytes.size

@[csimp] theorem allBytes_eq : @allBytes = @allBytesF := by
  funext p bytes
  unfold allBytesF
  split
  · rename_i h
    rw [allBytesU_eq p bytes _ bytes.usize _ (usize_eq bytes (Nat.lt_succ_of_le h))]
    exact (allBytesGo_eq p bytes bytes.size).symm
  · exact (allBytesGo_eq p bytes bytes.size).symm

/-! ## A file read in blocks, line by line (the FASTA reader) -/

-- a file read in blocks: the unread bytes are `buffer` from `pos` on
structure FastqReader where
  handle : IO.FS.Handle
  buffer : IO.Ref ByteArray
  pos    : IO.Ref Nat

def FastqReader.ofHandle (handle : IO.FS.Handle) : IO FastqReader :=
  return { handle, buffer := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef 0 }

-- the next line without its "\n" (or "\r\n"); none at the end of the file
def FastqReader.line (reader : FastqReader) : IO (Option ByteArray) := do
  repeat
    let buffer ← reader.buffer.get
    let pos ← reader.pos.get
    let newline := findNewline buffer pos
    if newline < buffer.size then
      reader.pos.set (newline + 1)
      let stop := if pos < newline && buffer[newline - 1]! == 13 then newline - 1 else newline
      return some (buffer.extract pos stop)
    let block ← reader.handle.read (4 * 1024 * 1024)
    if block.isEmpty then
      reader.buffer.set ByteArray.empty
      reader.pos.set 0
      return if pos < buffer.size then some (buffer.extract pos buffer.size) else none
    reader.buffer.set (buffer.extract pos buffer.size ++ block)
    reader.pos.set 0
  return none

/-! ## The byte parser -/

-- a read as bytes: the name without its '@', the letters, the quality (`ReadB.toRead`, Spec/Sam.lean)
structure ReadB where
  name : ByteArray
  seq  : ByteArray
  qual : ByteArray

-- the letters `FQ.bases` allows: A C G T N
@[inline] def isBase (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84 || b == 78

-- `FQ.Record.valid` of the four lines (each without its '\n'); `none` when valid, else the reason
def recordError (name seq plus qual : ByteArray) : Option String :=
  if !(0 < name.size && name[0]! == 64) then some "header line does not start with '@'"
  else if !(10 ≤ name.size && name.size ≤ 501) then some "header line is not 10..501 bytes"
  else if !allBytes (fun b => b < 128 && b != 10 && b != 13) name then
    some "header line is not ASCII (or has a carriage return)"
  else if !allBytes isBase seq then some "letters other than A C G T N (lowercase, IUPAC, carriage return)"
  else if !(seq.size ≤ 1000) then some "read longer than 1000 bases"
  else if !(0 < plus.size && plus[0]! == 43) then some "third line of a record does not start with '+'"
  else if !(plus.size == 1 || decide (plus.extract 1 plus.size = name.extract 1 name.size)) then
    some "'+' line names a different read"
  else if !allBytes (fun b => 33 ≤ b && b ≤ 126) qual then some "quality outside '!'..'~' (or a carriage return)"
  else if qual.size != seq.size then some "sequence and quality lengths differ"
  else none

theorem findNewlineGo_ge (bytes : ByteArray) : ∀ k i, i ≤ findNewlineGo bytes k i
  | 0, i => Nat.le_refl _
  | k + 1, i => by
    rw [findNewlineGo]; split
    · exact Nat.le_trans (Nat.le_succ i) (findNewlineGo_ge bytes k (i + 1))
    · exact Nat.le_refl _

theorem findNewline_ge (bytes : ByteArray) (i : Nat) : i ≤ findNewline bytes i := findNewlineGo_ge _ _ _

-- the reads of `b` from byte `i` on, appended to `acc`; an error names the first record that is not valid
def parseFrom (b : ByteArray) (i : Nat) (acc : Array ReadB) : Except String (Array ReadB) :=
  if h : b.size ≤ i then .ok acc else
  let j1 := findNewline b i
  if b.size ≤ j1 then .error "FASTQ: file ends inside a record" else
  let j2 := findNewline b (j1 + 1)
  if b.size ≤ j2 then .error "FASTQ: file ends inside a record" else
  let j3 := findNewline b (j2 + 1)
  if b.size ≤ j3 then .error "FASTQ: file ends inside a record" else
  let j4 := findNewline b (j3 + 1)
  if b.size ≤ j4 then .error "FASTQ: file ends inside a record (or without a final newline)" else
  let name := b.extract i j1
  let seq := b.extract (j1 + 1) j2
  let plus := b.extract (j2 + 1) j3
  let qual := b.extract (j3 + 1) j4
  match recordError name seq plus qual with
  | some why => .error s!"FASTQ: {why} (record at byte {i} of the slice)"
  | none => parseFrom b (j4 + 1) (acc.push ⟨name.extract 1 name.size, seq, qual⟩)
termination_by b.size - i
decreasing_by
  have h1 := findNewline_ge b i
  have h2 := findNewline_ge b (findNewline b i + 1)
  have h3 := findNewline_ge b (findNewline b (findNewline b i + 1) + 1)
  have h4 := findNewline_ge b (findNewline b (findNewline b (findNewline b i + 1) + 1) + 1)
  omega

-- the reads of a FASTQ file (or of a slice of one cut after a record), or why it is not valid FASTQ
def parseFastqB (b : ByteArray) : Except String (Array ReadB) := parseFrom b 0 #[]

end Spec
