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

theorem Go_skip (bytes : ByteArray) (k i : Nat) (hi : i < bytes.size) (hb : bytes[i]! ≠ 10) :
    findNewlineGo bytes (k + 1) i = findNewlineGo bytes k (i + 1) := by
  rw [findNewlineGo, if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]; exact ⟨hi, hb⟩)]

theorem Go_hit (bytes : ByteArray) (k i : Nat) (hi : i < bytes.size) (hb : bytes[i]! = 10) :
    findNewlineGo bytes (k + 1) i = i := by
  rw [findNewlineGo, if_neg (by simp [hb])]

-- `findNewlineU` eight bytes per step: one bounds test per eight bytes (`findNewline8_eq`)
def findNewline8 (bytes : @& ByteArray) (hs : bytes.size < 4294967296) (j : USize) (hj : j.toNat ≤ bytes.size) : USize :=
  if h : 8 ≤ bytes.usize ∧ j ≤ bytes.usize - 8 then
    have hu : bytes.usize.toNat = bytes.size := usize_eq bytes hs
    have h8 : j.toNat + 8 ≤ bytes.size := by
      have a := h.1; have b := h.2
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ a] at b
      have : (8 : USize).toNat = 8 := toNat_toUSize 8 (by decide)
      rw [USize.le_iff_toNat_le] at a
      omega
    have e1 : (j + 1).toNat = j.toNat + 1 := toNat_add1 j (by omega)
    have e2 : (j + 1 + 1).toNat = j.toNat + 2 := by rw [toNat_add1 _ (by omega), e1]
    have e3 : (j + 1 + 1 + 1).toNat = j.toNat + 3 := by rw [toNat_add1 _ (by omega), e2]
    have e4 : (j + 1 + 1 + 1 + 1).toNat = j.toNat + 4 := by rw [toNat_add1 _ (by omega), e3]
    have e5 : (j + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 5 := by rw [toNat_add1 _ (by omega), e4]
    have e6 : (j + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 6 := by rw [toNat_add1 _ (by omega), e5]
    have e7 : (j + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 7 := by rw [toNat_add1 _ (by omega), e6]
    have e8 : (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 8 := by rw [toNat_add1 _ (by omega), e7]
    if bytes.uget j (by omega) == 10 then j
    else if bytes.uget (j + 1) (by omega) == 10 then j + 1
    else if bytes.uget (j + 1 + 1) (by omega) == 10 then j + 1 + 1
    else if bytes.uget (j + 1 + 1 + 1) (by omega) == 10 then j + 1 + 1 + 1
    else if bytes.uget (j + 1 + 1 + 1 + 1) (by omega) == 10 then j + 1 + 1 + 1 + 1
    else if bytes.uget (j + 1 + 1 + 1 + 1 + 1) (by omega) == 10 then j + 1 + 1 + 1 + 1 + 1
    else if bytes.uget (j + 1 + 1 + 1 + 1 + 1 + 1) (by omega) == 10 then j + 1 + 1 + 1 + 1 + 1 + 1
    else if bytes.uget (j + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega) == 10 then j + 1 + 1 + 1 + 1 + 1 + 1 + 1
    else findNewline8 bytes hs (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega)
  else findNewlineU bytes hs j hj
termination_by bytes.size - j.toNat
decreasing_by omega

theorem findNewline8_eq (bytes : ByteArray) (hs : bytes.size < 4294967296) : ∀ n (j : USize) hj,
    bytes.size - j.toNat = n → (findNewline8 bytes hs j hj).toNat = findNewlineGo bytes n j.toNat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro j hj hn
  rw [findNewline8]
  split
  · rename_i h
    have hu : bytes.usize.toNat = bytes.size := usize_eq bytes hs
    have h8 : j.toNat + 8 ≤ bytes.size := by
      have a := h.1; have b := h.2
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ a] at b
      have : (8 : USize).toNat = 8 := toNat_toUSize 8 (by decide)
      rw [USize.le_iff_toNat_le] at a
      omega
    have e1 : (j + 1).toNat = j.toNat + 1 := toNat_add1 j (by omega)
    have e2 : (j + 1 + 1).toNat = j.toNat + 2 := by rw [toNat_add1 _ (by omega), e1]
    have e3 : (j + 1 + 1 + 1).toNat = j.toNat + 3 := by rw [toNat_add1 _ (by omega), e2]
    have e4 : (j + 1 + 1 + 1 + 1).toNat = j.toNat + 4 := by rw [toNat_add1 _ (by omega), e3]
    have e5 : (j + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 5 := by rw [toNat_add1 _ (by omega), e4]
    have e6 : (j + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 6 := by rw [toNat_add1 _ (by omega), e5]
    have e7 : (j + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 7 := by rw [toNat_add1 _ (by omega), e6]
    have e8 : (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 8 := by rw [toNat_add1 _ (by omega), e7]
    have hg : ∀ (x : USize) hx, bytes.uget x hx = bytes[x.toNat]! := fun x hx => by
      rw [getElem!_pos bytes x.toNat hx]; rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    dsimp only
    simp only [hg, e1, e2, e3, e4, e5, e6, e7, beq_iff_eq]
    have s := fun k i hi hb => Go_skip bytes k i hi hb
    have t := fun k i hi hb => Go_hit bytes k i hi hb
    split
    · rename_i b0; rw [t _ _ (by omega) b0]
    rename_i b0; rw [s _ _ (by omega) b0]
    split
    · rename_i b1; rw [t _ _ (by omega) b1, e1]
    rename_i b1; rw [s _ _ (by omega) b1]
    split
    · rename_i b2; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b2), e2]
    rename_i b2; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b2)]
    split
    · rename_i b3; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b3), e3]
    rename_i b3; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b3)]
    split
    · rename_i b4; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b4), e4]
    rename_i b4; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b4)]
    split
    · rename_i b5; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b5), e5]
    rename_i b5; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b5)]
    split
    · rename_i b6; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b6), e6]
    rename_i b6; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b6)]
    split
    · rename_i b7; rw [t _ _ (by omega) (by simpa [Nat.add_assoc] using b7), e7]
    rename_i b7; rw [s _ _ (by omega) (by simpa [Nat.add_assoc] using b7)]
    rw [ih m (by omega) _ _ (by omega), e8]
  · exact findNewlineU_eq bytes hs n j hj hn

@[inline] def findNewlineF (bytes : ByteArray) (i : Nat) : Nat :=
  if h : i ≤ bytes.size ∧ bytes.size ≤ 4294967295 then
    (findNewline8 bytes (Nat.lt_succ_of_le h.2) i.toUSize (by rw [toNat_toUSize i (by omega)]; exact h.1)).toNat
  else findNewlineGo bytes (bytes.size - i) i

@[csimp] theorem findNewline_eq : @findNewline = @findNewlineF := by
  funext bytes i
  unfold findNewline findNewlineF
  split
  · rename_i h
    rw [findNewline8_eq bytes (Nat.lt_succ_of_le h.2) (bytes.size - i) _ _ (by rw [toNat_toUSize i (by omega)]), toNat_toUSize i (by omega)]
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

/-! ## One scan per line: the parser with its checks fused into the line scans -/

-- the first index `≥ i` (within `fuel` steps) whose byte fails `p`, or where the bytes end
@[specialize] def scanGo (p : UInt8 → Bool) (b : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | f + 1, i => if i < b.size && p b[i]! then scanGo p b f (i + 1) else i

theorem scanGo_spec (p : UInt8 → Bool) (b : ByteArray) : ∀ f i, b.size - i ≤ f →
    i ≤ scanGo p b f i ∧ (i ≤ b.size → scanGo p b f i ≤ b.size) ∧
    (∀ j, i ≤ j → j < scanGo p b f i → p b[j]! = true) ∧
    (scanGo p b f i < b.size → p b[scanGo p b f i]! = false)
  | 0, i, hf => by
    simp only [scanGo]
    refine ⟨Nat.le_refl _, fun h => h, fun j h1 h2 => by omega, fun h => by omega⟩
  | f + 1, i, hf => by
    rw [scanGo]
    by_cases hc : (i < b.size && p b[i]!) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have ih := scanGo_spec p b f (i + 1) (by omega)
      refine ⟨by omega, fun _ => ih.2.1 (by omega), fun j h1 h2 => ?_, ih.2.2.2⟩
      by_cases e : j = i
      · subst e; exact hc.2
      · exact ih.2.2.1 j (by omega) h2
    · rw [if_neg hc]
      refine ⟨Nat.le_refl _, fun h => h, fun j h1 h2 => by omega, fun h => ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
      cases e : p b[i]!
      · rfl
      · exact absurd e (hc h)

-- the first newline at or after `i`, when the bytes before it all pass a test that a newline fails
theorem findNewlineGo_at (b : ByteArray) : ∀ f i k, b.size - i ≤ f → i ≤ k → k < b.size → b[k]! = 10 →
    (∀ j, i ≤ j → j < k → b[j]! ≠ 10) → findNewlineGo b f i = k
  | 0, i, k, hf, h1, h2, h3, h4 => by omega
  | f + 1, i, k, hf, h1, h2, h3, h4 => by
    rw [findNewlineGo]
    by_cases e : i = k
    · subst e; rw [if_neg (by simp [h3])]
    · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]; exact ⟨by omega, h4 i (Nat.le_refl _) (by omega)⟩)]
      exact findNewlineGo_at b f (i + 1) k (by omega) (by omega) h2 h3 (fun j a c => h4 j (by omega) c)

theorem findNewline_at (b : ByteArray) (i k : Nat) (h1 : i ≤ k) (h2 : k < b.size) (h3 : b[k]! = 10)
    (h4 : ∀ j, i ≤ j → j < k → b[j]! ≠ 10) : findNewline b i = k :=
  findNewlineGo_at b _ i k (Nat.le_refl _) h1 h2 h3 h4

theorem allBytes_extract (p : UInt8 → Bool) (b : ByteArray) (i k : Nat) (hk : k ≤ b.size)
    (h : ∀ j, i ≤ j → j < k → p b[j]! = true) : allBytes p (b.extract i k) = true := by
  have hsz : (b.extract i k).size = k - i := by rw [ByteArray.size_extract]; omega
  have hget : ∀ t, t < k - i → (b.extract i k)[t]! = b[i + t]! := by
    intro t ht
    rw [getElem!_pos (b.extract i k) t (by omega), getElem!_pos b (i + t) (by omega), ByteArray.getElem_extract]
  have hall : ∀ n, n ≤ (b.extract i k).size → allBytesGo p (b.extract i k) n = true := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [allBytesGo, ih (by omega), Bool.and_true, hget n (by omega)]
      exact h (i + n) (by omega) (by omega)
  unfold allBytes
  rw [← allBytesGo_eq]
  exact hall _ (Nat.le_refl _)

-- `scanGo` over the rest of the bytes
def scan (p : UInt8 → Bool) (b : ByteArray) (i : Nat) : Nat := scanGo p b (b.size - i) i

-- `scanGo` by `uget`
@[specialize] def scanU (p : UInt8 → Bool) (b : @& ByteArray) (hs : b.size < 4294967296) (j : USize)
    (_hj : j.toNat ≤ b.size) : USize :=
  if h : j < b.usize then
    have hl : j.toNat < b.size := Nat.lt_of_lt_of_le h (usize_le b)
    if p (b.uget j hl) then scanU p b hs (j + 1) (by rw [toNat_add1 j (by omega)]; omega) else j
  else j
termination_by b.size - j.toNat
decreasing_by
  rw [toNat_add1 j (by omega)]; omega

theorem scanU_eq (p : UInt8 → Bool) (b : ByteArray) (hs : b.size < 4294967296) : ∀ k (j : USize) hj,
    b.size - j.toNat = k → (scanU p b hs j hj).toNat = scanGo p b k j.toNat
  | 0, j, hj, hk => by
    rw [scanU, dif_neg (fun h => by have : j.toNat < b.usize.toNat := h; rw [usize_eq b hs] at this; omega)]
    rfl
  | k + 1, j, hj, hk => by
    have hl : j.toNat < b.size := by omega
    rw [scanU, dif_pos (show j < b.usize from show j.toNat < b.usize.toNat by rw [usize_eq b hs]; exact hl),
      scanGo, getElem!_pos b j.toNat hl]
    dsimp only
    have hg : ∀ hl', b.uget j hl' = b[j.toNat] := fun _ => rfl
    simp only [hg]
    by_cases hb : p b[j.toNat] = true
    · rw [if_pos hb, if_pos (by simp [hl, hb]), scanU_eq p b hs k (j + 1) _ (by rw [toNat_add1 j (by omega)]; omega),
        toNat_add1 j (by omega)]
    · rw [if_neg hb, if_neg (by simp [hb])]

@[inline] def scanF (p : UInt8 → Bool) (b : ByteArray) (i : Nat) : Nat :=
  if h : i ≤ b.size ∧ b.size ≤ 4294967295 then
    (scanU p b (Nat.lt_succ_of_le h.2) i.toUSize (by rw [toNat_toUSize i (by omega)]; exact h.1)).toNat
  else scanGo p b (b.size - i) i

@[csimp] theorem scan_eqF : @scan = @scanF := by
  funext p b i
  unfold scan scanF
  split
  · rename_i h
    rw [scanU_eq p b (Nat.lt_succ_of_le h.2) (b.size - i) _ _ (by rw [toNat_toUSize i (by omega)]),
      toNat_toUSize i (by omega)]
  · rfl

@[inline] def nameP (c : UInt8) : Bool := c < 128 && c != 10 && c != 13
@[inline] def qualP (c : UInt8) : Bool := 33 ≤ c && c ≤ 126

theorem scan_nl (p : UInt8 → Bool) (hp : p 10 = false) (b : ByteArray) (i : Nat)
    (h1 : scan p b i < b.size) (h2 : b[scan p b i]! = 10) :
    findNewline b i = scan p b i ∧ ∀ j, i ≤ j → j < scan p b i → p b[j]! = true := by
  have hs := scanGo_spec p b (b.size - i) i (Nat.le_refl _)
  refine ⟨findNewline_at b i _ hs.1 h1 h2 (fun j a c e => ?_), hs.2.2.1⟩
  have := hs.2.2.1 j a c; rw [e, hp] at this; cases this

-- `parseFrom` with each line scanned once: the name, letter and quality tests run in the line scans. Anything
-- unusual (an invalid byte, a '+' line with a name, a short slice) goes to `parseFrom` itself (`parseFromF_eq`).
def parseFromF (b : ByteArray) (i : Nat) (acc : Array ReadB) : Except String (Array ReadB) :=
  if h : b.size ≤ i then .ok acc else
  let j1 := scan nameP b i
  let j2 := scan isBase b (j1 + 1)
  let j3 := findNewline b (j2 + 1)
  let j4 := scan qualP b (j3 + 1)
  if hc : j1 < b.size ∧ b[j1]! = 10 ∧ j2 < b.size ∧ b[j2]! = 10 ∧ j3 = j2 + 2 ∧ j4 < b.size ∧ b[j4]! = 10 ∧
      b[i]! = 64 ∧ 10 ≤ j1 - i ∧ j1 - i ≤ 501 ∧ j2 - (j1 + 1) ≤ 1000 ∧ b[j2 + 1]! = 43 ∧
      j4 - (j3 + 1) = j2 - (j1 + 1) then
    parseFromF b (j4 + 1) (acc.push ⟨b.extract (i + 1) j1, b.extract (j1 + 1) j2, b.extract (j3 + 1) j4⟩)
  else parseFrom b i acc
termination_by b.size - i
decreasing_by
  have a1 := (scanGo_spec nameP b (b.size - i) i (Nat.le_refl _)).1
  have a2 := (scanGo_spec isBase b (b.size - (scan nameP b i + 1)) (scan nameP b i + 1) (Nat.le_refl _)).1
  have a3 := findNewline_ge b (scan isBase b (scan nameP b i + 1) + 1)
  have a4 := (scanGo_spec qualP b (b.size - (findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1))
    (findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1) (Nat.le_refl _)).1
  have h4 : scan qualP b (findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1) < b.size := hc.2.2.2.2.2.1
  unfold scan at *
  omega

theorem parseFromF_eq (b : ByteArray) : ∀ n i (acc : Array ReadB), b.size - i = n →
    parseFromF b i acc = parseFrom b i acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i acc hn
  rw [parseFromF]
  by_cases h : b.size ≤ i
  · rw [dif_pos h, parseFrom, dif_pos h]
  rw [dif_neg h]
  dsimp only
  split
  · rename_i hc
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hc
    have s1 := scan_nl nameP rfl b i c1 c2
    have s2 := scan_nl isBase rfl b _ c3 c4
    have s4 := scan_nl qualP rfl b _ c6 c7
    have a1 : i ≤ scan nameP b i := (scanGo_spec nameP b (b.size - i) i (Nat.le_refl _)).1
    have a2 : scan nameP b i + 1 ≤ scan isBase b (scan nameP b i + 1) :=
      (scanGo_spec isBase b _ (scan nameP b i + 1) (Nat.le_refl _)).1
    have a4 : findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1 ≤
        scan qualP b (findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1) :=
      (scanGo_spec qualP b _ (findNewline b (scan isBase b (scan nameP b i + 1) + 1) + 1) (Nat.le_refl _)).1
    rw [ih _ (by omega) _ _ rfl]
    conv => rhs; rw [parseFrom]
    rw [dif_neg h]
    dsimp only
    rw [s1.1, s2.1, s4.1]
    generalize scan nameP b i = j1 at *
    generalize scan isBase b (j1 + 1) = j2 at *
    rw [c5] at *
    generalize scan qualP b (j2 + 2 + 1) = j4 at *
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have g0 : ∀ x y : Nat, x ≤ y → y ≤ b.size → (b.extract x y).size = y - x := fun x y h1 h2 => by
      rw [ByteArray.size_extract]; omega
    have gn : allBytes (fun c => c < 128 && c != 10 && c != 13) (b.extract i j1) = true :=
      allBytes_extract _ b i j1 (by omega) s1.2
    have gs : allBytes isBase (b.extract (j1 + 1) j2) = true := allBytes_extract _ b _ _ (by omega) s2.2
    have gq : allBytes (fun c => 33 ≤ c && c ≤ 126) (b.extract (j2 + 2 + 1) j4) = true :=
      allBytes_extract _ b _ _ (by omega) s4.2
    have n0 : (b.extract i j1)[0]! = 64 := by
      rw [getElem!_pos _ 0 (by rw [g0 i j1 a1 (by omega)]; omega), ByteArray.getElem_extract]
      rw [getElem!_pos b i (by omega)] at c8; simpa using c8
    have p0 : (b.extract (j2 + 1) (j2 + 2))[0]! = 43 := by
      rw [getElem!_pos _ 0 (by rw [g0 _ _ (by omega) (by omega)]; omega), ByteArray.getElem_extract]
      rw [getElem!_pos b _ (by omega)] at c12; simpa using c12
    have hr : recordError (b.extract i j1) (b.extract (j1 + 1) j2) (b.extract (j2 + 1) (j2 + 2))
        (b.extract (j2 + 2 + 1) j4) = none := by
      have e4 : findNewline b (j2 + 2 + 1) = j4 := s4.1
      unfold recordError
      simp only [g0 i j1 a1 (by omega), g0 _ _ a2 (by omega), g0 (j2 + 1) (j2 + 2) (by omega) (by omega),
        g0 _ _ a4 (by omega), n0, p0, gn, gs, gq]
      have q1 : 0 < j1 - i := by omega
      have q3 : j2 + 2 - (j2 + 1) = 1 := by omega
      simp [q1, c9, c10, c11, q3, c13]
    rw [hr]
    dsimp only
    have hx : (b.extract i j1).extract 1 (b.extract i j1).size = b.extract (i + 1) j1 := by
      rw [g0 i j1 a1 (by omega)]
      apply ByteArray.ext; simp only [ByteArray.data_extract, Array.extract_extract]
      congr 1 <;> omega
    rw [hx]
  · rfl

-- `parseFastqB` with the fused scans
@[inline] def parseFastqBF (b : ByteArray) : Except String (Array ReadB) := parseFromF b 0 #[]

@[csimp] theorem parseFastqB_eqF : @parseFastqB = @parseFastqBF := by
  funext b
  exact (parseFromF_eq b _ 0 #[] rfl).symm

end Spec
