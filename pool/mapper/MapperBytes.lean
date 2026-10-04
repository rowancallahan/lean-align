import MapSpec

/-!
Byte genome: one `ByteArray` per chromosome, byte = `Char.val`.  Lemmas
linking `windowSeq` to byte slices, and the 2-bit word code
(A0 C1 G2 T3, any other letter 0) with its rolling-update lemma.
-/

namespace MapSpec

/-! ## Bytes ↔ letters -/

/-- The letter with code point `b`. -/
def toChar (b : UInt8) : Char :=
  ⟨b.toUInt32, Or.inl (by
    have := b.toNat_lt
    show b.toUInt32.toNat < 55296
    rw [UInt8.toNat_toUInt32]; omega)⟩

theorem toChar_val_toNat (b : UInt8) : (toChar b).val.toNat = b.toNat :=
  UInt8.toNat_toUInt32 b

def decodeBytes (B : ByteArray) : List Char := B.data.toList.map toChar

theorem length_decodeBytes (B : ByteArray) : (decodeBytes B).length = B.size := by
  rcases B with ⟨bs⟩
  simp only [decodeBytes, List.length_map, Array.length_toList]
  rfl

theorem getElem_decodeBytes (B : ByteArray) (i : Nat) (h : i < (decodeBytes B).length) :
    (decodeBytes B)[i] = toChar (B.get! i) := by
  rw [length_decodeBytes] at h
  rcases B with ⟨bs⟩
  have h' : i < bs.size := h
  simp only [decodeBytes, List.getElem_map, Array.getElem_toList, ByteArray.get!]
  rw [getElem!_pos bs i h']

structure ByteChrom where
  name : String
  bytes : ByteArray
deriving Inhabited

/-- One `ByteArray` per chromosome. -/
abbrev ByteGenome := Array ByteChrom

def decodeGenome (gb : ByteGenome) : Genome :=
  gb.toList.map fun bc => { name := bc.name, seq := decodeBytes bc.bytes }

/-- Every letter of the genome is a single byte. -/
def AsciiGenome (g : Genome) : Prop :=
  ∀ chromosome ∈ g, ∀ ch ∈ chromosome.seq, ch.val.toNat < 256

def encodeGenome (g : Genome) : ByteGenome :=
  (g.map fun c => ({ name := c.name, bytes := (c.seq.map fun ch => ch.val.toUInt8).toByteArray } : ByteChrom)).toArray

theorem toChar_toUInt8 (ch : Char) (h : ch.val.toNat < 256) : toChar ch.val.toUInt8 = ch := by
  apply Char.ext
  apply UInt32.toNat_inj.mp
  show ch.val.toUInt8.toUInt32.toNat = ch.val.toNat
  rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8]
  omega

theorem decodeBytes_toByteArray (s : List Char) (h : ∀ ch ∈ s, ch.val.toNat < 256) :
    decodeBytes (s.map fun ch => ch.val.toUInt8).toByteArray = s := by
  simp only [decodeBytes, List.data_toByteArray, List.toList_toArray, List.map_map]
  conv => rhs; rw [← List.map_id s]
  apply List.map_congr_left
  intro ch hch
  exact toChar_toUInt8 ch (h ch hch)

/-- An ASCII genome survives the byte encoding. -/
theorem decodeGenome_encodeGenome (g : Genome) (h : AsciiGenome g) :
    decodeGenome (encodeGenome g) = g := by
  simp only [decodeGenome, encodeGenome, List.toList_toArray, List.map_map]
  conv => rhs; rw [← List.map_id g]
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp, id]
  rw [decodeBytes_toByteArray c.seq (h c hc)]

theorem getElem?_decodeGenome (gb : ByteGenome) (c : Nat) :
    (decodeGenome gb)[c]? = if h : c < gb.size then
      some { name := gb[c].name, seq := decodeBytes gb[c].bytes } else none := by
  unfold decodeGenome
  split
  · next h => simp [h]
  · next h => simp; omega

/-- **Windows are byte slices.**  A window of the decoded genome is the
letters of bytes `start .. start+len` of its chromosome. -/
theorem windowSeq_decodeGenome (gb : ByteGenome) (w : Window) :
    windowSeq (decodeGenome gb) w =
      if h : w.chr < gb.size then
        if w.start + w.len ≤ gb[w.chr].bytes.size then
          some ((List.range w.len).map fun i => toChar (gb[w.chr].bytes.get! (w.start + i)))
        else none
      else none := by
  unfold windowSeq
  rw [getElem?_decodeGenome]
  by_cases hc : w.chr < gb.size
  · simp only [hc, dite_true, length_decodeBytes]
    split
    · next hfit =>
      congr 1
      apply List.ext_getElem
      · simp [length_decodeBytes]; omega
      · intro i h1 h2
        simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
        rw [getElem_decodeBytes]
    · rfl
  · simp [hc]

/-! ## 2-bit word codes -/

def codeNat (n : Nat) : Nat :=
  if n = 67 then 1 else if n = 71 then 2 else if n = 84 then 3 else 0

/-- A0 C1 G2 T3, anything else 0. -/
def charCode (ch : Char) : Nat := codeNat ch.val.toNat

@[inline] def byteCode (b : UInt8) : Nat :=
  if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 0

theorem byteCode_eq_codeNat (b : UInt8) : byteCode b = codeNat b.toNat := by
  have h : ∀ k : UInt8, (b == k) = decide (b.toNat = k.toNat) := fun k => by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact ⟨fun h => h ▸ rfl, UInt8.toNat_inj.mp⟩
  simp only [byteCode, codeNat, h, decide_eq_true_eq]
  rfl

theorem codeNat_lt (n : Nat) : codeNat n < 4 := by
  unfold codeNat; split <;> (try split) <;> (try split) <;> omega

theorem charCode_toChar (b : UInt8) : charCode (toChar b) = byteCode b := by
  simp only [charCode, byteCode_eq_codeNat, toChar_val_toNat]

def codeStep (h : Nat) (ch : Char) : Nat := h * 4 + charCode ch

/-- Base-4 number of a word, first letter most significant. -/
def codeOfWord (w : List Char) : Nat := w.foldl codeStep 0

theorem foldl_codeStep (a : Nat) (w : List Char) :
    w.foldl codeStep a = a * 4 ^ w.length + codeOfWord w := by
  induction w generalizing a with
  | nil => simp [codeOfWord]
  | cons x w ih =>
    simp only [List.foldl_cons, codeOfWord, List.length_cons]
    rw [ih, ih (codeStep 0 x)]
    simp only [codeStep, Nat.pow_succ, Nat.add_mul, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mul_assoc, Nat.mul_comm 4, Nat.add_assoc]

theorem codeOfWord_cons (x : Char) (w : List Char) :
    codeOfWord (x :: w) = charCode x * 4 ^ w.length + codeOfWord w := by
  rw [codeOfWord, List.foldl_cons, foldl_codeStep]
  simp [codeStep]

theorem codeOfWord_append (w : List Char) (x : Char) :
    codeOfWord (w ++ [x]) = codeOfWord w * 4 + charCode x := by
  simp [codeOfWord, List.foldl_append, codeStep]

theorem codeOfWord_lt (w : List Char) : codeOfWord w < 4 ^ w.length := by
  induction w with
  | nil => simp [codeOfWord]
  | cons x w ih =>
    rw [codeOfWord_cons, List.length_cons, Nat.pow_succ]
    have h1 : charCode x ≤ 3 := Nat.le_of_lt_succ (codeNat_lt _)
    have h2 := Nat.mul_le_mul_right (4 ^ w.length) h1
    omega

/-- The word of `l0` letters at `p`. -/
def wordAt (L : List Char) (l0 p : Nat) : List Char := (L.drop p).take l0

/-- **Rolling update.**  The code of the next word from the code of this one. -/
theorem codeOfWord_wordAt_succ (L : List Char) (l0 p : Nat) (hl : 0 < l0) (hp : p + l0 < L.length) :
    codeOfWord (wordAt L l0 (p + 1)) =
      (codeOfWord (wordAt L l0 p) * 4 + charCode L[p + l0]) % 4 ^ l0 := by
  obtain ⟨m, rfl⟩ : ∃ m, l0 = m + 1 := ⟨l0 - 1, by omega⟩
  let mid := (L.drop (p + 1)).take m
  have hmid : mid.length = m := by simp [mid]; omega
  have h1 : wordAt L (m + 1) p = L[p] :: mid := by
    simp only [wordAt, mid]
    rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
  have h2 : wordAt L (m + 1) (p + 1) = mid ++ [L[p + (m + 1)]] := by
    simp only [wordAt, mid]
    rw [List.take_add_one, List.getElem?_drop]
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    congr 3
    omega
  rw [h1, h2, codeOfWord_append, codeOfWord_cons, hmid]
  have hlt := codeOfWord_lt mid
  rw [hmid] at hlt
  have hc := codeNat_lt (L[p + (m + 1)]).val.toNat
  have hlt2 : codeOfWord mid * 4 + charCode L[p + (m + 1)] < 4 ^ (m + 1) := by
    rw [Nat.pow_succ]; simp only [charCode]; omega
  have he : (charCode L[p] * 4 ^ m + codeOfWord mid) * 4 + charCode L[p + (m + 1)] =
      (codeOfWord mid * 4 + charCode L[p + (m + 1)]) + 4 ^ (m + 1) * charCode L[p] := by
    simp only [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]; omega
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]

/-- Code of the first `l0` letters of a byte string. -/
def initCode (B : ByteArray) (l0 : Nat) : Nat :=
  (List.range l0).foldl (fun h i => h * 4 + byteCode (B.get! i)) 0

/-- Code of the `l0` letters at `p` of a byte string, computed from the bytes. -/
def byteWordCode (B : ByteArray) (p l0 : Nat) : Nat :=
  (List.range l0).foldl (fun h i => h * 4 + byteCode (B.get! (p + i))) 0

theorem wordAt_decodeBytes (B : ByteArray) (p l0 : Nat) (h : p + l0 ≤ B.size) :
    wordAt (decodeBytes B) l0 p = (List.range l0).map fun i => toChar (B.get! (p + i)) := by
  apply List.ext_getElem
  · simp [wordAt, length_decodeBytes]; omega
  · intro i h1 h2
    simp only [wordAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [getElem_decodeBytes]

theorem byteWordCode_eq (B : ByteArray) (p l0 : Nat) (h : p + l0 ≤ B.size) :
    byteWordCode B p l0 = codeOfWord (wordAt (decodeBytes B) l0 p) := by
  rw [wordAt_decodeBytes B p l0 h, codeOfWord, List.foldl_map]
  simp only [byteWordCode, codeStep, charCode_toChar]

theorem initCode_eq (B : ByteArray) (l0 : Nat) (h : l0 ≤ B.size) :
    initCode B l0 = codeOfWord (wordAt (decodeBytes B) l0 0) := by
  rw [← byteWordCode_eq B 0 l0 (by omega)]
  simp [initCode, byteWordCode]

end MapSpec
