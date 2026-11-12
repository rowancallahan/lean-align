import FastqIO

namespace Spec.FQ

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

/-! ## `parse`: a state machine over the bytes

The bytes are read one at a time. `Field` says which line of the current record they belong to; a newline moves to
the next line, and the newline that ends the quality line finishes the record. At the end the file must stop
between records, and every record must be valid. -/

inductive Field where
  | name | sequence | plus | quality
  deriving DecidableEq

-- the line after this one (after the quality line: the next record's name)
def Field.next : Field → Field
  | .name => .sequence
  | .sequence => .plus
  | .plus => .quality
  | .quality => .name

def emptyRecord : Record := ⟨[], [], [], []⟩

-- the records finished so far, and the one being read
structure Parse where
  field   : Field
  current : Record
  done    : List Record

def emptyParse : Parse := ⟨.name, emptyRecord, []⟩

-- one byte
def step (p : Parse) (b : UInt8) : Parse :=
  match b == newline, p.field with
  | true, .quality => ⟨.name, emptyRecord, p.done ++ [p.current]⟩
  | true, f => { p with field := f.next }
  | false, .name => { p with current := { p.current with name := p.current.name ++ [b] } }
  | false, .sequence => { p with current := { p.current with sequence := p.current.sequence ++ [b] } }
  | false, .plus => { p with current := { p.current with plus := p.current.plus ++ [b] } }
  | false, .quality => { p with current := { p.current with quality := p.current.quality ++ [b] } }

instance (r : Record) : Decidable r.valid := by unfold Record.valid; infer_instance

def parse (bytes : List UInt8) : Option (List Read) :=
  let p := bytes.foldl step emptyParse
  if p.field = .name ∧ p.current.name = [] ∧ ∀ r ∈ p.done, r.valid then some (p.done.map toRead) else none

/-! ### `parse_correct` -/

-- the bytes of the record being read, up to here
def Parse.partial (p : Parse) : List UInt8 :=
  match p.field with
  | .name => p.current.name
  | .sequence => p.current.name ++ [newline] ++ p.current.sequence
  | .plus => p.current.name ++ [newline] ++ p.current.sequence ++ [newline] ++ p.current.plus
  | .quality => p.current.name ++ [newline] ++ p.current.sequence ++ [newline] ++ p.current.plus ++ [newline] ++
      p.current.quality

-- what has been read: the finished records' bytes, then the current one's
def Parse.read (p : Parse) : List UInt8 := p.done.flatMap toBytes ++ p.partial

-- the lines after the current one are still empty
def Parse.ok (p : Parse) : Prop :=
  match p.field with
  | .name => p.current.sequence = [] ∧ p.current.plus = [] ∧ p.current.quality = []
  | .sequence => p.current.plus = [] ∧ p.current.quality = []
  | .plus => p.current.quality = []
  | .quality => True

theorem step_read (p : Parse) (hp : p.ok) (b : UInt8) : (step p b).ok ∧ (step p b).read = p.read ++ [b] := by
  obtain ⟨f, ⟨n, s, l, q⟩, d⟩ := p
  unfold step
  by_cases hb : b = newline
  · subst hb
    cases f <;> simp_all [Parse.ok, Parse.read, Parse.partial, Field.next, emptyRecord, toBytes]
  · have : (b == newline) = false := by simpa using hb
    rw [this]
    cases f <;> simp_all [Parse.ok, Parse.read, Parse.partial]

theorem foldl_read (bytes : List UInt8) : ∀ p, p.ok → (bytes.foldl step p).read = p.read ++ bytes := by
  induction bytes with
  | nil => intro p _; simp
  | cons b bs ih =>
    intro p hp
    obtain ⟨h1, h2⟩ := step_read p hp b
    rw [List.foldl_cons, ih _ h1, h2]; simp

-- a line's bytes (no newline among them) only extend the current line
def addTo (f : Field) (r : Record) (l : List UInt8) : Record :=
  match f with
  | .name => { r with name := r.name ++ l }
  | .sequence => { r with sequence := r.sequence ++ l }
  | .plus => { r with plus := r.plus ++ l }
  | .quality => { r with quality := r.quality ++ l }

theorem foldl_line (l : List UInt8) (hl : newline ∉ l) : ∀ p : Parse,
    l.foldl step p = { p with current := addTo p.field p.current l } := by
  induction l with
  | nil => intro p; obtain ⟨f, ⟨n, s, l, q⟩, d⟩ := p; cases f <;> simp [addTo]
  | cons b bs ih =>
    intro p
    have hb : (b == newline) = false := by simp at hl ⊢; exact fun e => hl.1 e.symm
    have hbs : newline ∉ bs := fun h => hl (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons, ih hbs]
    obtain ⟨f, ⟨n, s, l, q⟩, d⟩ := p
    unfold step; rw [hb]
    cases f <;> simp [addTo]

theorem step_nl_name (c : Record) (d) : step ⟨.name, c, d⟩ newline = ⟨.sequence, c, d⟩ := rfl
theorem step_nl_sequence (c : Record) (d) : step ⟨.sequence, c, d⟩ newline = ⟨.plus, c, d⟩ := rfl
theorem step_nl_plus (c : Record) (d) : step ⟨.plus, c, d⟩ newline = ⟨.quality, c, d⟩ := rfl
theorem step_nl_quality (c : Record) (d) : step ⟨.quality, c, d⟩ newline = ⟨.name, emptyRecord, d ++ [c]⟩ := rfl

-- a record whose four lines have no newline is read as one record
theorem foldl_record (r : Record) (h1 : newline ∉ r.name) (h2 : newline ∉ r.sequence) (h3 : newline ∉ r.plus)
    (h4 : newline ∉ r.quality) (d : List Record) :
    (toBytes r).foldl step ⟨.name, emptyRecord, d⟩ = ⟨.name, emptyRecord, d ++ [r]⟩ := by
  obtain ⟨n, s, l, q⟩ := r
  simp only [toBytes, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_line _ h1]; simp only [addTo, emptyRecord, List.nil_append]; rw [step_nl_name]
  rw [foldl_line _ h2]; simp only [addTo, List.nil_append]; rw [step_nl_sequence]
  rw [foldl_line _ h3]; simp only [addTo, List.nil_append]; rw [step_nl_plus]
  rw [foldl_line _ h4]; simp only [addTo, List.nil_append]; rw [step_nl_quality]; rfl

theorem valid_no_newline (r : Record) (h : r.valid) :
    newline ∉ r.name ∧ newline ∉ r.sequence ∧ newline ∉ r.plus ∧ newline ∉ r.quality := by
  obtain ⟨hn, -, -, -, hnl, -, hs, -, hp, hpt, hq, -⟩ := h
  refine ⟨hnl, fun m => by have := hs _ m; simp [bases, newline] at this, ?_, fun m => by
    have := hq _ m; simp [qualityByte, newline] at this⟩
  intro m
  cases hpl : r.plus with
  | nil => simp [hpl] at hp
  | cons x xs =>
    rw [hpl] at hp m hpt
    simp at hp; subst hp
    rcases List.mem_cons.mp m with e | e
    · exact absurd e (by decide)
    · simp at hpt
      rcases hpt with rfl | rfl
      · simp at e
      · exact hnl (List.mem_of_mem_tail e)

theorem foldl_records (rs : List Record) (h : ∀ r ∈ rs, r.valid) : ∀ d,
    (rs.flatMap toBytes).foldl step ⟨.name, emptyRecord, d⟩ = ⟨.name, emptyRecord, d ++ rs⟩ := by
  induction rs with
  | nil => intro d; simp
  | cons r rs ih =>
    intro d
    obtain ⟨h1, h2, h3, h4⟩ := valid_no_newline r (h r (by simp))
    rw [List.flatMap_cons, List.foldl_append, foldl_record r h1 h2 h3 h4, ih (fun r m => h r (by simp [m]))]
    simp

-- every valid decomposition is the one `parse` finds
theorem parse_of_records (rs : List Record) (h : ∀ r ∈ rs, r.valid) :
    parse (rs.flatMap toBytes) = some (rs.map toRead) := by
  unfold parse
  have e := foldl_records rs h []
  simp only [emptyParse, e]
  simp [emptyRecord]
  exact h

theorem parse_correct (bytes : List UInt8) :
    match parse bytes with
    | some reads => ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes ∧ records.map toRead = reads
    | none => ¬ ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes := by
  split
  · rename_i reads hp
    unfold parse at hp
    dsimp only at hp
    split at hp
    · rename_i hc
      obtain ⟨hf, hn, hv⟩ := hc
      cases hp
      refine ⟨_, hv, ?_, rfl⟩
      have h := foldl_read bytes emptyParse (by simp [Parse.ok, emptyParse, emptyRecord])
      generalize bytes.foldl step emptyParse = q at hf hn hv h ⊢
      have e0 : emptyParse.read = [] := rfl
      have e1 : q.read = q.done.flatMap toBytes := by
        unfold Parse.read Parse.partial; rw [hf]; simp [hn]
      rw [e0, e1] at h
      simpa using h
    · cases hp
  · rename_i hp
    rintro ⟨rs, hv, rfl⟩
    rw [parse_of_records rs hv] at hp
    cases hp


/-! ## The byte parser the shim runs is `parse`

`Spec.parseFastqB` (Aligner/io/FastqIO.lean) cuts the bytes at newlines, four lines per record, checks each record
with `recordError` and keeps the reads as `ReadB`s. `parseFastqB_eq`: it fails exactly when `parse` does, and
otherwise returns the same reads. `parse_eq` (`@[csimp]`): `parse` runs as `parseFastqB`. -/

-- `toBytes` as four lines
theorem toBytes_lines (r : Record) (rest : List UInt8) : toBytes r ++ rest =
    r.name ++ newline :: (r.sequence ++ newline :: (r.plus ++ newline :: (r.quality ++ newline :: rest))) := by
  simp [toBytes]

-- a line ends at its first newline
theorem split_unique : ∀ (x x' y y' : List UInt8), newline ∉ x → newline ∉ x' →
    x ++ newline :: y = x' ++ newline :: y' → x = x' ∧ y = y'
  | [], [], y, y', _, _, h => by simpa using h
  | [], c :: x', y, y', _, h', h => by
    simp at h; exact absurd (List.mem_cons_self ..) (h.1 ▸ h')
  | c :: x, [], y, y', h0, _, h => by
    simp at h; exact absurd (List.mem_cons_self ..) (h.1.symm ▸ h0)
  | c :: x, c' :: x', y, y', h0, h', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e1, e2⟩ := split_unique x x' y y' (fun m => h0 (List.mem_cons_of_mem _ m))
      (fun m => h' (List.mem_cons_of_mem _ m)) h
    exact ⟨by rw [e1], e2⟩

-- a record's four lines are determined by the bytes, when no line has a newline
theorem toBytes_unique_nl (r r' : Record) (a : newline ∉ r.name ∧ newline ∉ r.sequence ∧ newline ∉ r.plus ∧
    newline ∉ r.quality) (b : newline ∉ r'.name ∧ newline ∉ r'.sequence ∧ newline ∉ r'.plus ∧
    newline ∉ r'.quality) (x y : List UInt8)
    (h : toBytes r ++ x = toBytes r' ++ y) : r = r' ∧ x = y := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  rw [toBytes_lines, toBytes_lines] at h
  obtain ⟨e1, h1⟩ := split_unique _ _ _ _ a1 b1 h
  obtain ⟨e2, h2⟩ := split_unique _ _ _ _ a2 b2 h1
  obtain ⟨e3, h3⟩ := split_unique _ _ _ _ a3 b3 h2
  obtain ⟨e4, h4⟩ := split_unique _ _ _ _ a4 b4 h3
  refine ⟨?_, h4⟩
  obtain ⟨_, _, _, _⟩ := r; obtain ⟨_, _, _, _⟩ := r'
  simp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

-- the first record of a valid decomposition is determined by the bytes
theorem toBytes_unique (r r' : Record) (hr : r.valid) (hr' : r'.valid) (x y : List UInt8)
    (h : toBytes r ++ x = toBytes r' ++ y) : r = r' ∧ x = y :=
  toBytes_unique_nl r r' (valid_no_newline r hr) (valid_no_newline r' hr') x y h

theorem parse_some (bytes : List UInt8) (reads : List Read) (h : parse bytes = some reads) :
    ∃ records : List Record, (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes ∧
      records.map toRead = reads := by
  have := parse_correct bytes
  rw [h] at this
  exact this

theorem parse_none (bytes : List UInt8) (h : ¬ ∃ records : List Record, (∀ r ∈ records, r.valid) ∧
    records.flatMap toBytes = bytes) : parse bytes = none := by
  cases hp : parse bytes with
  | none => rfl
  | some reads =>
    obtain ⟨rs, hv, hb, -⟩ := parse_some bytes reads hp
    exact absurd ⟨rs, hv, hb⟩ h

-- one valid record, then the rest
theorem parse_cons (r : Record) (hr : r.valid) (rest : List UInt8) :
    parse (toBytes r ++ rest) = (parse rest).map (toRead r :: ·) := by
  cases hp : parse rest with
  | some reads =>
    obtain ⟨rs, hv, rfl, rfl⟩ := parse_some rest reads hp
    have := parse_of_records (r :: rs) (fun x m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hr
      · exact hv x m)
    simpa using this
  | none =>
    apply parse_none
    rintro ⟨rs, hv, hb⟩
    cases rs with
    | nil => simp [toBytes] at hb
    | cons r' rs =>
      rw [List.flatMap_cons] at hb
      obtain ⟨rfl, hb2⟩ := toBytes_unique r' r (hv r' (by simp)) hr _ _ hb
      rw [← hb2, parse_of_records rs (fun x m => hv x (by simp [m]))] at hp
      cases hp

-- a non-empty valid file has a newline
theorem parse_no_newline (l : List UInt8) (hl : newline ∉ l) (hne : l ≠ []) : parse l = none := by
  apply parse_none
  rintro ⟨rs, hv, hb⟩
  cases rs with
  | nil => exact hne (by simpa using hb.symm)
  | cons r rs => rw [List.flatMap_cons, toBytes_lines] at hb; exact hl (hb ▸ by simp)

def readOfB (r : ReadB) : Read := ⟨r.name.data.toList, r.seq.data.toList, r.qual.data.toList⟩

-- the bytes of `b` from byte `i` on
def L (b : ByteArray) (i : Nat) : List UInt8 := b.data.toList.drop i

theorem L_cons (b : ByteArray) (i : Nat) (h : i < b.size) : L b i = b[i]! :: L b (i + 1) := by
  unfold L
  rw [List.drop_eq_getElem_cons (by simpa using h), getElem!_pos b i h, Array.getElem_toList,
    ← ByteArray.getElem_eq_getElem_data]

theorem L_size (b : ByteArray) (i : Nat) (h : b.size ≤ i) : L b i = [] := by
  unfold L; simp; simpa using h

theorem extract_list (b : ByteArray) (i j : Nat) : (b.extract i j).data.toList = (L b i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take]; rfl

theorem L_split (b : ByteArray) (i j : Nat) (h : i ≤ j) : L b i = (L b i).take (j - i) ++ L b j := by
  conv => lhs; rw [← List.take_append_drop (j - i) (L b i)]
  unfold L; rw [List.drop_drop, Nat.add_sub_cancel' h]

theorem findNewlineGo_spec (b : ByteArray) : ∀ k i, i ≤ b.size → b.size - i ≤ k →
    i ≤ findNewlineGo b k i ∧ findNewlineGo b k i ≤ b.size ∧
    newline ∉ (L b i).take (findNewlineGo b k i - i) ∧
    (findNewlineGo b k i < b.size → L b (findNewlineGo b k i) = newline :: L b (findNewlineGo b k i + 1))
  | 0, i, h1, h2 => by
    have : i = b.size := by omega
    subst this; simp [findNewlineGo]
  | k + 1, i, h1, h2 => by
    rw [findNewlineGo]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨hi, hb⟩ := hc
      obtain ⟨a1, a2, a3, a4⟩ := findNewlineGo_spec b k (i + 1) (by omega) (by omega)
      refine ⟨by omega, a2, ?_, a4⟩
      rw [L_cons b i hi, show findNewlineGo b k (i + 1) - i = (findNewlineGo b k (i + 1) - (i + 1)) + 1 by omega,
        List.take_succ_cons]
      intro m
      rcases List.mem_cons.mp m with e | e
      · exact hb (by rw [← e]; rfl)
      · exact a3 e
    · rename_i hc
      refine ⟨Nat.le_refl _, h1, by simp, ?_⟩
      intro hi
      rw [L_cons b i hi]
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
      rw [hc hi]; rfl

-- the line at `i`: it ends at the first newline, or runs to the end without one
theorem findNewline_line (b : ByteArray) (i : Nat) (h : i ≤ b.size) :
    i ≤ findNewline b i ∧ findNewline b i ≤ b.size ∧ newline ∉ (b.extract i (findNewline b i)).data.toList ∧
    (findNewline b i < b.size → L b i = (b.extract i (findNewline b i)).data.toList ++ newline :: L b (findNewline b i + 1)) ∧
    (b.size ≤ findNewline b i → newline ∉ L b i) := by
  obtain ⟨a1, a2, a3, a4⟩ := findNewlineGo_spec b (b.size - i) i h (Nat.le_refl _)
  have e : findNewline b i = findNewlineGo b (b.size - i) i := rfl
  rw [e, extract_list]
  refine ⟨a1, a2, a3, fun hl => ?_, fun hl => ?_⟩
  · rw [← a4 hl]; exact L_split b i _ a1
  · have := L_split b i _ a1
    rw [L_size b _ hl, List.append_nil] at this
    rw [this]; exact a3


/-! ### `recordError` is `Record.valid` -/

theorem allBytesGo_iff (p : UInt8 → Bool) (a : ByteArray) : ∀ n, allBytesGo p a n = true ↔ ∀ i < n, p a[i]! = true
  | 0 => by simp [allBytesGo]
  | n + 1 => by
    rw [allBytesGo, Bool.and_eq_true, allBytesGo_iff p a n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h; exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem allBytes_iff (p : UInt8 → Bool) (a : ByteArray) : allBytes p a = true ↔ ∀ x ∈ a.data.toList, p x = true := by
  rw [show allBytes p a = allBytesGo p a a.size from (allBytesGo_eq p a a.size).symm, allBytesGo_iff]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < a.size := by simpa using hi
    have := h i hi'
    rwa [getElem!_pos a i hi', ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList] at this
  · intro h i hi
    rw [getElem!_pos a i hi, ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList (by simpa using hi)]
    exact h _ (List.getElem_mem _)

theorem head_iff (a : ByteArray) (c : UInt8) : (0 < a.size && a[0]! == c) = true ↔ a.data.toList.head? = some c := by
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨h0, h1⟩ := h
    rw [getElem!_pos a 0 h0, ByteArray.getElem_eq_getElem_data] at h1
    rw [List.head?_eq_getElem? , Array.getElem?_toList, Array.getElem?_eq_getElem (by simpa using h0), h1]
  · intro h
    have h0 : 0 < a.data.toList.length := by
      cases e : a.data.toList with
      | nil => rw [e] at h; simp at h
      | cons _ _ => simp
    have h0' : 0 < a.size := by simpa using h0
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Array.getElem_toList] at h
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨h0', ?_⟩
    rw [getElem!_pos a 0 h0', ByteArray.getElem_eq_getElem_data, h]

theorem tail_list (a : ByteArray) : (a.extract 1 a.size).data.toList = a.data.toList.tail := by
  rw [extract_list]
  unfold L
  rw [List.drop_one, List.take_of_length_le (by simp)]

theorem ba_eq_iff (a c : ByteArray) : a = c ↔ a.data.toList = c.data.toList := by
  constructor
  · rintro rfl; rfl
  · intro h; exact ByteArray.ext (Array.toList_inj.mp h)

theorem ite_none (c : Bool) (m : String) (rest : Option String) :
    ((if (!c) = true then some m else rest) = none) ↔ c = true ∧ rest = none := by
  cases c <;> simp

theorem ite_last (a b : Nat) (m : String) : ((if (a != b) = true then some m else none) = none) ↔ a = b := by
  by_cases h : a = b <;> simp [h]

theorem recordError_none (name seq plus qual : ByteArray) :
    recordError name seq plus qual = none ↔
      Record.valid ⟨name.data.toList, seq.data.toList, plus.data.toList, qual.data.toList⟩ := by
  have hb : ∀ x : UInt8, isBase x = true ↔ x ∈ bases := by
    intro x; simp only [isBase, bases, Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.mem_nil_iff, or_false]
    constructor
    · rintro ((((h | h) | h) | h) | h) <;> simp [h]
    · rintro (h | h | h | h | h) <;> simp [h]
  have hn : (allBytes (fun b => b < 128 && b != 10 && b != 13) name = true) ↔
      (∀ b ∈ name.data.toList, ascii b) ∧ newline ∉ name.data.toList ∧ carriageReturn ∉ name.data.toList := by
    rw [allBytes_iff]
    constructor
    · intro h
      refine ⟨fun b m => by have := h b m; simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at this; simp [ascii, this.1.1],
        fun m => by have := h _ m; simp [newline] at this, fun m => by have := h _ m; simp [carriageReturn] at this⟩
    · rintro ⟨h1, h2, h3⟩ b m
      have := h1 b m
      simp only [ascii, decide_eq_true_eq] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨this, fun e => h2 (by subst e; exact m)⟩, fun e => h3 (by subst e; exact m)⟩
  have hs : allBytes isBase seq = true ↔ ∀ b ∈ seq.data.toList, b ∈ bases := by
    rw [allBytes_iff]; exact ⟨fun h b m => (hb b).mp (h b m), fun h b m => (hb b).mpr (h b m)⟩
  have hq : allBytes (fun b => 33 ≤ b && b ≤ 126) qual = true ↔ ∀ b ∈ qual.data.toList, qualityByte b := by
    rw [allBytes_iff]; rfl
  have hp : ∀ (_ : plus.data.toList.head? = some plusSign),
      (plus.size == 1 || decide (plus.extract 1 plus.size = name.extract 1 name.size)) = true ↔
      (plus.data.toList.tail = [] ∨ plus.data.toList.tail = name.data.toList.tail) := by
    intro h
    rw [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ba_eq_iff, tail_list, tail_list]
    have hl : plus.data.toList.length = plus.size := by simp
    cases e : plus.data.toList with
    | nil => rw [e] at h; simp at h
    | cons x xs =>
      rw [e] at hl
      simp only [List.tail_cons, List.length_cons] at hl ⊢
      constructor
      · rintro (h1 | h1)
        · left; exact List.eq_nil_of_length_eq_zero (by omega)
        · right; exact h1
      · rintro (h1 | h1)
        · left; subst h1; simp at hl; omega
        · right; exact h1
  have hc : recordError name seq plus qual = none ↔
      (0 < name.size && name[0]! == 64) = true ∧ (10 ≤ name.size ∧ name.size ≤ 501) ∧
      allBytes (fun b => b < 128 && b != 10 && b != 13) name = true ∧ allBytes isBase seq = true ∧
      seq.size ≤ 1000 ∧ (0 < plus.size && plus[0]! == 43) = true ∧
      (plus.size == 1 || decide (plus.extract 1 plus.size = name.extract 1 name.size)) = true ∧
      allBytes (fun b => 33 ≤ b && b ≤ 126) qual = true ∧ qual.size = seq.size := by
    unfold recordError
    simp only [ite_none, ite_last]
    have e1 : (decide (10 ≤ name.size) && decide (name.size ≤ 501)) = true ↔ (10 ≤ name.size ∧ name.size ≤ 501) := by
      simp
    rw [e1, decide_eq_true_eq]
  rw [hc, head_iff, head_iff, hn, hs, hq]
  unfold Record.valid
  simp only [Array.length_toList, ByteArray.size_data]
  constructor
  · rintro ⟨a1, ⟨a2, a3⟩, ⟨a4, a5, a6⟩, a7, a8, a9, a10, a11, a12⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, (hp a9).mp a10, a11, a12⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
    exact ⟨a1, ⟨a2, a3⟩, ⟨a4, a5, a6⟩, a7, a8, a9, (hp a9).mpr a10, a11, a12⟩

/-! ### `parseFrom` is `parse` on the rest of the bytes -/

theorem L_ne_nil (b : ByteArray) (i : Nat) (h : i < b.size) : L b i ≠ [] := by
  rw [L_cons b i h]; simp

theorem nl_mem_toBytes (r : Record) (rest : List UInt8) : newline ∈ toBytes r ++ rest := by
  rw [toBytes_lines]; simp

theorem parse_some_lines (l : List UInt8) (reads : List Read) (h : parse l = some reads) (hne : l ≠ []) :
    ∃ (r : Record) (rs : List Record), r.valid ∧ (∀ x ∈ rs, x.valid) ∧
      l = r.name ++ newline :: (r.sequence ++ newline :: (r.plus ++ newline :: (r.quality ++ newline ::
        rs.flatMap toBytes))) ∧ reads = toRead r :: rs.map toRead := by
  obtain ⟨rs, hv, hb, hr⟩ := parse_some l reads h
  cases rs with
  | nil => exact absurd hb.symm (by simpa using hne)
  | cons r rs =>
    refine ⟨r, rs, hv r (by simp), fun x m => hv x (by simp [m]), ?_, hr.symm⟩
    rw [← hb, List.flatMap_cons, toBytes_lines]

theorem parseFrom_eq (b : ByteArray) : ∀ n i (acc : Array ReadB), b.size - i = n →
    (parseFrom b i acc).toOption.map (·.toList.map readOfB) = (parse (L b i)).map (acc.toList.map readOfB ++ ·) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i acc hn
  rw [parseFrom]
  split
  · rename_i h
    rw [L_size b i h, show parse [] = some [] from parse_of_records [] (by simp)]
    simp [Except.toOption]
  · rename_i h
    have hi : i < b.size := by omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := findNewline_line b i (by omega)
    generalize hj1 : findNewline b i = j1 at a1 a2 a3 a4 a5
    dsimp only
    by_cases c1 : b.size ≤ j1
    · rw [if_pos c1, parse_no_newline _ (a5 c1) (L_ne_nil b i hi)]; rfl
    rw [if_neg c1]
    have e1 := a4 (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := findNewline_line b (j1 + 1) (by omega)
    generalize hj2 : findNewline b (j1 + 1) = j2 at b1 b2 b3 b4 b5
    by_cases c2 : b.size ≤ j2
    · rw [if_pos c2]
      cases hP : parse (L b i) with
      | none => rfl
      | some reads =>
        obtain ⟨r, rs, hr, -, hl, -⟩ := parse_some_lines _ reads hP (L_ne_nil b i hi)
        have n := valid_no_newline r hr
        rw [e1] at hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ a3 n.1 hl
        exact absurd (by rw [hl]; simp) (b5 c2)
    rw [if_neg c2]
    have e2 := b4 (by omega)
    obtain ⟨d1, d2, d3, d4, d5⟩ := findNewline_line b (j2 + 1) (by omega)
    generalize hj3 : findNewline b (j2 + 1) = j3 at d1 d2 d3 d4 d5
    by_cases c3 : b.size ≤ j3
    · rw [if_pos c3]
      cases hP : parse (L b i) with
      | none => rfl
      | some reads =>
        obtain ⟨r, rs, hr, -, hl, -⟩ := parse_some_lines _ reads hP (L_ne_nil b i hi)
        have n := valid_no_newline r hr
        rw [e1, e2] at hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ a3 n.1 hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ b3 n.2.1 hl
        exact absurd (by rw [hl]; simp) (d5 c3)
    rw [if_neg c3]
    have e3 := d4 (by omega)
    obtain ⟨f1, f2, f3, f4, f5⟩ := findNewline_line b (j3 + 1) (by omega)
    generalize hj4 : findNewline b (j3 + 1) = j4 at f1 f2 f3 f4 f5
    by_cases c4 : b.size ≤ j4
    · rw [if_pos c4]
      cases hP : parse (L b i) with
      | none => rfl
      | some reads =>
        obtain ⟨r, rs, hr, -, hl, -⟩ := parse_some_lines _ reads hP (L_ne_nil b i hi)
        have n := valid_no_newline r hr
        rw [e1, e2, e3] at hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ a3 n.1 hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ b3 n.2.1 hl
        obtain ⟨-, hl⟩ := split_unique _ _ _ _ d3 n.2.2.1 hl
        exact absurd (by rw [hl]; simp) (f5 c4)
    rw [if_neg c4]
    have e4 := f4 (by omega)
    -- the four lines make one record
    have hL : L b i = toBytes ⟨(b.extract i j1).data.toList, (b.extract (j1 + 1) j2).data.toList,
        (b.extract (j2 + 1) j3).data.toList, (b.extract (j3 + 1) j4).data.toList⟩ ++ L b (j4 + 1) := by
      rw [toBytes_lines, e1, e2, e3, e4]
    split
    · rename_i why hw
      cases hP : parse (L b i) with
      | none => rfl
      | some reads =>
        obtain ⟨r, rs, hr, -, hl, -⟩ := parse_some_lines _ reads hP (L_ne_nil b i hi)
        rw [← toBytes_lines, hL] at hl
        obtain ⟨hR, -⟩ := toBytes_unique_nl _ r ⟨a3, b3, d3, f3⟩ (valid_no_newline r hr) _ _ hl
        rw [← hR] at hr
        rw [(recordError_none _ _ _ _).mpr hr] at hw
        cases hw
    · rename_i hw
      have hv := (recordError_none _ _ _ _).mp hw
      rw [ih (b.size - (j4 + 1)) (by omega) (j4 + 1) _ rfl, hL, parse_cons _ hv]
      cases parse (L b (j4 + 1)) with
      | none => rfl
      | some reads =>
        simp only [Option.map_some, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append, Option.some.injEq]
        congr 2
        simp only [readOfB, toRead, tail_list]

/-- **The shim's byte parser is the spec's parser**: it fails exactly when `parse` does (no valid records make up
the bytes), and otherwise returns the same reads, in order. -/
theorem parseFastqB_eq (b : ByteArray) :
    (parseFastqB b).toOption.map (·.toList.map readOfB) = parse b.data.toList := by
  have := parseFrom_eq b _ 0 #[] rfl
  simp only [List.map_nil, List.nil_append, Option.map_id'] at this
  exact this

-- `parse` for the compiled code: the byte parser on the same bytes
def parseF (bytes : List UInt8) : Option (List Read) :=
  (parseFastqB ⟨bytes.toArray⟩).toOption.map (·.toList.map readOfB)

@[csimp] theorem parse_eq : @parse = @parseF := by
  funext bytes
  unfold parseF
  rw [parseFastqB_eq]

end Spec.FQ

#print axioms Spec.FQ.parse_correct
#print axioms Spec.FQ.parseFastqB_eq
