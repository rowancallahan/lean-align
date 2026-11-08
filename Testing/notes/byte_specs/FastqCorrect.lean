/-! PROOF of `parse_correct` for a reference parser, against Rowan's locked spec `FastqSpec.lean` (definitions copied verbatim
below, up to `parse`). Standalone (core only): `lake env lean Testing/notes/byte_specs/FastqCorrect.lean`.
The reference parser here (`parseRec` = four `takeLine`s + the validity check; `parse` = repeat until the input is empty) is a
stand-in with the shape S-G's parser needs: the lemmas that do the work are `takeLine_append` (a valid record's fields have no
newline, so the lines split uniquely), `parseRec_complete` (`toBytes r ++ rest` parses back to `(r, rest)`) and `parseRec_sound`. -/
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

/-! ## The reference parser -/

instance (r : Record) : Decidable r.valid := by unfold Record.valid; infer_instance

-- the first line (without its newline) and what follows it; none if there is no newline
def takeLine : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | x :: xs => if x = newline then some ([], xs) else (takeLine xs).map fun (c, r) => (x :: c, r)

theorem takeLine_spec : ∀ (l c r : List UInt8), takeLine l = some (c, r) → l = c ++ newline :: r ∧ newline ∉ c
  | [], c, r, h => by simp [takeLine] at h
  | x :: xs, c, r, h => by
    unfold takeLine at h
    split at h
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := by simpa using h
      simp [hx]
    · rename_i hx
      cases hr : takeLine xs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨c', r'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih := takeLine_spec xs c' r' hr
        refine ⟨by rw [ih.1]; rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hx h.symm, ih.2⟩

theorem takeLine_append : ∀ (c r : List UInt8), newline ∉ c → takeLine (c ++ newline :: r) = some (c, r)
  | [], r, _ => by simp [takeLine]
  | x :: xs, r, h => by
    have hx : x ≠ newline := fun e => h (by simp [e])
    have ih := takeLine_append xs r (fun e => h (List.mem_cons_of_mem _ e))
    simp [takeLine, hx, ih]

def parseRec (bytes : List UInt8) : Option (Record × List UInt8) := do
  let (n, b1) ← takeLine bytes
  let (s, b2) ← takeLine b1
  let (p, b3) ← takeLine b2
  let (q, b4) ← takeLine b3
  let r : Record := ⟨n, s, p, q⟩
  if r.valid then some (r, b4) else none

theorem parseRec_sound {bytes rest : List UInt8} {r : Record} (h : parseRec bytes = some (r, rest)) :
    r.valid ∧ bytes = toBytes r ++ rest := by
  unfold parseRec at h
  cases h1 : takeLine bytes with
  | none => simp [h1] at h
  | some p1 =>
  obtain ⟨n, b1⟩ := p1
  cases h2 : takeLine b1 with
  | none => simp [h1, h2] at h
  | some p2 =>
  obtain ⟨s, b2⟩ := p2
  cases h3 : takeLine b2 with
  | none => simp [h1, h2, h3] at h
  | some p3 =>
  obtain ⟨p, b3⟩ := p3
  cases h4 : takeLine b3 with
  | none => simp [h1, h2, h3, h4] at h
  | some p4 =>
  obtain ⟨q, b4⟩ := p4
  simp [h1, h2, h3, h4] at h
  obtain ⟨hv, rfl, rfl⟩ := h
  refine ⟨hv, ?_⟩
  rw [(takeLine_spec _ _ _ h1).1, (takeLine_spec _ _ _ h2).1, (takeLine_spec _ _ _ h3).1, (takeLine_spec _ _ _ h4).1]
  simp [toBytes]

-- the key lemma: a valid record's bytes split back into exactly its four fields
theorem parseRec_complete {r : Record} (hv : r.valid) (rest : List UInt8) : parseRec (toBytes r ++ rest) = some (r, rest) := by
  have hv' := hv
  obtain ⟨_, _, _, _, hn, _, hs, _, hp, hpt, hq, _⟩ := hv'
  have hs' : newline ∉ r.sequence := fun h => by have := hs _ h; simp [bases, newline] at this
  have hq' : newline ∉ r.quality := fun h => by
    have := hq _ h
    simp only [qualityByte, newline, Bool.and_eq_true, decide_eq_true_eq] at this
    exact absurd this.1 (by decide)
  have hp' : newline ∉ r.plus := by
    intro h
    cases hh : r.plus with
    | nil => simp [hh] at hp
    | cons x xs =>
      rw [hh] at h hpt
      have hx : x = plusSign := by simpa [hh] using hp
      rcases List.mem_cons.1 h with h | h
      · exact absurd (h.trans hx) (by decide)
      · rcases hpt with hpt | hpt
        · simp at hpt; simp [hpt] at h
        · simp at hpt; rw [hpt] at h; exact hn (List.mem_of_mem_tail h)
  have e : toBytes r ++ rest = r.name ++ newline :: (r.sequence ++ newline :: (r.plus ++ newline :: (r.quality ++ newline :: rest))) := by
    simp [toBytes]
  unfold parseRec
  rw [e]
  simp [takeLine_append _ _ hn, takeLine_append _ _ hs', takeLine_append _ _ hp', takeLine_append _ _ hq', hv]

theorem parseRec_shorter {bytes rest : List UInt8} {r : Record} (h : parseRec bytes = some (r, rest)) :
    rest.length < bytes.length := by
  rw [(parseRec_sound h).2]
  simp [toBytes]
  omega

/-! ## `parse`: records until the input is empty -/

def parse (bytes : List UInt8) : Option (List Read) :=
  if bytes = [] then some [] else
  match hp : parseRec bytes with
  | some (r, rest) => (parse rest).map (toRead r :: ·)
  | none => none
termination_by bytes.length
decreasing_by exact parseRec_shorter hp

theorem parse_sound (n : Nat) : ∀ (bytes : List UInt8) (reads : List Read), bytes.length = n → parse bytes = some reads →
    ∃ records : List Record, (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes ∧ records.map toRead = reads := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bytes reads hn h
    rw [parse] at h
    by_cases hb : bytes = []
    · rw [if_pos hb] at h
      obtain rfl := Option.some.inj h
      exact ⟨[], by simp, by simp [hb], rfl⟩
    · rw [if_neg hb] at h
      split at h
      · rename_i r rest hp
        cases hr : parse rest with
        | none => simp [hr] at h
        | some reads' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          have hlt := parseRec_shorter hp
          obtain ⟨rs, hv, hf, hm⟩ := ih rest.length (by omega) rest reads' rfl hr
          obtain ⟨hrv, hbytes⟩ := parseRec_sound hp
          refine ⟨r :: rs, ?_, ?_, ?_⟩
          · intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exact hrv; exact hv x hx
          · rw [List.flatMap_cons, hf, hbytes]
          · rw [List.map_cons, hm]
      · simp at h

theorem parse_complete : ∀ records : List Record, (∀ r ∈ records, r.valid) → parse (records.flatMap toBytes) = some (records.map toRead)
  | [], _ => by simp [parse]
  | r :: rs, hv => by
    have hrv := hv r (by simp)
    have ih := parse_complete rs (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    have hne : toBytes r ++ rs.flatMap toBytes ≠ [] := by simp [toBytes]
    rw [List.flatMap_cons, parse, if_neg hne]
    split
    · rename_i r' rest hp
      rw [parseRec_complete hrv] at hp
      obtain ⟨rfl, rfl⟩ := by simpa using hp
      simp [ih]
    · rename_i hp
      rw [parseRec_complete hrv] at hp
      simp at hp

theorem parse_correct (bytes : List UInt8) :
    match parse bytes with
    | some reads => ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes ∧ records.map toRead = reads
    | none => ¬ ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes := by
  cases h : parse bytes with
  | some reads => exact parse_sound _ bytes reads rfl h
  | none =>
    rintro ⟨records, hv, hb⟩
    subst hb
    rw [parse_complete records hv] at h
    simp at h

#print axioms parse_correct

end FQ
