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

def parse (bytes : List UInt8) : Option (List Read) := sorry

theorem parse_correct (bytes : List UInt8) :
    match parse bytes with
    | some reads => ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes ∧ records.map toRead = reads
    | none => ¬ ∃ records : List Record,
        (∀ r ∈ records, r.valid) ∧ records.flatMap toBytes = bytes := by
  sorry

end Spec.FQ
