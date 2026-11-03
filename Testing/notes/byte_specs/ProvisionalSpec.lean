import Proofs.Sam
/-! PROVISIONAL, for Rowan to review (not built by lake, not part of Spec/): how `Spec/Fastq.lean` and `Spec/Sam.lean`
would change if the spec were over bytes. Check: `lake env lean Testing/notes/byte_specs/ProvisionalSpec.lean`.
Everything here is in `Spec.Provisional`, so `FastqRecord`, `parseRecord`, `trimRecord`, `samLines` ... below are the PROPOSED
versions; the current ones stay reachable as `_root_.Spec.*`. Lines marked `-- CHANGED` are the places where text differs from today.

What changes, in one paragraph:
1. `FastqRecord` is `{qname, letters, quality}`, all `ByteArray`. No `String` is built while reading. The QNAME rule (up to the first
   space, no trailing `/1` `/2`) lives in one function `qnameOf`, which replaces both `mateName` (Fastq) and `samName` (Sam), the
   same function today. `parseRecord` also does the checks `readChunk` does today (QNAME is a SAM name, SEQ and QUAL equally long).
2. The file as a whole is specified: `parseFastq bytes` (same `lines` / `parseLines` as FastqBytes.lean), `pairUp`, `pairsOfFiles`.
   Any reader (block reader, parallel slice parser) must return exactly the prefix of `pairsOfFiles` it is asked for.
3. `Spec/Sam.lean`: the String functions stay as the readable spec (`samLine`, `cigarText` ...). Three lines change (the record
   fields). The output file is `samFile ... : ByteArray`, defined as the UTF-8 of the readable text; a byte writer is proved equal to it.
STATUS: no `sorry`. Not proved: `qnameOf` = today's `samName`/`mateName` (they use the legacy `String.splitOn`, which has no
lemmas in core 4.35); it is `#guard`-tested on examples below. -/
namespace Spec.Provisional
open Spec

/-! ## 0. Small facts used below (ASCII bytes are valid UTF-8; copied from research/io2 `Proofs/SamBytes.lean`) -/

def Ascii (b : ByteArray) : Prop := ∀ x ∈ b.data.toList, x < 128

theorem utf8Encode_ascii (l : List UInt8) (h : ∀ x ∈ l, x < 128) :
    (l.map fun x => Char.ofNat x.toNat).utf8Encode = l.toByteArray := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x < 128 := h x (by simp)
    rw [List.map_cons, List.utf8Encode_cons, ih (fun y hy => h y (by simp [hy])), List.utf8Encode_singleton]
    have hn : x.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using hx
    have hv : Nat.isValidChar x.toNat := Or.inl (by omega)
    have hc : (Char.ofNat x.toNat).val.toNat = x.toNat := by
      simp [Char.ofNat, hv, Char.ofNatAux]
    have : String.utf8EncodeChar (Char.ofNat x.toNat) = [x] := by
      simp only [String.utf8EncodeChar, hc]
      rw [if_pos (by omega)]
      simp
    rw [this]
    exact (List.toByteArray_append (l := [x]) (l' := xs)).symm

theorem isValidUTF8_of_ascii (b : ByteArray) (h : Ascii b) : b.IsValidUTF8 :=
  .intro (b.data.toList.map fun x => Char.ofNat x.toNat) (by
    rw [utf8Encode_ascii _ h]
    apply ByteArray.ext
    simp [List.data_toByteArray])

-- the `String` view of ASCII bytes is lossless: this is why the String functions below can stay the readable spec
theorem fromUTF8!_toUTF8_ascii (b : ByteArray) (h : Ascii b) : (String.fromUTF8! b).toUTF8 = b := by
  unfold String.fromUTF8!
  rw [dif_pos (isValidUTF8_of_ascii b h)]
  rfl

theorem ascii_extract (b : ByteArray) (h : Ascii b) (s e : Nat) : Ascii (b.extract s e) := by
  intro x hx
  rw [ByteArray.data_extract] at hx
  simp only [Array.toList_extract] at hx
  exact h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem lt128 (x : UInt8) (h : x ≤ 126) : x < 128 := by
  rw [UInt8.le_iff_toNat_le] at h
  rw [UInt8.lt_iff_toNat_lt]
  have : (126 : UInt8).toNat = 126 := rfl
  have : (128 : UInt8).toNat = 128 := rfl
  omega

theorem ascii_empty : Ascii ByteArray.empty := fun x hx => by rw [ByteArray.data_empty] at hx; simp at hx

theorem ascii_of_allBytes (p : UInt8 → Bool) (hp : ∀ x, p x = true → x < 128) (b : ByteArray)
    (h : allBytes p b = true) : Ascii b := by
  have key : ∀ n, allBytesGo p b n = true → ∀ i, i < n → p b[i]! = true := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro h i hi
      simp only [allBytesGo, Bool.and_eq_true] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih h.2 i hi
      · exact h.1
  have h' : allBytesGo p b b.size = true := by rw [allBytesGo_eq]; exact h
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < b.size := by simpa using hi
  have := key b.size h' i hi'
  rw [getElem!_pos b i hi'] at this
  exact hp _ (by simpa [ByteArray.getElem_eq_getElem_data] using this)

/-! ## 1. Records over bytes (replaces the record, `mateName`, `parseRecord` and the checks in `readChunk` of Spec/Fastq.lean) -/

-- CHANGED: all fields are bytes, the name is the QNAME (see `qnameOf`)
structure FastqRecord where
  qname   : ByteArray
  letters : ByteArray
  quality : ByteArray

-- QNAME of a header (the text after '@'): up to the first space, without a trailing "/1" or "/2".
-- CHANGED: one function for what `mateName` (Fastq) and `samName` (Sam) both did on Strings.
def qnameOf (header : ByteArray) : ByteArray :=
  let base := header.data.toList.takeWhile (· != 32)
  ByteArray.mk (match base.reverse with
    | d :: 47 :: rest => if d == 49 || d == 50 then rest.reverse else base
    | _ => base).toArray

-- the characters SAM allows in a QNAME: '!'..'?' and 'A'..'~'
def isQnameByte (b : UInt8) : Bool := (33 ≤ b && b ≤ 63) || (65 ≤ b && b ≤ 126)

-- the four lines of a record, checked. CHANGED: also the checks `readChunk` does today (QNAME is a SAM name, SEQ and QUAL
-- have the same length), so that a record that `parseRecord` returns needs no further check, and the result has no String.
def parseRecord (header letters plus quality : ByteArray) : Except String FastqRecord :=
  let qname := qnameOf (header.extract 1 header.size)
  if !(0 < header.size && header[0]! == 64 && allBytes (fun b => 32 ≤ b && b ≤ 126) header) then
    .error "header line is not '@' + printable ASCII"
  else if !(0 < plus.size && plus[0]! == 43) then .error "third line of a record does not start with '+'"
  else if !allBytes isDnaByte letters then .error "letters other than A C G T N (lowercase, IUPAC)"
  else if !allBytes (fun b => 33 ≤ b && b ≤ 126) quality then .error "quality outside '!'..'~'"
  else if letters.size != quality.size then .error "sequence and quality lengths differ"
  else if !(0 < qname.size && qname.size ≤ 254 && allBytes isQnameByte qname) then .error "read name is not a SAM QNAME"
  else .ok { qname, letters, quality }

-- adapter cut, quality window, minimum length: as today, without the String round trip for the qualities
def trimRecord (record : FastqRecord) : FastqRecord :=   -- CHANGED: `record.quality` is bytes already
  let (letters, qual) := AdapterTrim.cutTruSeq record.letters record.quality
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  let (letters, qual) := AdapterTrim.dropShort minLength letters qual
  { record with letters, quality := qual }

/-! ## 2. The whole file (NEW; same `lines` / `parseLines` / `parseFastq` / `pairUp` as `FastqBytes.lean`, for the new record) -/

theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have hi : i < bs.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hi]
    simp [ByteArray.get!, Array.get!Internal_eq_getElem!, h]
  | case2 i r h =>
    have : bs.data.toList.length ≤ i := by simpa using h
    simp [List.drop_eq_nil_of_le this]

-- the lines of a file without their "\n" (or "\r\n"); a last line without "\n" counts, a final empty piece does not
def lines (bytes : ByteArray) : List ByteArray :=
  let ls := (bytes.toList.splitOn 10).map fun l =>
    ByteArray.mk (if l.getLast? = some 13 then l.dropLast else l).toArray
  if ls.getLast?.map (·.size) = some 0 then ls.dropLast else ls

def parseLines : List ByteArray → Except String (List FastqRecord)
  | [] => .ok []
  | header :: letters :: plus :: quality :: rest => do
      let record ← parseRecord header letters plus quality
      let records ← parseLines rest
      pure (record :: records)
  | _ => .error "file ends inside a record"

-- THE spec of reading: the records of a whole file, or the first error
def parseFastq (bytes : ByteArray) : Except String (List FastqRecord) := parseLines (lines bytes)

-- pairing: equal numbers of records, and the QNAMEs agree record by record
def pairUp (r1 r2 : List FastqRecord) : Except String (List (FastqRecord × FastqRecord)) :=
  if r1.length != r2.length then .error "FASTQ files out of step: different numbers of reads"
  else (r1.zip r2).mapM fun (x, y) =>
    if x.qname.data == y.qname.data then .ok (x, y) else .error "FASTQ files out of step: mate names differ"

-- what the shim's reading + `trimChunk` must produce, chunk by chunk: the pairs of the two files, trimmed, in order
def pairsOfFiles (f1 f2 : ByteArray) : Except String (List (FastqRecord × FastqRecord)) := do
  let pairs ← pairUp (← parseFastq f1) (← parseFastq f2)
  pure (pairs.map fun (a, b) => (trimRecord a, trimRecord b))

/-! ## 3. Facts about the new spec: what a parsed record satisfies, and the link to today's Spec -/

-- every record `parseRecord` returns is ASCII in all three fields (discharges `RecordAscii` of the byte SAM writer)
structure RecordAscii (r : FastqRecord) : Prop where
  qname : Ascii r.qname
  letters : Ascii r.letters
  quality : Ascii r.quality

theorem parseRecord_ascii {header letters plus quality : ByteArray} {r : FastqRecord}
    (h : parseRecord header letters plus quality = .ok r) : RecordAscii r := by
  unfold parseRecord at h
  dsimp only at h
  split at h
  · cases h
  rename_i c1
  split at h
  · cases h
  rename_i c2
  split at h
  · cases h
  rename_i c3
  split at h
  · cases h
  rename_i c4
  split at h
  · cases h
  rename_i c5
  split at h
  · cases h
  rename_i c6
  obtain rfl := Except.ok.inj h
  have hn : allBytes isDnaByte letters = true := by simpa using c3
  have hl : allBytes (fun b => 33 ≤ b && b ≤ 126) quality = true := by simpa using c4
  have hq : allBytes isQnameByte (qnameOf (header.extract 1 header.size)) = true := by
    have h6 := c6; simp [Bool.and_eq_true] at h6; exact h6.2
  refine ⟨?_, ?_, ?_⟩
  · exact ascii_of_allBytes _ (fun x hx => by
      simp only [isQnameByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
      rcases hx with hx | hx
      · exact lt128 x (UInt8.le_iff_toNat_le.2 (by
          have := UInt8.le_iff_toNat_le.1 hx.2
          have : (63 : UInt8).toNat = 63 := rfl
          have : (126 : UInt8).toNat = 126 := rfl
          omega))
      · exact lt128 x hx.2) _ hq
  · exact ascii_of_allBytes isDnaByte (fun x hx => by
      simp only [isDnaByte, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> decide) _ hn
  · exact ascii_of_allBytes _ (fun x hx => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      exact lt128 x hx.2) _ hl

theorem parseLines_ascii : ∀ (L : List ByteArray) (rs : List FastqRecord), parseLines L = .ok rs →
    ∀ r ∈ rs, RecordAscii r
  | [], rs, h, r, hr => by simp [parseLines] at h; subst h; simp at hr
  | header :: letters :: plus :: quality :: rest, rs, h, r, hr => by
    simp only [parseLines] at h
    cases hp : parseRecord header letters plus quality with
    | error e => simp [hp, bind, Except.bind] at h
    | ok record =>
      cases hq : parseLines rest with
      | error e => simp [hp, hq, bind, Except.bind] at h
      | ok rs' =>
        simp [hp, hq, bind, Except.bind, pure, Except.pure] at h
        subst h
        rcases List.mem_cons.1 hr with rfl | hr
        · exact parseRecord_ascii hp
        · exact parseLines_ascii rest rs' hq r hr
  | [_], rs, h, _, _ => by simp [parseLines] at h
  | [_, _], rs, h, _, _ => by simp [parseLines] at h
  | [_, _, _], rs, h, _, _ => by simp [parseLines] at h

-- every record of a file is ASCII
theorem parseFastq_ascii (bytes : ByteArray) (rs : List FastqRecord) (h : parseFastq bytes = .ok rs) :
    ∀ r ∈ rs, RecordAscii r := parseLines_ascii _ rs h

theorem ascii_dropShort (n : Nat) (l q : ByteArray) (hl : Ascii l) (hq : Ascii q) :
    Ascii (AdapterTrim.dropShort n l q).1 ∧ Ascii (AdapterTrim.dropShort n l q).2 := by
  unfold AdapterTrim.dropShort
  split
  · exact ⟨ascii_empty, ascii_empty⟩
  · exact ⟨hl, hq⟩

-- trimming only shortens (extract / empty), so it keeps ASCII
theorem trimRecord_ascii (r : FastqRecord) (h : RecordAscii r) : RecordAscii (trimRecord r) := by
  have hl : Ascii (AdapterTrim.cutTruSeq r.letters r.quality).1 := ascii_extract _ h.letters _ _
  have hq : Ascii (AdapterTrim.cutTruSeq r.letters r.quality).2 := ascii_extract _ h.quality _ _
  unfold trimRecord
  generalize AdapterTrim.cutTruSeq r.letters r.quality = p at hl hq
  obtain ⟨l1, q1⟩ := p
  simp only at hl hq ⊢
  cases ReadTrim.trimRead l1 q1 with
  | none => exact ⟨h.qname, (ascii_dropShort _ _ _ ascii_empty ascii_empty).1, (ascii_dropShort _ _ _ ascii_empty ascii_empty).2⟩
  | some se =>
    exact ⟨h.qname, (ascii_dropShort _ _ _ (ascii_extract _ hl _ _) (ascii_extract _ hq _ _)).1,
      (ascii_dropShort _ _ _ (ascii_extract _ hl _ _) (ascii_extract _ hq _ _)).2⟩

theorem mapM_same {α : Type} (xs : List α) (f : α → Except String α) (hf : ∀ x z, f x = .ok z → z = x) :
    ∀ ys, xs.mapM f = .ok ys → ys = xs := by
  induction xs with
  | nil => intro ys h; rw [List.mapM_nil] at h; exact (Except.ok.inj h).symm
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hfx : f x with
    | error e => simp [hfx, bind, Except.bind] at h
    | ok z =>
      cases hm : xs.mapM f with
      | error e => simp [hfx, hm, bind, Except.bind] at h
      | ok zs =>
        simp [hfx, hm, bind, Except.bind, pure, Except.pure] at h
        subst h
        rw [hf x z hfx, ih zs hm]

theorem pairUp_mem {r1 r2 : List FastqRecord} {ps : List (FastqRecord × FastqRecord)} (h : pairUp r1 r2 = .ok ps) :
    ∀ p ∈ ps, p.1 ∈ r1 ∧ p.2 ∈ r2 := by
  unfold pairUp at h
  split at h
  · cases h
  have := mapM_same _ _ (fun x z hz => by
    obtain ⟨a, b⟩ := x
    simp only at hz; split at hz
    · exact (Except.ok.inj hz).symm
    · cases hz) ps h
  subst this
  intro p hp
  exact List.of_mem_zip hp

-- the pairs of two files are ASCII too (what `samChunkB_eq` needs of every record it writes)
theorem pairsOfFiles_ascii (f1 f2 : ByteArray) (ps : List (FastqRecord × FastqRecord)) (h : pairsOfFiles f1 f2 = .ok ps) :
    ∀ p ∈ ps, RecordAscii p.1 ∧ RecordAscii p.2 := by
  unfold pairsOfFiles at h
  cases h1 : parseFastq f1 with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
  cases h2 : parseFastq f2 with
  | error e => simp [h1, h2, bind, Except.bind] at h
  | ok r2 =>
  cases hp : pairUp r1 r2 with
  | error e => simp [h1, h2, hp, bind, Except.bind] at h
  | ok pairs =>
    simp [h1, h2, hp, bind, Except.bind, pure, Except.pure] at h
    subst h
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
    have := pairUp_mem hp q hq
    exact ⟨trimRecord_ascii _ (parseFastq_ascii f1 r1 h1 _ this.1), trimRecord_ascii _ (parseFastq_ascii f2 r2 h2 _ this.2)⟩

/-! ### The link to today's `Spec.parseRecord`: same accept/reject on the common checks, same letters and qualities -/

theorem parseRecord_old {header letters plus quality : ByteArray} {r : FastqRecord}
    (h : parseRecord header letters plus quality = .ok r) :
    ∃ o, _root_.Spec.parseRecord header letters plus quality = .ok o ∧ o.letters = r.letters ∧
      o.quality = String.fromUTF8! r.quality := by
  unfold parseRecord at h
  dsimp only at h
  unfold _root_.Spec.parseRecord
  split at h
  · cases h
  rename_i c1
  rw [if_neg c1]
  split at h
  · cases h
  rename_i c2
  rw [if_neg c2]
  split at h
  · cases h
  rename_i c3
  rw [if_neg c3]
  split at h
  · cases h
  rename_i c4
  rw [if_neg c4]
  split at h
  · cases h
  split at h
  · cases h
  obtain rfl := Except.ok.inj h
  exact ⟨_, rfl, rfl, rfl⟩

/-! ### `qnameOf` against today's `mateName` / `samName` (legacy `String.splitOn`: no lemmas in core, so tested, not proved) -/

-- NOT a theorem: the one statement that ties the bytes to today's String functions. It is the hypothesis `hm.2.2` below.
def QnameAgrees : Prop := ∀ n : String, (n.toList.all fun c => c.toNat < 128) →
  (mateName n).toUTF8 = qnameOf n.toUTF8 ∧ (samName n).toUTF8 = qnameOf n.toUTF8

#guard ["r1/1 c", "r1/2", "r1", "/1", "/2", "a/1/1", "x/3", "", " a", "a b/1", "ab/1 /2", "a//1", "@x/1"].all fun n =>
  (mateName n).toUTF8.data == (qnameOf n.toUTF8).data && (samName n).toUTF8.data == (qnameOf n.toUTF8).data

/-! ## 4. SAM (Spec/Sam.lean). The String functions stay the readable spec; only what reads the record changes -/

-- CHANGED: record fields are bytes (`record.quality` needs no `toUTF8`)
def samSequence (record : FastqRecord) (strand : Strand) : String × String :=
  if record.letters.isEmpty then ("*", "*") else
  match strand with
  | .forward => (String.fromUTF8! record.letters, String.fromUTF8! record.quality)
  | .reverse => (String.fromUTF8! (reverseMapBytes complementByte record.letters),
                 String.fromUTF8! (reverseMapBytes id record.quality))

def mappedLine (chromosomes : ChromosomeList) (record : FastqRecord) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) : String :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let rname := (chromosomes[mate.placement.chromosome]?.map (·.1)).getD "*"
  let rnext := if mate.placement.chromosome = other.placement.chromosome then "=" else
    (chromosomes[other.placement.chromosome]?.map (·.1)).getD "*"
  let left := min mate.placement.start other.placement.start
  let right := max mate.placement.stop other.placement.stop
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then right - left else -((right - left : Nat) : Int)
  let (seq, qual) := samSequence record mate.placement.strand
  samLine (String.fromUTF8! record.qname) flag rname (mate.placement.start + 1) (mapq answer)   -- CHANGED: was `samName record.name`
    (cigarText mate.cigar) rnext (other.placement.start + 1) tlen seq qual
    (s!"AS:i:{mate.score}" :: answerTags answer)

def unmappedLine (record : FastqRecord) (which : Mate) (tags : List String) : String :=
  let flag := flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which
  let (seq, qual) := samSequence record .forward
  samLine (String.fromUTF8! record.qname) flag "*" 0 0 "*" "*" 0 0 seq qual tags   -- CHANGED: was `samName record.name`

def samLines (chromosomes : ChromosomeList) (record1 record2 : FastqRecord) (result : PairResult) :
    List String :=
  match result with
  | .trimmedAway mate =>
      let tags := [s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"]
      [unmappedLine record1 .one tags, unmappedLine record2 .two tags]
  | .aligned answer =>
      match answer.found with
      | some pair =>
          [mappedLine chromosomes record1 .one pair.mate1 pair.mate2 answer,
           mappedLine chromosomes record2 .two pair.mate2 pair.mate1 answer]
      | none =>
          [unmappedLine record1 .one (answerTags answer), unmappedLine record2 .two (answerTags answer)]

-- the output file: header, then every pair's lines in pair order, each line ended by "\n"; the bytes are the UTF-8 of this text
def linesBytes (lines : List String) : ByteArray := (String.join (lines.map (· ++ "\n"))).toUTF8

def samFile (chromosomes : ChromosomeList) (pairs : List ((FastqRecord × FastqRecord) × PairResult)) : ByteArray :=
  linesBytes (samHeader chromosomes) ++
    linesBytes (pairs.flatMap fun ((record1, record2), result) => samLines chromosomes record1 record2 result)

/-! ### The new SAM functions agree with today's when the old record carries the same data -/

-- `o` (today's record) holds what `r` holds: same letters, qualities as a String, and today's `samName` gives the QNAME
def Matches (r : FastqRecord) (o : _root_.Spec.FastqRecord) : Prop :=
  o.letters = r.letters ∧ o.quality = String.fromUTF8! r.quality ∧ _root_.Spec.samName o.name = String.fromUTF8! r.qname

theorem samSequence_matches (r : FastqRecord) (o : _root_.Spec.FastqRecord) (hm : Matches r o) (hq : Ascii r.quality)
    (strand : Strand) : samSequence r strand = _root_.Spec.samSequence o strand := by
  obtain ⟨hl, hq', _⟩ := hm
  unfold samSequence _root_.Spec.samSequence
  rw [hl, hq', fromUTF8!_toUTF8_ascii _ hq]
  rfl

theorem mappedLine_matches (chromosomes : ChromosomeList) (r : FastqRecord) (o : _root_.Spec.FastqRecord)
    (hm : Matches r o) (hq : Ascii r.quality) (which : Mate) (mate other : MateReport) (answer : PairAnswer) :
    mappedLine chromosomes r which mate other answer = _root_.Spec.mappedLine chromosomes o which mate other answer := by
  unfold mappedLine _root_.Spec.mappedLine
  rw [samSequence_matches r o hm hq, hm.2.2]

theorem unmappedLine_matches (r : FastqRecord) (o : _root_.Spec.FastqRecord) (hm : Matches r o) (hq : Ascii r.quality)
    (which : Mate) (tags : List String) :
    unmappedLine r which tags = _root_.Spec.unmappedLine o which tags := by
  unfold unmappedLine _root_.Spec.unmappedLine
  rw [samSequence_matches r o hm hq, hm.2.2]

theorem samLines_matches (chromosomes : ChromosomeList) (r1 r2 : FastqRecord) (o1 o2 : _root_.Spec.FastqRecord)
    (hm1 : Matches r1 o1) (hm2 : Matches r2 o2) (hq1 : Ascii r1.quality) (hq2 : Ascii r2.quality) (result : PairResult) :
    samLines chromosomes r1 r2 result = _root_.Spec.samLines chromosomes o1 o2 result := by
  cases result with
  | trimmedAway m =>
    simp only [samLines, _root_.Spec.samLines, unmappedLine_matches r1 o1 hm1 hq1, unmappedLine_matches r2 o2 hm2 hq2]
  | aligned a =>
    cases hf : a.found with
    | none =>
      simp only [samLines, _root_.Spec.samLines, hf, unmappedLine_matches r1 o1 hm1 hq1, unmappedLine_matches r2 o2 hm2 hq2]
    | some pair =>
      simp only [samLines, _root_.Spec.samLines, hf, mappedLine_matches chromosomes r1 o1 hm1 hq1,
        mappedLine_matches chromosomes r2 o2 hm2 hq2]

theorem linesBytes_append (l1 l2 : List String) : linesBytes (l1 ++ l2) = linesBytes l1 ++ linesBytes l2 := by
  unfold linesBytes
  induction l1 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.map_cons, String.join_cons, String.toUTF8_eq_toByteArray, String.toByteArray_append] at ih ⊢
    rw [ih]
    simp only [ByteArray.append_assoc]

-- writing chunk after chunk is writing the whole file (the chained writer is correct for any chunking)
theorem samFile_chunks (chromosomes : ChromosomeList)
    (chunks : List (List ((FastqRecord × FastqRecord) × PairResult))) :
    samFile chromosomes chunks.flatten =
      linesBytes (samHeader chromosomes) ++
        (chunks.map fun c => linesBytes (c.flatMap fun ((r1, r2), res) => samLines chromosomes r1 r2 res)).foldl (· ++ ·) ByteArray.empty := by
  unfold samFile
  congr 1
  have hfold : ∀ (bs : List ByteArray) (acc : ByteArray), bs.foldl (· ++ ·) acc = acc ++ bs.foldl (· ++ ·) ByteArray.empty := by
    intro bs
    induction bs with
    | nil => intro acc; simp [ByteArray.append_empty]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc ++ x), ih (ByteArray.empty ++ x), ByteArray.empty_append, ByteArray.append_assoc]
  induction chunks with
  | nil => simp [linesBytes]
  | cons c cs ih =>
    simp only [List.flatten_cons, List.flatMap_append, linesBytes_append, List.map_cons, List.foldl_cons, ih]
    rw [hfold _ (ByteArray.empty ++ _), ByteArray.empty_append]

#print axioms parseRecord_ascii
#print axioms parseLines_ascii
#print axioms trimRecord_ascii
#print axioms pairsOfFiles_ascii
#print axioms parseRecord_old
#print axioms samLines_matches
#print axioms samFile_chunks

end Spec.Provisional
