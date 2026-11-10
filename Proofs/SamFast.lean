import Proofs.Sam
import Proofs.SamBytes

/-! # The byte SAM writer is `SamSpec.samFile`

`samLinesS` / `samChunkS` / `samHeaderB`: the old shim byte writer (`samLines`, removed) without the XT tier
tag, and with the spec's TLEN (`max stop − min start` as a `Nat`). Proved equal to the spec's bytes:
* `samHeaderB_eq`: the header bytes are `SamSpec.header`;
* `samChunkS_eq`: a chunk's bytes are `SamSpec.body` of its pairs (as `FQ.Read`s, `ReadB.toRead`) and results;
* `samFileS_eq`: header then the chunks, in order, is `SamSpec.samFile`. -/

namespace Spec

/-! ## The writer -/

-- XB best possible pair score, XU uniqueness (the spec has no XT tier tag)
def answerTagsS (answer : PairAnswer) : List String :=
  [s!"XB:i:{answer.bestPossibleScore}", s!"XU:Z:{uniquenessText answer.uniqueness}"]

-- a mate of a found pair (as `mappedLine`, TLEN as in the spec)
def mappedLineS (b : ByteArray) (chromosomes : ChromosomeList) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) : ByteArray :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let rname := (chromosomes[mate.placement.chromosome]?.map (·.1)).getD "*"
  let rnext := if mate.placement.chromosome = other.placement.chromosome then "=" else
    (chromosomes[other.placement.chromosome]?.map (·.1)).getD "*"
  let span : Nat := max mate.placement.stop other.placement.stop - min mate.placement.start other.placement.start
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then (span : Int) else -(span : Int)
  let (seq, qual) := samSequence read mate.placement.strand
  samLine b (qnameB read.name) flag rname (mate.placement.start + 1) (mapq answer)
    (cigarText mate.cigar) rnext (other.placement.start + 1) tlen seq qual
    (s!"AS:i:{mate.score}" :: answerTagsS answer)

-- the two SAM lines of one pair (as `samLines`, without XT tier)
def samLinesS (b : ByteArray) (chromosomes : ChromosomeList) (read1 read2 : ReadB) (result : PairResult) :
    ByteArray :=
  match result with
  | .trimmedAway mate =>
      let tags := [s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"]
      (unmappedLine ((unmappedLine b read1 .one tags).push 10) read2 .two tags).push 10
  | .aligned answer =>
      match answer.found with
      | some pair =>
          (mappedLineS ((mappedLineS b chromosomes read1 .one pair.mate1 pair.mate2 answer).push 10)
            chromosomes read2 .two pair.mate2 pair.mate1 answer).push 10
      | none =>
          (unmappedLine ((unmappedLine b read1 .one (answerTagsS answer)).push 10) read2 .two
            (answerTagsS answer)).push 10

-- one chunk's SAM text, in pair order
def samChunkS (chromosomes : ChromosomeList) (chunk : Array (ReadB × ReadB)) (results : List PairResult) : ByteArray :=
  (chunk.zip results.toArray).foldl (init := ByteArray.empty)
    fun bytes ((read1, read2), result) => samLinesS bytes chromosomes read1 read2 result

-- the header lines, each with its newline
def samHeaderB (chromosomes : ChromosomeList) : ByteArray :=
  (samHeader chromosomes).foldl (fun b l => (b ++ l.toUTF8).push 10) ByteArray.empty

/-! ## Bytes as lists -/

namespace SamFast

theorem toList_loop (b : ByteArray) : ∀ k i r, b.size - i = k →
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i
  | 0, i, r, h => by
    have hs : b.size = b.data.toList.length := by rw [Array.length_toList]; rfl
    rw [ByteArray.toList.loop, if_neg (by omega), List.drop_eq_nil_of_le (by omega)]; simp
  | k + 1, i, r, h => by
    have hs : b.size = b.data.toList.length := by rw [Array.length_toList]; rfl
    rw [ByteArray.toList.loop, if_pos (by omega), toList_loop b k (i + 1) _ (by omega)]
    have hi : i < b.data.toList.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    have e : b.get! i = b.data.toList[i] := by
      show b.data[i]! = _
      rw [getElem!_pos b.data i (by rw [← Array.length_toList]; exact hi)]; simp
    rw [e]; simp

theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  rw [ByteArray.toList, toList_loop b _ 0 [] rfl]; simp

theorem text_eq (s : String) : SamSpec.text s = s.toUTF8.data.toList := by
  unfold SamSpec.text; rw [toList_eq]

theorem push_append (b c : ByteArray) (x : UInt8) : (b ++ c).push x = b ++ c.push x := by
  rw [← ByteArray.append_toByteArray_singleton, ← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc]

theorem digit_bytes (d : Nat) (h : d < 10) :
    (String.ofList [Nat.digitChar d]).toByteArray = [48 + d.toUInt8].toByteArray := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pushNat_eq (n : Nat) : ∀ b : ByteArray, pushNat b n = b ++ (toString n).toUTF8 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro b
    rw [pushNat]
    split
    · rename_i h
      have : toString n = String.ofList [Nat.digitChar n] := by
        show Nat.repr n = _
        rw [Nat.repr, Nat.toDigits_of_lt_base h]
      rw [this]
      simp only [String.toUTF8_eq_toByteArray, digit_bytes n h]
      simp
    · rename_i h
      have h10 : 1 < 10 := by decide
      have hd : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have key : toString n = toString (n / 10) ++ String.ofList [Nat.digitChar (n % 10)] := by
        show Nat.repr n = Nat.repr (n / 10) ++ _
        rw [Nat.repr, Nat.repr, Nat.toDigits_of_base_le h10 (by omega)]
        simp [String.ofList_append]
      rw [ih (n / 10) (by omega), key]
      simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append, digit_bytes _ hd]
      simp [push_append]

theorem pushInt_eq (b : ByteArray) (i : Int) : pushInt b i = b ++ (toString i).toUTF8 := by
  unfold pushInt
  cases i with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Int.not_lt.mpr, if_false, Int.toNat_natCast]
    rw [pushNat_eq]
    rfl
  | negSucc m =>
    simp only [Int.natAbs_negSucc]
    rw [if_pos (Int.negSucc_lt_zero m), pushNat_eq]
    show _ = b ++ (Int.repr (Int.negSucc m)).toUTF8
    simp only [Int.repr, String.toUTF8_eq_toByteArray, String.toByteArray_append]
    have h1 : "-".toByteArray = [45].toByteArray := by decide
    have h2 : (toString (Nat.succ m)).toByteArray = (Nat.succ m).repr.toByteArray := rfl
    rw [h1, h2, ← ByteArray.append_assoc, ByteArray.append_toByteArray_singleton]

/-- bytes of a `ByteArray` as a list -/
abbrev bl (b : ByteArray) : List UInt8 := b.data.toList

theorem bl_append (b c : ByteArray) : bl (b ++ c) = bl b ++ bl c := ByteArray.toList_data_append

theorem bl_push (b : ByteArray) (x : UInt8) : bl (b.push x) = bl b ++ [x] := by simp [bl]

theorem bl_pushNat (b : ByteArray) (n : Nat) : bl (pushNat b n) = bl b ++ SamSpec.num n := by
  rw [pushNat_eq, bl_append, SamSpec.num, text_eq]; rfl

theorem bl_pushInt (b : ByteArray) (i : Int) : bl (pushInt b i) = bl b ++ SamSpec.num i := by
  rw [pushInt_eq, bl_append, SamSpec.num, text_eq]

theorem bl_utf8 (b : ByteArray) (s : String) : bl (b ++ s.toUTF8) = bl b ++ SamSpec.text s := by
  rw [bl_append, text_eq]

theorem bl_text (s : String) : bl s.toByteArray = SamSpec.text s := by rw [text_eq]; rfl

theorem intercalate_cons (f : List UInt8) : ∀ fs : List (List UInt8),
    List.intercalate [9] (f :: fs) = f ++ fs.flatMap (fun x => 9 :: x)
  | [] => by simp
  | g :: fs => by
    rw [List.intercalate_cons_cons, intercalate_cons g fs]; simp

theorem tags_foldl (tags : List String) : ∀ b : ByteArray,
    bl (tags.foldl (fun b tag => (b.push 9) ++ tag.toUTF8) b) = bl b ++ (tags.map SamSpec.text).flatMap (fun x => 9 :: x) := by
  induction tags with
  | nil => intro b; simp
  | cons t ts ih => intro b; rw [List.foldl_cons, ih, bl_utf8, bl_push]; simp

/-- **One SAM line, as bytes**: the fields joined by tabs (no newline). -/
theorem bl_samLine (b qname : ByteArray) (flag : Nat) (rname : String) (pos mapq : Nat) (cigar rnext : String)
    (pnext : Nat) (tlen : Int) (seq qual : ByteArray) (tags : List String) :
    bl (samLine b qname flag rname pos mapq cigar rnext pnext tlen seq qual tags) =
      bl b ++ List.intercalate [9] ([bl qname, SamSpec.num flag, SamSpec.text rname, SamSpec.num pos,
        SamSpec.num mapq, SamSpec.text cigar, SamSpec.text rnext, SamSpec.num pnext, SamSpec.num tlen, bl seq,
        bl qual] ++ tags.map SamSpec.text) := by
  unfold samLine
  simp only [tags_foldl, bl_append, bl_push, bl_pushNat, bl_pushInt, bl_utf8, List.cons_append, intercalate_cons,
    List.flatMap_cons, List.flatMap_append]
  simp [bl_text]

theorem qnameOf_eq (name : List UInt8) : qnameOf name = SamSpec.qname name := by
  unfold qnameOf SamSpec.qname
  simp only []
  generalize name.takeWhile (· != 32) = x
  rw [show x = x.reverse.reverse by simp]
  generalize x.reverse = y
  match y with
  | [] => simp
  | [a] => simp [List.isSuffixOf]
  | a :: c :: rest =>
    have e : (a :: c :: rest).reverse.reverse = a :: c :: rest := by simp
    simp only [List.isSuffixOf, e]
    by_cases hc : c = 47
    · subst hc
      by_cases ha : a = 49
      · subst ha; simp [List.isPrefixOf]
      · by_cases ha2 : a = 50
        · subst ha2; simp [List.isPrefixOf]
        · simp [List.isPrefixOf, ha, ha2, Ne.symm ha, Ne.symm ha2]
    · simp [List.isPrefixOf, hc, Ne.symm hc]

theorem bl_qname (name : ByteArray) : bl (qnameB name) = SamSpec.qname (bl name) := by
  rw [← qnameOf_eq]; exact qnameB_eq name

theorem foldl_push {β : Type} (g : β → UInt8) : ∀ (l : List β) (o : ByteArray),
    bl (l.foldl (fun o a => o.push (g a)) o) = bl o ++ l.map g
  | [], o => by simp
  | a :: l, o => by rw [List.foldl_cons, foldl_push g l, bl_push]; simp

theorem bget! (b : ByteArray) (k : Nat) : b[k]! = (bl b)[k]! := by
  have hs : b.size = (bl b).length := by rw [Array.length_toList]; rfl
  by_cases h : k < b.size
  · rw [getElem!_pos b k h, getElem!_pos _ k (by rw [← hs]; exact h)]
    try rfl
    try simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg b k h, getElem!_neg _ k (by rw [← hs]; exact h)]
    try rfl

theorem bl_reverseMap (f : UInt8 → UInt8) (b : ByteArray) : bl (reverseMapBytes f b) = ((bl b).map f).reverse := by
  have hs : b.size = (bl b).length := by rw [Array.length_toList]; rfl
  unfold reverseMapBytes
  simp
  show bl (List.foldl (fun o a => o.push (f b[b.size - 1 - a]!)) (ByteArray.emptyWithCapacity b.size)
    (List.range' 0 b.size)) = _
  rw [foldl_push (fun a => f b[b.size - 1 - a]!)]
  have he : bl (ByteArray.emptyWithCapacity b.size) = [] := rfl
  rw [he, List.nil_append]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', List.length_reverse, hs]
  · intro j h1 h2
    simp only [List.length_map, List.length_range'] at h1
    rw [List.getElem_map, List.getElem_range', List.getElem_reverse, List.getElem_map, bget!,
      getElem!_pos (bl b) _ (by omega)]
    simp only [List.length_map, hs, Nat.zero_add, Nat.one_mul]

theorem isEmpty_bl (b : ByteArray) : b.isEmpty = true ↔ bl b = [] := by
  have hs : b.size = (bl b).length := by rw [Array.length_toList]; rfl
  rw [ByteArray.isEmpty, beq_iff_eq, hs, List.length_eq_zero_iff]

theorem seq_eq (read : ReadB) (p : Option (MateReport × MateReport)) :
    bl (samSequence read (SamSpec.strand p)).1 = SamSpec.seq read.toRead p ∧
    bl (samSequence read (SamSpec.strand p)).2 = SamSpec.qual read.toRead p := by
  unfold samSequence SamSpec.seq SamSpec.qual
  have ht : read.toRead.sequence = bl read.seq := rfl
  have hq : read.toRead.quality = bl read.qual := rfl
  rw [ht, hq]
  by_cases he : read.seq.isEmpty = true
  · rw [if_pos he, (isEmpty_bl _).mp he]
    simp [bl_text, SamSpec.text]
  · rw [if_neg he]
    have hne : bl read.seq ≠ [] := fun h => he ((isEmpty_bl _).mpr h)
    generalize hst : SamSpec.strand p = st
    cases st with
    | forward =>
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      simp [hx]
    | reverse =>
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      simp only [bl_reverseMap, hx]
      refine ⟨?_, by simp⟩
      congr 2
      funext y
      unfold complementByte
      by_cases h1 : y = 65
      · subst h1; rfl
      by_cases h2 : y = 84
      · subst h2; rfl
      by_cases h3 : y = 67
      · subst h3; rfl
      by_cases h4 : y = 71
      · subst h4; rfl
      simp only [beq_iff_eq, h1, h2, h3, h4, if_false]
theorem bl_unmappedLine (b : ByteArray) (chrs : ChromosomeList) (read : ReadB) (which : Mate) (result : PairResult)
    (tags : List String) (hp : SamSpec.placed which result = none)
    (ht : tags.map SamSpec.text = SamSpec.tags result none) :
    bl ((unmappedLine b read which tags).push 10) = bl b ++ SamSpec.mateLine chrs read.toRead which result := by
  unfold unmappedLine SamSpec.mateLine SamSpec.line
  rw [hp, bl_push, bl_samLine]
  have hs := seq_eq read none
  simp only [SamSpec.strand] at hs
  simp only [hs.1, hs.2, bl_qname, ← ht]
  have hf : SamSpec.flag which none = flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which := by
    cases which <;> rfl
  have hm : SamSpec.mapq result none = 0 := by cases result <;> rfl
  rw [hf, hm, List.append_assoc]
  rfl
theorem text_append (a c : String) : SamSpec.text (a ++ c) = SamSpec.text a ++ SamSpec.text c := by
  rw [text_eq, text_eq, text_eq, String.toUTF8_eq_toByteArray, String.toByteArray_append, ← bl_append]; rfl

theorem text_join (l : List String) : SamSpec.text (String.join l) = l.flatMap SamSpec.text := by
  induction l with
  | nil => show SamSpec.text "" = []; rw [text_eq]; rfl
  | cons x l ih => rw [String.join_cons, text_append, ih, List.flatMap_cons]

theorem text_cigar (p other : MateReport) :
    SamSpec.text (cigarText p.cigar) = SamSpec.cigar (some (p, other)) := by
  unfold cigarText SamSpec.cigar
  dsimp only
  rw [text_join, List.flatMap_map]
  congr 1; funext x
  obtain ⟨st, n⟩ := x
  rw [text_append]
  cases st <;> rfl

theorem text_rname (chrs : ChromosomeList) (i : Nat) :
    SamSpec.text ((chrs[i]?.map (·.1)).getD "*") = SamSpec.chrName chrs i := by
  unfold SamSpec.chrName
  cases chrs[i]? with
  | none => rfl
  | some x => obtain ⟨n, l⟩ := x; rfl

theorem bl_mappedLine (b : ByteArray) (chrs : ChromosomeList) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer)
    (hp : SamSpec.placed which (.aligned answer) = some (mate, other)) :
    bl ((mappedLineS b chrs read which mate other answer).push 10) =
      bl b ++ SamSpec.mateLine chrs read.toRead which (.aligned answer) := by
  unfold mappedLineS SamSpec.mateLine SamSpec.line
  rw [hp, bl_push, bl_samLine]
  have hs := seq_eq read (some (mate, other))
  simp only [SamSpec.strand] at hs
  simp only [hs.1, hs.2, bl_qname]
  have hf : SamSpec.flag which (some (mate, other)) = flagPaired + flagProperPair + mateFlag which +
      reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse := by
    unfold SamSpec.flag SamSpec.reverseBit reverseFlag
    cases which <;> rfl
  have hm : SamSpec.mapq (.aligned answer) (some (mate, other)) = mapq answer := by
    unfold SamSpec.mapq mapq; rfl
  have hrn : SamSpec.text (if mate.placement.chromosome = other.placement.chromosome then "=" else
      (chrs[other.placement.chromosome]?.map (·.1)).getD "*") = SamSpec.rnext chrs (some (mate, other)) := by
    unfold SamSpec.rnext
    by_cases e : mate.placement.chromosome = other.placement.chromosome
    · simp [e]
    · simp only [e, if_false, decide_false]; exact text_rname _ _
  have htl : SamSpec.tlen which (some (mate, other)) =
      (if (mate.placement.start < other.placement.start ||
          (mate.placement.start = other.placement.start && which = .one)) = true
        then ((max mate.placement.stop other.placement.stop - min mate.placement.start other.placement.start : Nat) : Int)
        else -((max mate.placement.stop other.placement.stop - min mate.placement.start other.placement.start : Nat) : Int)) := by
    unfold SamSpec.tlen
    simp only []
    rcases Nat.lt_trichotomy mate.placement.start other.placement.start with h | h | h
    · rw [Nat.compare_eq_lt.mpr h]; simp [h]
    · rw [Nat.compare_eq_eq.mpr h]; cases which <;> simp [h]
    · rw [Nat.compare_eq_gt.mpr h]; simp [h, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
  have htg : SamSpec.tags (.aligned answer) (some (mate, other)) =
      (s!"AS:i:{mate.score}" :: answerTagsS answer).map SamSpec.text := by
    unfold SamSpec.tags answerTagsS uniquenessText
    dsimp only
    cases answer.uniqueness <;> rfl
  rw [hf, hm, htl, htg, text_cigar mate other, text_rname, hrn, List.append_assoc]
  rfl
theorem bl_samLines (b : ByteArray) (chrs : ChromosomeList) (r1 r2 : ReadB) (result : PairResult) :
    bl (samLinesS b chrs r1 r2 result) = bl b ++ SamSpec.pairLines chrs r1.toRead r2.toRead result := by
  unfold samLinesS SamSpec.pairLines
  cases result with
  | trimmedAway mate =>
    dsimp only
    have ht : ∀ w, [s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"].map SamSpec.text =
        SamSpec.tags (.trimmedAway mate) (SamSpec.placed w (.trimmedAway mate)) := by
      intro w; cases mate <;> rfl
    rw [bl_unmappedLine _ chrs _ .two _ _ rfl (ht .two), bl_unmappedLine _ chrs _ .one _ _ rfl (ht .one),
      List.append_assoc]
  | aligned answer =>
    dsimp only
    cases hf : answer.found with
    | some pair =>
      dsimp only
      have h1 : SamSpec.placed .one (.aligned answer) = some (pair.mate1, pair.mate2) := by
        unfold SamSpec.placed; dsimp only; rw [hf]; rfl
      have h2 : SamSpec.placed .two (.aligned answer) = some (pair.mate2, pair.mate1) := by
        unfold SamSpec.placed; dsimp only; rw [hf]; rfl
      rw [bl_mappedLine _ chrs _ .two _ _ _ h2, bl_mappedLine _ chrs _ .one _ _ _ h1, List.append_assoc]
    | none =>
      dsimp only
      have hp : ∀ w, SamSpec.placed w (.aligned answer) = none := by
        intro w; unfold SamSpec.placed; cases w <;> (dsimp only; rw [hf]; rfl)
      have ht : ∀ w, (answerTagsS answer).map SamSpec.text =
          SamSpec.tags (.aligned answer) (SamSpec.placed w (.aligned answer)) := by
        intro w; rw [hp w]; unfold SamSpec.tags answerTagsS uniquenessText; dsimp only
        cases answer.uniqueness <;> rfl
      rw [bl_unmappedLine _ chrs _ .two _ _ (hp .two) (by rw [ht .two, hp .two]),
        bl_unmappedLine _ chrs _ .one _ _ (hp .one) (by rw [ht .one, hp .one]), List.append_assoc]
def toReads (p : ReadB × ReadB) : FQ.Read × FQ.Read := (p.1.toRead, p.2.toRead)

theorem fold_lines (chrs : ChromosomeList) : ∀ (l : List ((ReadB × ReadB) × PairResult)) (b : ByteArray),
    bl (l.foldl (fun bytes x => samLinesS bytes chrs x.1.1 x.1.2 x.2) b) =
      bl b ++ (l.map fun x => SamSpec.pairLines chrs x.1.1.toRead x.1.2.toRead x.2).flatten
  | [], b => by simp
  | x :: l, b => by rw [List.foldl_cons, fold_lines chrs l, bl_samLines]; simp

/-- **A chunk's bytes are the spec's body** of its pairs and results. -/
theorem samChunkS_eq (chrs : ChromosomeList) (chunk : Array (ReadB × ReadB)) (results : List PairResult) :
    bl (samChunkS chrs chunk results) = SamSpec.body chrs (chunk.toList.map toReads) results := by
  unfold samChunkS SamSpec.body
  rw [← Array.foldl_toList, Array.toList_zip, List.toList_toArray]
  have : (chunk.toList.zip results).foldl (init := ByteArray.empty)
      (fun bytes x => match x with | ((read1, read2), result) => samLinesS bytes chrs read1 read2 result) =
      (chunk.toList.zip results).foldl (fun bytes x => samLinesS bytes chrs x.1.1 x.1.2 x.2) ByteArray.empty := rfl
  rw [this, fold_lines, List.zip_map_left]
  simp [toReads, Function.comp_def]

theorem fold_header : ∀ (ls : List String) (b : ByteArray),
    bl (ls.foldl (fun b l => (b ++ l.toUTF8).push 10) b) = bl b ++ ls.flatMap (fun l => SamSpec.text l ++ [10])
  | [], b => by simp
  | x :: l, b => by rw [List.foldl_cons, fold_header l, bl_push, bl_utf8]; simp

/-- **The header bytes are the spec's header.** -/
theorem samHeaderB_eq (chrs : ChromosomeList) : bl (samHeaderB chrs) = SamSpec.header chrs := by
  unfold samHeaderB samHeader SamSpec.header SamSpec.line
  rw [fold_header]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_map, intercalate_cons]
  simp only [text_append]
  have h1 : SamSpec.text "@HD\tVN:1.6\tSO:unsorted" =
      SamSpec.text "@HD" ++ 9 :: SamSpec.text "VN:1.6" ++ 9 :: SamSpec.text "SO:unsorted" := by decide +kernel
  have h2 : SamSpec.text (toString "@SQ\tSN:") = SamSpec.text "@SQ" ++ 9 :: SamSpec.text (toString "SN:") := by decide +kernel
  have h3 : SamSpec.text (toString "\tLN:") = 9 :: SamSpec.text (toString "LN:") := by decide +kernel
  have h4 : SamSpec.text "@PG\tID:lean-align\tPN:lean-align" =
      SamSpec.text "@PG" ++ 9 :: SamSpec.text "ID:lean-align" ++ 9 :: SamSpec.text "PN:lean-align" := by decide +kernel
  have he : bl ByteArray.empty = [] := rfl
  simp only [h1, h2, h3, h4, he, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
theorem body_append (chrs : ChromosomeList) (p1 p2 : List (FQ.Read × FQ.Read)) (r1 r2 : List PairResult)
    (h : p1.length = r1.length) :
    SamSpec.body chrs (p1 ++ p2) (r1 ++ r2) = SamSpec.body chrs p1 r1 ++ SamSpec.body chrs p2 r2 := by
  unfold SamSpec.body
  rw [List.zip_append h, List.map_append, List.flatten_append]

/-- **The SAM file**: the header bytes, then each chunk's bytes in order, are `SamSpec.samFile` of all the pairs
and results (each chunk with one result per pair). -/
theorem samFileS_eq (chrs : ChromosomeList) (chunks : List (Array (ReadB × ReadB) × List PairResult))
    (h : ∀ c ∈ chunks, c.1.size = c.2.length) :
    bl (samHeaderB chrs) ++ chunks.flatMap (fun c => bl (samChunkS chrs c.1 c.2)) =
      SamSpec.samFile chrs (chunks.flatMap fun c => c.1.toList.map toReads) (chunks.flatMap (·.2)) := by
  unfold SamSpec.samFile
  rw [samHeaderB_eq]
  congr 1
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, ih (fun x hx => h x (by simp [hx])),
      samChunkS_eq, body_append]
    simp [h c (by simp)]

end SamFast
end Spec



#print axioms Spec.SamFast.samHeaderB_eq
#print axioms Spec.SamFast.samChunkS_eq
#print axioms Spec.SamFast.samFileS_eq
#print axioms Spec.SamFast.bl_samLines
