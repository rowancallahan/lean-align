import Proofs.SamFast

/-! # The fused SAM writer

`samChunkF`: one pass per job from the reads and results into one pre-sized `ByteArray`. No `String`s per line
(chromosome names turned into bytes once per job, tag prefixes and uniqueness words are constants), the QNAME copied
straight from the read's name, digits pushed in place (`pushNat`), CIGAR counts and letters pushed directly,
SEQ / QUAL reversed (and complemented) by a byte loop into the output. `samChunkF_eq`: it is `samChunkS`, byte for
byte (`@[csimp] samChunkS_eq_F`: the compiled code runs it). -/

namespace Spec.SamFused
open Spec Spec.SamFast

/-! ## Pieces -/

-- `bytes` from the last byte to the first, each through `f`, pushed onto `out` (`i`: bytes left)
@[specialize] def revPush (f : UInt8 → UInt8) (bytes out : ByteArray) (i : USize) (h : i.toNat ≤ bytes.size) :
    ByteArray :=
  if h0 : i = 0 then out
  else
    have hj : (i - 1).toNat = i.toNat - 1 := toNat_sub1 i h0
    have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
    revPush f bytes (out.push (f (bytes.uget (i - 1) (by omega)))) (i - 1) (by omega)
termination_by i.toNat
decreasing_by
  have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [toNat_sub1 i h0]; omega

-- `out ++ reverseMapBytes f bytes`
@[inline] def pushRevMap (f : UInt8 → UInt8) (out bytes : ByteArray) : ByteArray :=
  if bytes.size < 4294967296 then revPush f bytes out bytes.usize (usize_le bytes)
  else out ++ reverseMapBytes f bytes

-- `out ++ src.extract 0 n`, copied in place
@[inline] def pushPrefix (out src : ByteArray) (n : Nat) : ByteArray :=
  src.copySlice 0 out out.size n false

-- `out ++ qnameB name`
@[inline] def pushQname (out name : ByteArray) : ByteArray :=
  let e := spaceAt name name.size 0
  if 2 ≤ e && name[e - 2]! == 47 && (name[e - 1]! == 49 || name[e - 1]! == 50) then pushPrefix out name (e - 2)
  else pushPrefix out name e

def stepByte : Step → UInt8
  | .diag => 77
  | .gapY => 73
  | .gapX => 68

-- `out ++ (cigarText cigar).toUTF8`
@[inline] def pushCigar (out : ByteArray) (cigar : Array (Step × Nat)) : ByteArray :=
  cigar.foldl (fun b (step, count) => (pushNat b count).push (stepByte step)) out

-- the chromosome name `i` as bytes (`"*"` if there is none)
@[inline] def chrB (chrsB : Array ByteArray) (i : Nat) : ByteArray := chrsB.getD i "*".toUTF8

def uniqB : Uniqueness → ByteArray
  | .unique      => "unique".toUTF8
  | .multimapper => "multimapper".toUTF8
  | .unknown     => "unknown".toUTF8
  | .repetitiveUnknown => "repetitiveUnknown".toUTF8

-- TAB, then SEQ and TAB QUAL on `strand`
@[inline] def pushSeqQual (b : ByteArray) (read : ReadB) (strand : Strand) : ByteArray :=
  if read.seq.isEmpty then ((b.push 9).push 42).push 9 |>.push 42 else
  match strand with
  | .forward => (((b.push 9) ++ read.seq).push 9) ++ read.qual
  | .reverse => pushRevMap id ((pushRevMap complementByte (b.push 9) read.seq).push 9) read.qual

-- TAB XB:i:… TAB XU:Z:…
@[inline] def pushAnswer (b : ByteArray) (answer : PairAnswer) : ByteArray :=
  (pushInt ((b.push 9) ++ "XB:i:".toUTF8) answer.bestPossibleScore).push 9 ++ "XU:Z:".toUTF8 ++ uniqB answer.uniqueness

/-! ## Lines -/

def mappedLineF (b : ByteArray) (chrsB : Array ByteArray) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) : ByteArray :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let span : Nat := max mate.placement.stop other.placement.stop - min mate.placement.start other.placement.start
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then (span : Int) else -(span : Int)
  let b := pushQname b read.name
  let b := pushNat (b.push 9) flag
  let b := (b.push 9) ++ chrB chrsB mate.placement.chromosome
  let b := pushNat (b.push 9) (mate.placement.start + 1)
  let b := pushNat (b.push 9) (mapq answer)
  let b := pushCigar (b.push 9) mate.cigar
  let b := if mate.placement.chromosome = other.placement.chromosome then (b.push 9).push 61
    else (b.push 9) ++ chrB chrsB other.placement.chromosome
  let b := pushNat (b.push 9) (other.placement.start + 1)
  let b := pushInt (b.push 9) tlen
  let b := pushSeqQual b read mate.placement.strand
  let b := pushInt ((b.push 9) ++ "AS:i:".toUTF8) mate.score
  (pushAnswer b answer).push 10

-- an unmapped mate: QNAME FLAG * 0 0 * * 0 0 SEQ QUAL, then `tags` (already with their leading TAB)
@[inline] def unmappedLineF (b : ByteArray) (read : ReadB) (which : Mate) (tags : ByteArray → ByteArray) : ByteArray :=
  let b := pushQname b read.name
  let b := pushNat (b.push 9) (flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which)
  let b := b ++ "\t*\t0\t0\t*\t*\t0\t0".toUTF8
  (tags (pushSeqQual b read .forward)).push 10

def samLinesF (b : ByteArray) (chrsB : Array ByteArray) (read1 read2 : ReadB) (result : PairResult) : ByteArray :=
  match result with
  | .trimmedAway mate =>
      let tag := if mate = .one then "\tXT:Z:trimmedAway1".toUTF8 else "\tXT:Z:trimmedAway2".toUTF8
      unmappedLineF (unmappedLineF b read1 .one (· ++ tag)) read2 .two (· ++ tag)
  | .aligned answer =>
      match answer.found with
      | some pair =>
          mappedLineF (mappedLineF b chrsB read1 .one pair.mate1 pair.mate2 answer)
            chrsB read2 .two pair.mate2 pair.mate1 answer
      | none =>
          unmappedLineF (unmappedLineF b read1 .one (pushAnswer · answer)) read2 .two (pushAnswer · answer)

-- bytes to reserve for a job's lines
def sizeHint (chunk : Array (ReadB × ReadB)) : Nat :=
  chunk.foldl (fun n (r1, r2) => n + 2 * (r1.name.size + r2.name.size + r1.seq.size + r2.seq.size) + 400) 0

def samChunkF (chromosomes : ChromosomeList) (chunk : Array (ReadB × ReadB)) (results : List PairResult) :
    ByteArray :=
  let chrsB := chromosomes.map (·.1.toUTF8)
  (chunk.zip results.toArray).foldl (init := ByteArray.emptyWithCapacity (sizeHint chunk))
    fun bytes ((read1, read2), result) => samLinesF bytes chrsB read1 read2 result

/-! ## Proof -/

theorem bl_inj (a c : ByteArray) (h : bl a = bl c) : a = c := by
  apply ByteArray.ext; exact Array.toList_inj.mp h

theorem foldl_push_out {β : Type} (g : β → UInt8) : ∀ (l : List β) (out : ByteArray),
    l.foldl (fun b a => b.push (g a)) out = out ++ l.foldl (fun b a => b.push (g a)) ByteArray.empty := by
  intro l out
  apply bl_inj
  rw [foldl_push, bl_append, foldl_push]; simp

theorem revPush_eq (f : UInt8 → UInt8) (bytes : ByteArray) : ∀ m (i : USize) out h, i.toNat = m → m ≤ bytes.size →
    revPush f bytes out i h =
      (List.range' (bytes.size - m) m).foldl (fun b a => b.push (f bytes[bytes.size - 1 - a]!)) out
  | 0, i, out, h, hi, _ => by
    have h0 : i = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [revPush, dif_pos h0]; rfl
  | m + 1, i, out, h, hi, hm => by
    have h0 : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (i - 1).toNat = m := by rw [toNat_sub1 i h0, hi]; rfl
    rw [revPush, dif_neg h0]
    dsimp only
    rw [revPush_eq f bytes m (i - 1) _ _ ej (by omega), List.range'_succ, List.foldl_cons,
      show bytes.size - (m + 1) + 1 = bytes.size - m by omega,
      show bytes.size - 1 - (bytes.size - (m + 1)) = m by omega, getElem!_pos bytes m (by omega)]
    congr 3
    show bytes[(i - 1).toNat] = _
    simp only [ej]

theorem pushRevMap_eq (f : UInt8 → UInt8) (out bytes : ByteArray) :
    pushRevMap f out bytes = out ++ reverseMapBytes f bytes := by
  unfold pushRevMap
  split
  · rename_i h
    rw [revPush_eq f bytes bytes.size _ _ _ (usize_eq bytes h) (Nat.le_refl _), reverseMapBytes_eq,
      reverseMapBytesF, if_pos h, revMapU_eq f bytes bytes.size _ _ _ (usize_eq bytes h) (Nat.le_refl _),
      foldl_push_out, foldl_push_out (l := List.range' _ _) (out := ByteArray.emptyWithCapacity _)]
    rfl
  · rfl

theorem pushPrefix_eq (out src : ByteArray) (n : Nat) : pushPrefix out src n = out ++ src.extract 0 n := by
  unfold pushPrefix
  rw [ByteArray.copySlice_eq_append, ByteArray.extract_zero_size]
  have : out.extract (out.size + min n (src.data.size - 0)) out.data.size = ByteArray.empty := by
    have hs : out.size = out.data.size := rfl
    rw [ByteArray.extract_eq_empty_iff, ← hs]; omega
  rw [this, ByteArray.append_empty, Nat.zero_add]

theorem pushQname_eq (out name : ByteArray) : pushQname out name = out ++ qnameB name := by
  unfold pushQname qnameB
  dsimp only
  split <;> rename_i h <;> simp only [h, if_true, if_false, pushPrefix_eq]

theorem cigar_fold : ∀ (l : List (Step × Nat)) (out : ByteArray),
    bl (l.foldl (fun b (x : Step × Nat) => (pushNat b x.2).push (stepByte x.1)) out) =
      bl out ++ l.flatMap (fun x => SamSpec.num x.2 ++ [stepByte x.1])
  | [], out => by simp
  | x :: l, out => by
    rw [List.foldl_cons, cigar_fold l, bl_push, bl_pushNat]; simp

theorem step_text (st : Step) : [stepByte st] = SamSpec.text (stepLetter st) := by
  cases st <;> decide +kernel

theorem bl_pushCigar (out : ByteArray) (c : Array (Step × Nat)) :
    bl (pushCigar out c) = bl out ++ SamSpec.text (cigarText c) := by
  unfold pushCigar cigarText
  rw [← Array.foldl_toList]
  show bl (c.toList.foldl (fun b (x : Step × Nat) => (pushNat b x.2).push (stepByte x.1)) out) = _
  rw [cigar_fold, text_join, List.flatMap_map]
  congr 2; funext x
  obtain ⟨st, n⟩ := x
  rw [text_append, ← step_text]; rfl

theorem bl_chrB (chrs : ChromosomeList) (i : Nat) :
    bl (chrB (chrs.map (·.1.toUTF8)) i) = SamSpec.text ((chrs[i]?.map (·.1)).getD "*") := by
  unfold chrB
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases chrs[i]? with
  | none => rw [text_eq]; rfl
  | some x => rw [text_eq]; rfl

theorem bl_uniqB (u : Uniqueness) : bl (uniqB u) = SamSpec.text (uniquenessText u) := by
  cases u <;> rw [text_eq] <;> rfl

theorem bl_pushSeqQual (b : ByteArray) (read : ReadB) (st : Strand) :
    bl (pushSeqQual b read st) =
      bl b ++ 9 :: (bl (samSequence read st).1 ++ 9 :: bl (samSequence read st).2) := by
  unfold pushSeqQual samSequence
  by_cases he : read.seq.isEmpty = true
  · simp only [he, if_true]
    have h1 : bl "*".toByteArray = [42] := by decide +kernel
    simp [bl_push, h1]
  · simp only [he, if_false, Bool.false_eq_true]
    cases st with
    | forward => simp [bl_push, bl_append]
    | reverse =>
      simp only [pushRevMap_eq, bl_append, bl_push]
      simp

theorem bl_pushAnswer (b : ByteArray) (a : PairAnswer) :
    bl (pushAnswer b a) = bl b ++ ((answerTagsS a).map SamSpec.text).flatMap (fun x => 9 :: x) := by
  unfold pushAnswer answerTagsS
  simp only [bl_append, bl_push, bl_pushInt, bl_uniqB, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, text_append]
  have h1 : bl "XB:i:".toUTF8 = SamSpec.text (toString "XB:i:") := by rw [text_eq]; rfl
  have h2 : bl "XU:Z:".toUTF8 = SamSpec.text (toString "XU:Z:") := by rw [text_eq]; rfl
  have h3 : SamSpec.text (toString (uniquenessText a.uniqueness)) = SamSpec.text (uniquenessText a.uniqueness) := rfl
  rw [h1, h2, h3, SamSpec.num]
  simp

theorem bl_mappedLineF (b : ByteArray) (chrs : ChromosomeList) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) :
    bl (mappedLineF b (chrs.map (·.1.toUTF8)) read which mate other answer) =
      bl ((mappedLineS b chrs read which mate other answer).push 10) := by
  unfold mappedLineF mappedLineS
  have hAS : bl "AS:i:".toUTF8 = SamSpec.text (toString "AS:i:") := by rw [text_eq]; rfl
  have h61 : SamSpec.text "=" = [61] := by decide +kernel
  by_cases e : mate.placement.chromosome = other.placement.chromosome
  · simp only [e, if_true]
    simp only [bl_push, bl_samLine, bl_pushNat, bl_pushInt, bl_append, bl_pushCigar, bl_chrB, pushQname_eq,
      bl_pushSeqQual, bl_pushAnswer, intercalate_cons, List.flatMap_cons, List.flatMap_append, List.map_cons,
      List.cons_append, List.append_assoc, List.nil_append, bl_qname, h61, hAS, text_append, List.singleton_append]
    simp only [SamSpec.num, List.cons_append, List.append_assoc, List.nil_append]
  · simp only [e, if_false]
    simp only [bl_push, bl_samLine, bl_pushNat, bl_pushInt, bl_append, bl_pushCigar, bl_chrB, pushQname_eq,
      bl_pushSeqQual, bl_pushAnswer, intercalate_cons, List.flatMap_cons, List.flatMap_append, List.map_cons,
      List.cons_append, List.append_assoc, List.nil_append, bl_qname, h61, hAS, text_append, List.singleton_append]
    simp only [SamSpec.num, List.cons_append, List.append_assoc, List.nil_append]

theorem bl_unmappedLineF (b : ByteArray) (read : ReadB) (which : Mate) (tagsF : ByteArray → ByteArray)
    (tagsL : List String) (ht : ∀ x, bl (tagsF x) = bl x ++ (tagsL.map SamSpec.text).flatMap (fun y => 9 :: y)) :
    bl (unmappedLineF b read which tagsF) = bl ((unmappedLine b read which tagsL).push 10) := by
  unfold unmappedLineF unmappedLine
  have hc : bl "\t*\t0\t0\t*\t*\t0\t0".toUTF8 = [9, 42, 9, 48, 9, 48, 9, 42, 9, 42, 9, 48, 9, 48] := by decide +kernel
  have h1 : SamSpec.text "*" = [42] := by decide +kernel
  have h2 : SamSpec.num ((0 : Nat) : Int) = [48] := by decide +kernel
  have h3 : SamSpec.num (0 : Int) = [48] := by decide +kernel
  simp only [bl_push, ht, bl_samLine, bl_pushNat, bl_append, pushQname_eq, bl_pushSeqQual, intercalate_cons,
    List.flatMap_cons, List.flatMap_append, List.map_cons, List.cons_append, List.append_assoc, List.nil_append,
    hc, h1, h2, h3]

theorem mappedLineF_eq (b : ByteArray) (chrs : ChromosomeList) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) :
    mappedLineF b (chrs.map (·.1.toUTF8)) read which mate other answer =
      (mappedLineS b chrs read which mate other answer).push 10 :=
  bl_inj _ _ (bl_mappedLineF b chrs read which mate other answer)

theorem trimmedTag (mate : Mate) : ∀ x,
    bl (x ++ (if mate = .one then "\tXT:Z:trimmedAway1".toUTF8 else "\tXT:Z:trimmedAway2".toUTF8)) =
      bl x ++ ([s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"].map SamSpec.text).flatMap (fun y => 9 :: y) := by
  intro x; rw [bl_append]; cases mate <;> (congr 1; decide +kernel)

theorem samLinesF_eq (b : ByteArray) (chrs : ChromosomeList) (r1 r2 : ReadB) (result : PairResult) :
    samLinesF b (chrs.map (·.1.toUTF8)) r1 r2 result = samLinesS b chrs r1 r2 result := by
  unfold samLinesF samLinesS
  cases result with
  | trimmedAway mate =>
    dsimp only
    rw [bl_inj _ _ (bl_unmappedLineF _ _ _ _ _ (trimmedTag mate)),
      bl_inj _ _ (bl_unmappedLineF _ _ _ _ _ (trimmedTag mate))]
  | aligned answer =>
    dsimp only
    cases answer.found with
    | some pair => dsimp only; rw [mappedLineF_eq, mappedLineF_eq]
    | none =>
      dsimp only
      rw [bl_inj _ _ (bl_unmappedLineF _ _ _ _ _ (fun x => bl_pushAnswer x answer)),
        bl_inj _ _ (bl_unmappedLineF _ _ _ _ _ (fun x => bl_pushAnswer x answer))]

/-- **The fused writer is `samChunkS`**, byte for byte. -/
theorem samChunkF_eq (chrs : ChromosomeList) (chunk : Array (ReadB × ReadB)) (results : List PairResult) :
    samChunkF chrs chunk results = samChunkS chrs chunk results := by
  unfold samChunkF samChunkS
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have he : ByteArray.emptyWithCapacity (sizeHint chunk) = ByteArray.empty := rfl
  rw [he]
  congr 1; funext bytes x
  obtain ⟨⟨r1, r2⟩, res⟩ := x
  exact samLinesF_eq bytes chrs r1 r2 res

@[csimp] theorem samChunkS_eq_F : @samChunkS = @samChunkF := by
  funext chrs chunk results; exact (samChunkF_eq chrs chunk results).symm

end Spec.SamFused

#print axioms Spec.SamFused.samChunkF_eq
#print axioms Spec.SamFused.samChunkS_eq_F
