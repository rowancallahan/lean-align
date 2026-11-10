import Proofs.Fasta
import Proofs.Fastq
import FastqIO

/-! # From reads to SAM

* `ReadB.toRead`: the shim's reads (`ReadB`, bytes; FastqIO) are the spec's `FQ.Read`s.
* The QNAME rule (`qnameOf`): a read's name up to the first space, without a trailing "/1" or "/2". Mates are paired
  by it (the shim); a QNAME must be 1..254 bytes in '!'..'?' or 'A'..'~' (`qnameOk`).
* SAM output pieces (`samLine`, `unmappedLine`, `samSequence`, `pushNat`, ...) used by the proved writer
  (Proofs/SamFast.lean: `samChunkS_eq`).
* `qnameB_eq`, `qnameOkB_eq`: the byte QNAME rule is the list one. -/

namespace Spec

def samHeader (chromosomes : ChromosomeList) : List String :=
  ["@HD\tVN:1.6\tSO:unsorted"] ++
  chromosomes.toList.map (fun (name, length) => s!"@SQ\tSN:{name}\tLN:{length}") ++
  ["@PG\tID:lean-align\tPN:lean-align"]

-- SAM flag bits
def flagPaired       : Nat := 1
def flagProperPair   : Nat := 2
def flagUnmapped     : Nat := 4
def flagMateUnmapped : Nat := 8
def flagReverse      : Nat := 16
def flagMateReverse  : Nat := 32
def flagFirst        : Nat := 64
def flagSecond       : Nat := 128

def mateFlag : Mate → Nat
  | .one => flagFirst
  | .two => flagSecond

def reverseFlag (strand : Strand) (bit : Nat) : Nat :=
  match strand with
  | .forward => 0
  | .reverse => bit

-- SAM letters: M = read and reference, I = read only, D = reference only
def stepLetter : Step → String
  | .diag => "M"
  | .gapY => "I"
  | .gapX => "D"

-- e.g. "50M1I49M"
def cigarText (cigar : Array (Step × Nat)) : String :=
  String.join (cigar.toList.map fun (step, count) => toString count ++ stepLetter step)


/-! ## Reads, names, trimming -/

-- the shim's read as the spec's read
def ReadB.toRead (r : ReadB) : FQ.Read := ⟨r.name.data.toList, r.seq.data.toList, r.qual.data.toList⟩

-- the SAM QNAME of a read name (the name after '@'): up to the first space, without a trailing "/1" or "/2"
def qnameOf (name : List UInt8) : List UInt8 :=
  let base := name.takeWhile (· != 32)
  if [47, 49].isSuffixOf base || [47, 50].isSuffixOf base then base.dropLast.dropLast else base

-- a SAM QNAME: 1..254 bytes, each in '!'..'?' or 'A'..'~'
def qnameOk (q : List UInt8) : Bool :=
  0 < q.length && q.length ≤ 254 && q.all fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)

-- the first space at or after `i` (or the end)
def spaceAt (b : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | f + 1, i => if i < b.size && b[i]! != 32 then spaceAt b f (i + 1) else i

-- `qnameOf` on bytes (`qnameB_eq`)
def qnameB (name : ByteArray) : ByteArray :=
  let e := spaceAt name name.size 0
  if 2 ≤ e && name[e - 2]! == 47 && (name[e - 1]! == 49 || name[e - 1]! == 50) then name.extract 0 (e - 2)
  else name.extract 0 e

-- `qnameOk` on bytes (`qnameOkB_eq`)
def qnameOkB (q : ByteArray) : Bool :=
  0 < q.size && q.size ≤ 254 && allBytes (fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)) q

/-! ## SAM text -/

-- `complement` (Mapping.lean) on one byte: A <-> T, C <-> G, everything else unchanged
def complementByte (byte : UInt8) : UInt8 :=
  if byte == 65 then 84 else if byte == 84 then 65 else if byte == 67 then 71 else if byte == 71 then 67 else byte

-- the bytes in reverse order, each through `f`
def reverseMapBytes (f : UInt8 → UInt8) (bytes : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity bytes.size
  for i in [0:bytes.size] do
    out := out.push (f bytes[bytes.size - 1 - i]!)
  return out

-- `reverseMapBytes` by `uget`, last byte first (`reverseMapBytes_eq`, `@[csimp]`)
def revMapU (f : UInt8 → UInt8) (bytes out : ByteArray) (i : USize) (h : i.toNat ≤ bytes.size) : ByteArray :=
  if h0 : i = 0 then out
  else
    have hj : (i - 1).toNat = i.toNat - 1 := toNat_sub1 i h0
    have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
    revMapU f bytes (out.push (f (bytes.uget (i - 1) (by omega)))) (i - 1) (by omega)
termination_by i.toNat
decreasing_by
  have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [toNat_sub1 i h0]; omega

theorem revMapU_eq (f : UInt8 → UInt8) (bytes : ByteArray) : ∀ m (i : USize) out h, i.toNat = m → m ≤ bytes.size →
    revMapU f bytes out i h =
      (List.range' (bytes.size - m) m).foldl (fun b a => b.push (f bytes[bytes.size - 1 - a]!)) out
  | 0, i, out, h, hi, _ => by
    have h0 : i = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [revMapU, dif_pos h0]; rfl
  | m + 1, i, out, h, hi, hm => by
    have h0 : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (i - 1).toNat = m := by rw [toNat_sub1 i h0, hi]; rfl
    rw [revMapU, dif_neg h0]
    dsimp only
    rw [revMapU_eq f bytes m (i - 1) _ _ ej (by omega), List.range'_succ, List.foldl_cons,
      show bytes.size - (m + 1) + 1 = bytes.size - m by omega,
      show bytes.size - 1 - (bytes.size - (m + 1)) = m by omega, getElem!_pos bytes m (by omega)]
    congr 3
    show bytes[(i - 1).toNat] = _
    simp only [ej]

@[inline] def reverseMapBytesF (f : UInt8 → UInt8) (bytes : ByteArray) : ByteArray :=
  if bytes.size < 4294967296 then revMapU f bytes (ByteArray.emptyWithCapacity bytes.size) bytes.usize (usize_le bytes)
  else reverseMapBytes f bytes

@[csimp] theorem reverseMapBytes_eq : @reverseMapBytes = @reverseMapBytesF := by
  funext f bytes
  unfold reverseMapBytesF
  split
  · rename_i h
    rw [revMapU_eq f bytes bytes.size _ _ _ (usize_eq bytes h) (Nat.le_refl _), Nat.sub_self]
    unfold reverseMapBytes
    simp
  · rfl

def uniquenessText : Uniqueness → String
  | .unique      => "unique"
  | .multimapper => "multimapper"
  | .unknown     => "unknown"
  | .repetitiveUnknown => "repetitiveUnknown"

-- MAPQ (stand-in): 60 when proved unique, else 0
def mapq (answer : PairAnswer) : Nat :=
  match answer.uniqueness with
  | .unique => 60
  | _       => 0

-- the decimal digits of `n`, appended to `b` (= `b ++ (toString n).toUTF8`)
def pushNat (b : ByteArray) (n : Nat) : ByteArray :=
  if h : n < 10 then b.push (48 + n.toUInt8) else (pushNat b (n / 10)).push (48 + (n % 10).toUInt8)
termination_by n
decreasing_by omega

-- `toString i` appended to `b`
def pushInt (b : ByteArray) (i : Int) : ByteArray :=
  if i < 0 then pushNat (b.push 45) i.natAbs else pushNat b i.toNat

-- SEQ and QUAL as on the forward strand of the reference: reversed (and complemented) on reverse.
-- A mate trimmed away entirely has no letters: SEQ and QUAL are "*".
def samSequence (read : ReadB) (strand : Strand) : ByteArray × ByteArray :=
  if read.seq.isEmpty then ("*".toUTF8, "*".toUTF8) else
  match strand with
  | .forward => (read.seq, read.qual)
  | .reverse => (reverseMapBytes complementByte read.seq, reverseMapBytes id read.qual)

-- one SAM line appended to `b` (no newline): the eleven fields in SAM order, then the tags, tab-separated
def samLine (b : ByteArray) (qname : ByteArray) (flag : Nat) (rname : String) (pos mapq : Nat) (cigar rnext : String)
    (pnext : Nat) (tlen : Int) (seq qual : ByteArray) (tags : List String) : ByteArray :=
  let b := pushNat ((b ++ qname).push 9) flag
  let b := (b.push 9) ++ rname.toUTF8
  let b := pushNat (b.push 9) pos
  let b := pushNat (b.push 9) mapq
  let b := (b.push 9) ++ cigar.toUTF8
  let b := (b.push 9) ++ rnext.toUTF8
  let b := pushNat (b.push 9) pnext
  let b := pushInt (b.push 9) tlen
  let b := ((b.push 9) ++ seq).push 9 ++ qual
  tags.foldl (fun b tag => (b.push 9) ++ tag.toUTF8) b

-- a mate with no alignment reported
def unmappedLine (b : ByteArray) (read : ReadB) (which : Mate) (tags : List String) : ByteArray :=
  let flag := flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which
  let (seq, qual) := samSequence read .forward
  samLine b (qnameB read.name) flag "*" 0 0 "*" "*" 0 0 seq qual tags

/-! ## The QNAME rule on bytes -/

theorem spaceAt_eq (n : ByteArray) : ∀ k i, i ≤ n.size → n.size - i ≤ k →
    spaceAt n k i = i + ((FQ.L n i).takeWhile (· != 32)).length
  | 0, i, h1, h2 => by
    have : i = n.size := by omega
    subst this; rw [spaceAt, FQ.L_size n _ (Nat.le_refl _)]; simp
  | k + 1, i, h1, h2 => by
    rw [spaceAt]
    by_cases hi : i < n.size
    · rw [FQ.L_cons n i hi, List.takeWhile_cons]
      by_cases hb : (n[i]! != 32) = true
      · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hi, hb⟩), if_pos hb,
          spaceAt_eq n k (i + 1) (by omega) (by omega)]; simp; omega
      · rw [if_neg (by simp [hb]), if_neg hb]; simp
    · rw [if_neg (by simp [hi]), FQ.L_size n i (by omega)]; simp

-- the last two bytes of a list of length at least 2
theorem drop_two (l : List UInt8) (h : 2 ≤ l.length) :
    l.drop (l.length - 2) = [l[l.length - 2]'(by omega), l[l.length - 1]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    show l.length - 2 + 1 + 1 = l.length by omega, List.drop_length]
  simp only [show l.length - 2 + 1 = l.length - 1 by omega]

theorem suffix_two (a b : UInt8) (l : List UInt8) :
    [a, b].isSuffixOf l = true ↔ ∃ h : 2 ≤ l.length, l[l.length - 2]'(by omega) = a ∧ l[l.length - 1]'(by omega) = b := by
  rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop]
  simp only [List.length_cons, List.length_nil]
  constructor
  · intro h
    have hl : 2 ≤ l.length := by
      have := congrArg List.length h; simp at this; omega
    refine ⟨hl, ?_⟩
    rw [drop_two l hl] at h
    simp only [List.cons.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  · rintro ⟨hl, h1, h2⟩
    rw [drop_two l hl, h1, h2]

theorem qnameB_eq (name : ByteArray) : (qnameB name).data.toList = qnameOf name.data.toList := by
  have hl : FQ.L name 0 = name.data.toList := by simp [FQ.L]
  have hs := spaceAt_eq name name.size 0 (Nat.zero_le _) (by omega)
  rw [hl, Nat.zero_add] at hs
  unfold qnameB qnameOf
  simp only []
  rw [hs]
  have e := @List.takeWhile_append_dropWhile _ (· != 32) name.data.toList
  have hlen : name.data.toList.length = name.size := by simp
  generalize name.data.toList.takeWhile (· != 32) = base at e ⊢
  generalize name.data.toList.dropWhile (· != 32) = rest at e
  have hpre : name.data.toList.take base.length = base := by rw [← e]; exact List.take_left' rfl
  have hle : base.length ≤ name.size := by rw [← hlen, ← e, List.length_append]; omega
  have hget : ∀ j (hj : j < base.length), name[j]! = base[j] := by
    intro j hj
    have hj' : j < name.data.toList.length := by omega
    rw [getElem!_pos name j (by omega), ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList hj',
      List.getElem_of_eq hpre.symm hj, List.getElem_take]
  have hx : ∀ e, e ≤ base.length → (name.extract 0 e).data.toList = base.take e := by
    intro e he
    rw [FQ.extract_list, hl, Nat.sub_zero, ← hpre, List.take_take, Nat.min_eq_left he]
  by_cases h2 : 2 ≤ base.length
  · have e2 := hget (base.length - 2) (by omega)
    have e1 := hget (base.length - 1) (by omega)
    have hdl : base.dropLast.dropLast = base.take (base.length - 2) := by
      rw [List.dropLast_eq_take, List.dropLast_eq_take, List.take_take, List.length_take]; congr 1; omega
    by_cases c : (base[base.length - 2]'(by omega) = 47) ∧
        (base[base.length - 1]'(by omega) = 49 ∨ base[base.length - 1]'(by omega) = 50)
    · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, e2, e1]; exact ⟨⟨h2, c.1⟩, c.2⟩),
        if_pos (by rw [Bool.or_eq_true, suffix_two, suffix_two]; rcases c.2 with c2 | c2
                   · exact Or.inl ⟨h2, c.1, c2⟩
                   · exact Or.inr ⟨h2, c.1, c2⟩), hdl, hx _ (by omega)]
    · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, e2, e1]
                     exact fun ⟨⟨_, a⟩, b⟩ => c ⟨a, b⟩),
        if_neg (by rw [Bool.or_eq_true, suffix_two, suffix_two]
                   rintro (⟨_, a, b⟩ | ⟨_, a, b⟩)
                   · exact c ⟨a, Or.inl b⟩
                   · exact c ⟨a, Or.inr b⟩),
        hx _ (Nat.le_refl _), List.take_length]
  · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega),
      if_neg (by rw [Bool.or_eq_true, suffix_two, suffix_two]; rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega),
      hx _ (Nat.le_refl _), List.take_length]

theorem qnameOkB_eq (q : ByteArray) : qnameOkB q = qnameOk q.data.toList := by
  unfold qnameOkB qnameOk
  have ha := FQ.allBytes_iff (fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)) q
  simp only [Array.length_toList, ByteArray.size_data]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [ha, List.all_eq_true]

end Spec

#print axioms Spec.qnameB_eq
#print axioms Spec.qnameOkB_eq
