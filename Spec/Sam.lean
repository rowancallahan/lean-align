import Spec.Fasta
import Spec.Fastq
import FastqIO
import ReadTrim
import AdapterTrim

/-! # From reads to SAM

* `ReadB.toRead`: the shim's reads (`ReadB`, bytes; FastqIO) are the spec's `FQ.Read`s.
* The QNAME rule (`qnameOf`): a read's name up to the first space, without a trailing "/1" or "/2". Mates are paired
  by it (the shim); a QNAME must be 1..254 bytes in '!'..'?' or 'A'..'~' (`qnameOk`).
* Trimming (`trimRead`): the adapter cut, the quality window, the minimum length (proved pieces; Proofs/TrimRecord.lean).
* SAM output: two lines per pair, with the pair answer in custom tags (XB best possible pair score, XU uniqueness,
  XT tier), written as bytes. Unproved (trusted) formatting for the shim. -/

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

-- `qnameOf` on bytes (`qnameB_eq`, Proofs/TrimRecord.lean)
def qnameB (name : ByteArray) : ByteArray :=
  let e := spaceAt name name.size 0
  if 2 ≤ e && name[e - 2]! == 47 && (name[e - 1]! == 49 || name[e - 1]! == 50) then name.extract 0 (e - 2)
  else name.extract 0 e

-- `qnameOk` on bytes (`qnameOkB_eq`)
def qnameOkB (q : ByteArray) : Bool :=
  0 < q.size && q.size ≤ 254 && allBytes (fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)) q

-- shortest mate kept after trimming; shorter mates become empty (trimmed away)
def minLength : Nat := 25

-- adapter cut, then quality trimming, then the minimum length, all with proved functions: cut letters
-- and qualities at the first TruSeq adapter, keep the best window, and drop a mate shorter than
-- `minLength`; a mate with nothing worth keeping comes back with no letters (trimmed away)
def trimBytes (letters qual : ByteArray) : ByteArray × ByteArray :=
  let (letters, qual) := AdapterTrim.cutTruSeq letters qual
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  AdapterTrim.dropShort minLength letters qual

-- a read, trimmed (the name is kept)
def trimRead (read : FQ.Read) : FQ.Read :=
  let trimmed := trimBytes ⟨read.sequence.toArray⟩ ⟨read.quality.toArray⟩
  ⟨read.name, trimmed.1.data.toList, trimmed.2.data.toList⟩

-- `trimRead` on the shim's reads (`trimReadB_toRead`)
def trimReadB (read : ReadB) : ReadB :=
  let trimmed := trimBytes read.seq read.qual
  { read with seq := trimmed.1, qual := trimmed.2 }

-- trim every pair of a chunk with `trimReadB`, in `parts` tasks running at once; the result is the
-- pairs in their original order, each trimmed (`trimChunk_eq`, Proofs/TrimRecord.lean)
def trimChunk (chunk : Array (ReadB × ReadB)) (parts : Nat) : Array (ReadB × ReadB) :=
  let size := (chunk.size + parts - 1) / parts
  let tasks := (List.range parts).map fun part => Task.spawn fun _ =>
    (chunk.extract (part * size) ((part + 1) * size)).map fun (read1, read2) => (trimReadB read1, trimReadB read2)
  tasks.foldl (fun out task => out ++ task.get) #[]

-- a chunk of read pairs, as `alignPairs` takes them: a mate trimmed away (no letters left) is `none`
def chunkPairs (chunk : Array (ReadB × ReadB)) : List (Option ByteArray × Option ByteArray) :=
  chunk.toList.map fun (read1, read2) =>
    (if read1.seq.isEmpty then none else some read1.seq,
     if read2.seq.isEmpty then none else some read2.seq)

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

def tierText : Tier → String
  | .eachMateUnique    => "eachMateUnique"
  | .quickSearchUnique => "quickSearchUnique"
  | .deepSearchUnique  => "deepSearchUnique"
  | .quickSearchTie    => "quickSearchTie"
  | .deepSearchTie     => "deepSearchTie"
  | .bestUnchecked     => "bestUnchecked"
  | .stoppedEarly      => "stoppedEarly"
  | .boundsOnly        => "boundsOnly"

-- MAPQ (stand-in): 60 when proved unique, else 0
def mapq (answer : PairAnswer) : Nat :=
  match answer.uniqueness with
  | .unique => 60
  | _       => 0

-- custom tags: XB best possible pair score, XU uniqueness, XT tier
def answerTags (answer : PairAnswer) : List String :=
  [s!"XB:i:{answer.bestPossibleScore}", s!"XU:Z:{uniquenessText answer.uniqueness}",
   s!"XT:Z:{tierText answer.tier}"]

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

-- a mate of a found pair: SAM positions are 1-based, so POS is start + 1
def mappedLine (b : ByteArray) (chromosomes : ChromosomeList) (read : ReadB) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) : ByteArray :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let rname := (chromosomes[mate.placement.chromosome]?.map (·.1)).getD "*"
  let rnext := if mate.placement.chromosome = other.placement.chromosome then "=" else
    (chromosomes[other.placement.chromosome]?.map (·.1)).getD "*"
  -- TLEN: leftmost start to rightmost stop; positive on the leftmost mate
  let left := min mate.placement.start other.placement.start
  let right := max mate.placement.stop other.placement.stop
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then right - left else -((right - left : Nat) : Int)
  let (seq, qual) := samSequence read mate.placement.strand
  samLine b (qnameB read.name) flag rname (mate.placement.start + 1) (mapq answer)
    (cigarText mate.cigar) rnext (other.placement.start + 1) tlen seq qual
    (s!"AS:i:{mate.score}" :: answerTags answer)

-- a mate with no alignment reported
def unmappedLine (b : ByteArray) (read : ReadB) (which : Mate) (tags : List String) : ByteArray :=
  let flag := flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which
  let (seq, qual) := samSequence read .forward
  samLine b (qnameB read.name) flag "*" 0 0 "*" "*" 0 0 seq qual tags

-- the two SAM lines of one pair, each with its newline, appended to `b`
def samLines (b : ByteArray) (chromosomes : ChromosomeList) (read1 read2 : ReadB) (result : PairResult) :
    ByteArray :=
  match result with
  | .trimmedAway mate =>
      let tags := [s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"]
      (unmappedLine ((unmappedLine b read1 .one tags).push 10) read2 .two tags).push 10
  | .aligned answer =>
      match answer.found with
      | some pair =>
          (mappedLine ((mappedLine b chromosomes read1 .one pair.mate1 pair.mate2 answer).push 10)
            chromosomes read2 .two pair.mate2 pair.mate1 answer).push 10
      | none =>
          (unmappedLine ((unmappedLine b read1 .one (answerTags answer)).push 10) read2 .two (answerTags answer)).push 10

-- one chunk's SAM text, in pair order (after the proved call)
def samChunk (chromosomes : ChromosomeList) (chunk : Array (ReadB × ReadB)) (results : List PairResult) : ByteArray :=
  (chunk.zip results.toArray).foldl (init := ByteArray.empty)
    fun bytes ((read1, read2), result) => samLines bytes chromosomes read1 read2 result

end Spec
