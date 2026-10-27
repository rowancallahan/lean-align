import Spec.Fasta
import Spec.Fastq

/-! # SAM output: two lines per pair, with the pair answer in custom tags (XB best possible pair
score, XU uniqueness, XT tier). Unproved (trusted) formatting for the shim. -/

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

-- QNAME: the FASTQ name up to the first space, without a trailing /1 or /2
def samName (name : String) : String :=
  let name := (name.splitOn " ").headD name
  if name.endsWith "/1" || name.endsWith "/2" then (name.dropEnd 2).toString else name

-- SEQ and QUAL as on the forward strand of the reference: reversed (and complemented) on reverse
def samSequence (record : FastqRecord) (strand : Strand) : String × String :=
  match strand with
  | .forward => (String.ofList (decodeRead record.letters), record.quality)
  | .reverse => (String.ofList (reverseComplement (decodeRead record.letters)),
                 String.ofList record.quality.toList.reverse)

def uniquenessText : Uniqueness → String
  | .unique      => "unique"
  | .multimapper => "multimapper"
  | .unknown     => "unknown"

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

-- one SAM line: the eleven fields in SAM order, then the tags
def samLine (qname : String) (flag : Nat) (rname : String) (pos mapq : Nat) (cigar rnext : String)
    (pnext : Nat) (tlen : Int) (seq qual : String) (tags : List String) : String :=
  "\t".intercalate ([qname, toString flag, rname, toString pos, toString mapq, cigar, rnext,
    toString pnext, toString tlen, seq, qual] ++ tags)

-- a mate of a found pair: SAM positions are 1-based, so POS is start + 1
def mappedLine (chromosomes : ChromosomeList) (record : FastqRecord) (which : Mate)
    (mate other : MateReport) (answer : PairAnswer) : String :=
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
  let (seq, qual) := samSequence record mate.placement.strand
  samLine (samName record.name) flag rname (mate.placement.start + 1) (mapq answer)
    (cigarText mate.cigar) rnext (other.placement.start + 1) tlen seq qual
    (s!"AS:i:{mate.score}" :: answerTags answer)

-- a mate with no alignment reported
def unmappedLine (record : FastqRecord) (which : Mate) (tags : List String) : String :=
  let flag := flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which
  let (seq, qual) := samSequence record .forward
  samLine (samName record.name) flag "*" 0 0 "*" "*" 0 0 seq qual tags

-- the two SAM lines for one pair
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

end Spec
