import Spec.Aligner
import Spec.Fasta
import Spec.Fastq

namespace Spec.SamSpec
open Spec

def text (s : String) : List UInt8 := s.toUTF8.toList
def num (n : Int) : List UInt8 := text (toString n)
def line (fields : List (List UInt8)) : List UInt8 := List.intercalate [9] fields ++ [10]

def header (chrs : ChromosomeList) : List UInt8 :=
  line [text "@HD", text "VN:1.6", text "SO:unsorted"] ++
  chrs.toList.flatMap (fun (name, len) => line [text "@SQ", text s!"SN:{name}", text s!"LN:{len}"]) ++
  line [text "@PG", text "ID:lean-align", text "PN:lean-align"]

-- the name up to the first space, without /1 or /2
def qname (name : List UInt8) : List UInt8 :=
  let base := name.takeWhile (· != 32)
  match base.reverse with
  | 0x31 :: 0x2F :: rest | 0x32 :: 0x2F :: rest =>
    rest.reverse
  | _ =>
    base

def qnameOk (q : List UInt8) : Bool :=
  0 < q.length && q.length ≤ 254 && q.all fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)

def chrName (chrs : ChromosomeList) (i : Nat) : List UInt8 :=
  match chrs[i]? with
  | some (name, _) => text name
  | none           => text "*"

def cigar (c : Array (Step × Nat)) : List UInt8 :=
  c.toList.flatMap fun (step, n) => num n ++
    match step with
    | .diag => text "M"
    | .gapY => text "I"
    | .gapX => text "D"

def complement (b : UInt8) : UInt8 :=
  match b with
  | 0x41 => 0x54
  | 0x54 => 0x41
  | 0x43 => 0x47
  | 0x47 => 0x43
  | _    => b

-- SEQ and QUAL on the reference's forward strand
def seqQual (r : FQ.Read) (strand : Strand) : List UInt8 × List UInt8 :=
  match r.sequence, strand with
  | [], _       => (text "*", text "*")
  | s, .forward => (s, r.quality)
  | s, .reverse => ((s.map complement).reverse, r.quality.reverse)

def mateBit (which : Mate) : Nat :=
  match which with
  | .one => 64
  | .two => 128

def strandBit (strand : Strand) (bit : Nat) : Nat :=
  match strand with
  | .forward => 0
  | .reverse => bit

def answerTags (a : PairAnswer) : List (List UInt8) :=
  let uniqueness :=
    match a.uniqueness with
    | .unique            => "unique"
    | .multimapper       => "multimapper"
    | .unknown           => "unknown"
    | .repetitiveUnknown => "repetitiveUnknown"
  let tier :=
    match a.tier with
    | .eachMateUnique    => "eachMateUnique"
    | .quickSearchUnique => "quickSearchUnique"
    | .deepSearchUnique  => "deepSearchUnique"
    | .quickSearchTie    => "quickSearchTie"
    | .deepSearchTie     => "deepSearchTie"
    | .bestUnchecked     => "bestUnchecked"
    | .stoppedEarly      => "stoppedEarly"
    | .boundsOnly        => "boundsOnly"
  [text s!"XB:i:{a.bestPossibleScore}", text s!"XU:Z:{uniqueness}", text s!"XT:Z:{tier}"]

-- one mate's line; `placed` is where it and its mate were placed
def mateLine (chrs : ChromosomeList) (r : FQ.Read) (which : Mate) (mapq : Nat)
    (tags : List (List UInt8)) (placed : Option (MateReport × MateReport)) : List UInt8 :=
  match placed with
  | none =>
    let (s, q) := seqQual r .forward
    let flag := 1 + 4 + 8 + mateBit which
    -- QNAME, FLAG, RNAME, POS, MAPQ, CIGAR, RNEXT, PNEXT, TLEN, SEQ, QUAL, tags
    line ([qname r.name, num flag, text "*", num 0, num 0, text "*",
           text "*", num 0, num 0, s, q] ++ tags)
  | some (me, other) =>
    let p := me.placement
    let o := other.placement
    let (s, q) := seqQual r p.strand
    let flag := 1 + 2 + mateBit which + strandBit p.strand 16 + strandBit o.strand 32
    let rnext :=
      match decide (p.chromosome = o.chromosome) with
      | true  => text "="
      | false => chrName chrs o.chromosome
    -- TLEN: positive on the leftmost mate (mate 1 on a tie)
    let span : Int := (max p.stop o.stop - min p.start o.start : Nat)
    let tlen :=
      match compare p.start o.start, which with
      | .lt, _ | .eq, .one => span
      | _, _               => -span
    -- QNAME, FLAG, RNAME, POS, MAPQ, CIGAR, RNEXT, PNEXT, TLEN, SEQ, QUAL, tags
    line ([qname r.name, num flag, chrName chrs p.chromosome, num (p.start + 1), num mapq, cigar me.cigar,
           rnext, num (o.start + 1), num tlen, s, q, text s!"AS:i:{me.score}"] ++ tags)

-- the header, then two lines per pair
def samFile (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) :
    List UInt8 :=
  header chrs ++ (pairs.zip results).flatMap fun ((r1, r2), result) =>
    let (placed1, placed2, mapq, tags) :=
      match result with
      | .trimmedAway .one =>
        (none, none, 0, [text "XT:Z:trimmedAway1"])
      | .trimmedAway .two =>
        (none, none, 0, [text "XT:Z:trimmedAway2"])
      | .aligned a =>
        let mapq :=
          match a.uniqueness with
          | .unique => 60
          | _       => 0
        match a.found with
        | some pair => (some (pair.mate1, pair.mate2), some (pair.mate2, pair.mate1), mapq, answerTags a)
        | none      => (none, none, mapq, answerTags a)
    mateLine chrs r1 .one mapq tags placed1 ++ mateLine chrs r2 .two mapq tags placed2

end Spec.SamSpec
