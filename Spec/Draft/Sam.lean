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

-- SEQ and QUAL on the reference's forward strand
def seqQual (r : FQ.Read) (strand : Strand) : List UInt8 × List UInt8 :=
  let complement (b : UInt8) : UInt8 :=
    match b with
    | 0x41 => 0x54
    | 0x54 => 0x41
    | 0x43 => 0x47
    | 0x47 => 0x43
    | _    => b
  match r.sequence, strand with
  | [], _       => (text "*", text "*")
  | s, .forward => (s, r.quality)
  | s, .reverse => ((s.map complement).reverse, r.quality.reverse)

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

-- one mate's SAM line, from the pair's result
def mateLine (chrs : ChromosomeList) (r : FQ.Read) (which : Mate) (result : PairResult) : List UInt8 :=
  let mateBit :=
    match which with
    | .one => 64
    | .two => 128
  -- where this mate and the other mate were placed (if found), the MAPQ, and the tags
  let (placed, mapq, tags) :=
    match result with
    | .trimmedAway .one => (none, 0, [text "XT:Z:trimmedAway1"])
    | .trimmedAway .two => (none, 0, [text "XT:Z:trimmedAway2"])
    | .aligned a =>
      let mapq :=
        match a.uniqueness with
        | .unique => 60
        | _       => 0
      match a.found, which with
      | some p, .one => (some (p.mate1, p.mate2), mapq, answerTags a)
      | some p, .two => (some (p.mate2, p.mate1), mapq, answerTags a)
      | none, _      => (none, 0, answerTags a)
  -- the fields that depend on the placement
  let (flag, rname, pos, cigarText, rnext, pnext, tlen, strand, score) :=
    match placed with
    | none =>
      (1 + 4 + 8 + mateBit, text "*", 0, text "*", text "*", 0, (0 : Int), Strand.forward, [])
    | some (me, other) =>
      let p := me.placement
      let o := other.placement
      let reverseBits :=
        match p.strand, o.strand with
        | .forward, .forward => 0
        | .reverse, .forward => 16
        | .forward, .reverse => 32
        | .reverse, .reverse => 48
      let flag := 1 + 2 + mateBit + reverseBits
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
      (flag, chrName chrs p.chromosome, p.start + 1, cigar me.cigar, rnext, o.start + 1, tlen, p.strand,
       [text s!"AS:i:{me.score}"])
  let (s, q) := seqQual r strand
  -- QNAME, FLAG, RNAME, POS, MAPQ, CIGAR, RNEXT, PNEXT, TLEN, SEQ, QUAL, tags
  line ([qname r.name, num flag, rname, num pos, num mapq, cigarText, rnext, num pnext, num tlen, s, q]
        ++ score ++ tags)

-- the header, then two lines per pair
def samFile (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) :
    List UInt8 :=
  header chrs ++ (pairs.zip results).flatMap fun ((r1, r2), result) =>
    mateLine chrs r1 .one result ++ mateLine chrs r2 .two result

end Spec.SamSpec
