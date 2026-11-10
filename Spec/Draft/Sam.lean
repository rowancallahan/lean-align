import Spec.Aligner
import Spec.Fasta
import Spec.Fastq

namespace Spec.SamSpec
open Spec

def text (s : String) : List UInt8 := s.toUTF8.toList
def num (n : Int) : List UInt8 := text (toString n)
def line (fields : List (List UInt8)) : List UInt8 := List.intercalate [9] fields ++ [10]

def qname (name : List UInt8) : List UInt8 :=
  let base := name.takeWhile (· != 32)
  match base.reverse with
  | 0x31 :: 0x2F :: rest | 0x32 :: 0x2F :: rest => rest.reverse
  | _ => base

def qnameOk (q : List UInt8) : Bool :=
  0 < q.length && q.length ≤ 254 && q.all fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)

def complement : UInt8 → UInt8
  | 0x41 => 0x54 | 0x54 => 0x41 | 0x43 => 0x47 | 0x47 => 0x43 | b => b

def header (chrs : ChromosomeList) : List UInt8 :=
  line [text "@HD", text "VN:1.6", text "SO:unsorted"] ++
  chrs.toList.flatMap (fun (name, len) => line [text "@SQ", text s!"SN:{name}", text s!"LN:{len}"]) ++
  line [text "@PG", text "ID:lean-align", text "PN:lean-align"]

def chrName (chrs : ChromosomeList) (i : Nat) : List UInt8 :=
  match chrs[i]? with
  | some (name, _) => text name
  | none => text "*"

def cigar (c : Array (Step × Nat)) : List UInt8 :=
  c.toList.flatMap fun (step, n) => num n ++ match step with
    | .diag => text "M" | .gapY => text "I" | .gapX => text "D"

def mateBit : Mate → Nat
  | .one => 64 | .two => 128

def reverseBit (bit : Nat) : Strand → Nat
  | .forward => 0 | .reverse => bit

def seqQual (r : FQ.Read) (strand : Strand) : List UInt8 × List UInt8 :=
  match r.sequence, strand with
  | [], _        => (text "*", text "*")
  | s, .forward  => (s, r.quality)
  | s, .reverse  => ((s.map complement).reverse, r.quality.reverse)

def mapq (a : PairAnswer) : Nat :=
  match a.uniqueness with
  | .unique => 60 | _ => 0

def answerTags (a : PairAnswer) : List (List UInt8) :=
  [text s!"XB:i:{a.bestPossibleScore}",
   text ("XU:Z:" ++ match a.uniqueness with
     | .unique => "unique" | .multimapper => "multimapper" | .unknown => "unknown"
     | .repetitiveUnknown => "repetitiveUnknown"),
   text ("XT:Z:" ++ match a.tier with
     | .eachMateUnique => "eachMateUnique" | .quickSearchUnique => "quickSearchUnique"
     | .deepSearchUnique => "deepSearchUnique" | .quickSearchTie => "quickSearchTie"
     | .deepSearchTie => "deepSearchTie" | .bestUnchecked => "bestUnchecked"
     | .stoppedEarly => "stoppedEarly" | .boundsOnly => "boundsOnly")]

-- TLEN: leftmost start to rightmost stop, positive on the leftmost mate (mate 1 on a tie)
def tlen (which : Mate) (p o : Placement) : Int :=
  let len : Int := (max p.stop o.stop - min p.start o.start : Nat)
  match compare p.start o.start, which with
  | .lt, _ | .eq, .one => len
  | _, _               => -len

def mapped (chrs : ChromosomeList) (r : FQ.Read) (which : Mate) (me other : MateReport) (a : PairAnswer) :
    List UInt8 :=
  let p := me.placement
  let o := other.placement
  let (s, q) := seqQual r p.strand
  let rnext := match decide (p.chromosome = o.chromosome) with
    | true => text "=" | false => chrName chrs o.chromosome
  line ([qname r.name,
         num (1 + 2 + mateBit which + reverseBit 16 p.strand + reverseBit 32 o.strand),
         chrName chrs p.chromosome, num (p.start + 1), num (mapq a), cigar me.cigar,
         rnext, num (o.start + 1), num (tlen which p o), s, q,
         text s!"AS:i:{me.score}"] ++ answerTags a)

def unmapped (r : FQ.Read) (which : Mate) (tags : List (List UInt8)) : List UInt8 :=
  let (s, q) := seqQual r .forward
  line ([qname r.name, num (1 + 4 + 8 + mateBit which), text "*", num 0, num 0, text "*", text "*",
         num 0, num 0, s, q] ++ tags)

def pairLines (chrs : ChromosomeList) (r1 r2 : FQ.Read) : PairResult → List UInt8
  | .trimmedAway m =>
    let tags := [text ("XT:Z:trimmedAway" ++ match m with | .one => "1" | .two => "2")]
    unmapped r1 .one tags ++ unmapped r2 .two tags
  | .aligned a =>
    match a.found with
    | some pair => mapped chrs r1 .one pair.mate1 pair.mate2 a ++ mapped chrs r2 .two pair.mate2 pair.mate1 a
    | none      => unmapped r1 .one (answerTags a) ++ unmapped r2 .two (answerTags a)

def samFile (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) : List UInt8 :=
  header chrs ++ (pairs.zip results).flatMap fun ((r1, r2), result) => pairLines chrs r1 r2 result

end Spec.SamSpec
