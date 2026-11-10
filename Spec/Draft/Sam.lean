import Spec.Aligner
import Spec.Fasta
import Spec.Fastq

namespace Spec.SamSpec
open Spec

def text (s : String) : List UInt8 := s.toUTF8.toList
def num (n : Int) : List UInt8 := text (toString n)
def line (fields : List (List UInt8)) : List UInt8 := (List.intercalate [9] fields) ++ [10]

def header (chromosomes : ChromosomeList) : List UInt8 :=
  line [text "@HD", text "VN:1.6", text "SO:unsorted"] ++
  (chromosomes.toList.flatMap fun (name, len) => line [text "@SQ", text ("SN:" ++ name), text s!"LN:{len}"]) ++
  line [text "@PG", text "ID:lean-align", text "PN:lean-align"]

def qname (name : List UInt8) : List UInt8 :=
  let base := name.takeWhile (· != 32)
  if [47, 49].isSuffixOf base || [47, 50].isSuffixOf base then base.dropLast.dropLast else base

def qnameOk (q : List UInt8) : Bool :=
  0 < q.length && q.length ≤ 254 && q.all fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)

def complement (b : UInt8) : UInt8 :=
  if b = 65 then 84 else if b = 84 then 65 else if b = 67 then 71 else if b = 71 then 67 else b

def cigar (c : Array (Step × Nat)) : List UInt8 :=
  c.toList.flatMap fun (step, n) => num n ++ text (match step with | .diag => "M" | .gapY => "I" | .gapX => "D")

def tags (a : PairAnswer) : List (List UInt8) :=
  [text s!"XB:i:{a.bestPossibleScore}", text ("XU:Z:" ++ match a.uniqueness with
     | .unique => "unique" | .multimapper => "multimapper" | .unknown => "unknown"
     | .repetitiveUnknown => "repetitiveUnknown"),
   text ("XT:Z:" ++ match a.tier with
     | .eachMateUnique => "eachMateUnique" | .quickSearchUnique => "quickSearchUnique"
     | .deepSearchUnique => "deepSearchUnique" | .quickSearchTie => "quickSearchTie"
     | .deepSearchTie => "deepSearchTie" | .bestUnchecked => "bestUnchecked"
     | .stoppedEarly => "stoppedEarly" | .boundsOnly => "boundsOnly")]

def mateBit : Mate → Nat | .one => 64 | .two => 128
def revBit (s : Strand) (bit : Nat) : Nat := if s = .reverse then bit else 0

def mapped (chrs : ChromosomeList) (r : FQ.Read) (which : Mate) (me other : MateReport) (a : PairAnswer) :
    List UInt8 :=
  let p := me.placement; let o := other.placement
  let chr (i : Nat) := text ((chrs[i]?.map (·.1)).getD "*")
  let len : Int := (max p.stop o.stop - min p.start o.start : Nat)
  let leftmost := p.start < o.start || (p.start = o.start && which = .one)
  let (s, q) := if r.sequence = [] then (text "*", text "*")
    else if p.strand = .reverse then ((r.sequence.map complement).reverse, r.quality.reverse) else (r.sequence, r.quality)
  line ([qname r.name, num (1 + 2 + mateBit which + revBit p.strand 16 + revBit o.strand 32), chr p.chromosome,
    num (p.start + 1), num (if a.uniqueness = .unique then 60 else 0), cigar me.cigar,
    if p.chromosome = o.chromosome then text "=" else chr o.chromosome, num (o.start + 1),
    num (if leftmost then len else -len), s, q, text s!"AS:i:{me.score}"] ++ tags a)

def unmapped (r : FQ.Read) (which : Mate) (t : List (List UInt8)) : List UInt8 :=
  let (s, q) := if r.sequence = [] then (text "*", text "*") else (r.sequence, r.quality)
  line ([qname r.name, num (1 + 4 + 8 + mateBit which), text "*", num 0, num 0, text "*", text "*",
    num 0, num 0, s, q] ++ t)

def pairLines (chrs : ChromosomeList) (r1 r2 : FQ.Read) : PairResult → List UInt8
  | .trimmedAway m =>
    let t := [text s!"XT:Z:trimmedAway{if m = .one then 1 else 2}"]
    unmapped r1 .one t ++ unmapped r2 .two t
  | .aligned a => match a.found with
    | some p => mapped chrs r1 .one p.mate1 p.mate2 a ++ mapped chrs r2 .two p.mate2 p.mate1 a
    | none   => unmapped r1 .one (tags a) ++ unmapped r2 .two (tags a)

def samFile (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) : List UInt8 :=
  header chrs ++ ((pairs.zip results).flatMap fun ((r1, r2), res) => pairLines chrs r1 r2 res)

end Spec.SamSpec
