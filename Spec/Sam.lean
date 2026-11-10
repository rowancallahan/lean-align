-- LOCKED (Rowan, 2026-11-10): the SAM output spec. Rowan still has to re-check it line by line.
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

-- where this mate and the other mate were placed (none: not placed)
def placed (which : Mate) (result : PairResult) : Option (MateReport × MateReport) :=
  match result, which with
  | .aligned a, .one     => a.found.map fun pair => (pair.mate1, pair.mate2)
  | .aligned a, .two     => a.found.map fun pair => (pair.mate2, pair.mate1)
  | .trimmedAway _, _    => none

def reverseBit (m : MateReport) (bit : Nat) : Nat :=
  match m.placement.strand with
  | .forward => 0
  | .reverse => bit

def flag (which : Mate) (p : Option (MateReport × MateReport)) : Nat :=
  let mateBit :=
    match which with
    | .one => 64
    | .two => 128
  match p with
  | none             => 1 + 4 + 8 + mateBit
  | some (me, other) => 1 + 2 + mateBit + reverseBit me 16 + reverseBit other 32

def rname (chrs : ChromosomeList) (p : Option (MateReport × MateReport)) : List UInt8 :=
  match p with
  | none         => text "*"
  | some (me, _) => chrName chrs me.placement.chromosome

def pos (p : Option (MateReport × MateReport)) : Nat :=
  match p with
  | none         => 0
  | some (me, _) => me.placement.start + 1

def mapq (result : PairResult) (p : Option (MateReport × MateReport)) : Nat :=
  match result, p with
  | .aligned a, some _ =>
    match a.uniqueness with
    | .unique => 60
    | _       => 0
  | _, _ => 0

def cigar (p : Option (MateReport × MateReport)) : List UInt8 :=
  let letter (step : Step) : String :=
    match step with
    | .diag => "M"
    | .gapY => "I"
    | .gapX => "D"
  match p with
  | none         => text "*"
  | some (me, _) => me.cigar.toList.flatMap fun (step, n) => num n ++ text (letter step)

def rnext (chrs : ChromosomeList) (p : Option (MateReport × MateReport)) : List UInt8 :=
  match p with
  | none => text "*"
  | some (me, other) =>
    match decide (me.placement.chromosome = other.placement.chromosome) with
    | true  => text "="
    | false => chrName chrs other.placement.chromosome

def pnext (p : Option (MateReport × MateReport)) : Nat :=
  match p with
  | none            => 0
  | some (_, other) => other.placement.start + 1

-- leftmost start to rightmost stop, positive on the leftmost mate (mate 1 on a tie)
def tlen (which : Mate) (p : Option (MateReport × MateReport)) : Int :=
  match p with
  | none => 0
  | some (me, other) =>
    let a := me.placement
    let b := other.placement
    let span : Int := (max a.stop b.stop - min a.start b.start : Nat)
    match compare a.start b.start, which with
    | .lt, _ | .eq, .one => span
    | _, _               => -span

def strand (p : Option (MateReport × MateReport)) : Strand :=
  match p with
  | none         => .forward
  | some (me, _) => me.placement.strand

-- SEQ on the reference's forward strand: reverse-complemented on the reverse strand
def seq (r : FQ.Read) (p : Option (MateReport × MateReport)) : List UInt8 :=
  let complement (b : UInt8) : UInt8 :=
    match b with
    | 0x41 => 0x54
    | 0x54 => 0x41
    | 0x43 => 0x47
    | 0x47 => 0x43
    | _    => b
  match r.sequence, strand p with
  | [], _       => text "*"
  | s, .forward => s
  | s, .reverse => (s.map complement).reverse

def qual (r : FQ.Read) (p : Option (MateReport × MateReport)) : List UInt8 :=
  match r.sequence, strand p with
  | [], _       => text "*"
  | _, .forward => r.quality
  | _, .reverse => r.quality.reverse

-- AS (this mate's score), XB (no pair scores higher), XU (uniqueness)
def tags (result : PairResult) (p : Option (MateReport × MateReport)) : List (List UInt8) :=
  let score :=
    match p with
    | none         => []
    | some (me, _) => [text s!"AS:i:{me.score}"]
  let answer :=
    match result with
    | .trimmedAway .one => [text "XT:Z:trimmedAway1"]
    | .trimmedAway .two => [text "XT:Z:trimmedAway2"]
    | .aligned a =>
      let uniqueness :=
        match a.uniqueness with
        | .unique            => "unique"
        | .multimapper       => "multimapper"
        | .unknown           => "unknown"
        | .repetitiveUnknown => "repetitiveUnknown"
      -- tier (XT) left out for now
      [text s!"XB:i:{a.bestPossibleScore}", text s!"XU:Z:{uniqueness}"]
  score ++ answer

def mateLine (chrs : ChromosomeList) (r : FQ.Read) (which : Mate) (result : PairResult) : List UInt8 :=
  let p := placed which result
  line ([qname r.name,           -- QNAME
         num (flag which p),     -- FLAG
         rname chrs p,           -- RNAME
         num (pos p),            -- POS
         num (mapq result p),    -- MAPQ
         cigar p,                -- CIGAR
         rnext chrs p,           -- RNEXT
         num (pnext p),          -- PNEXT
         num (tlen which p),     -- TLEN
         seq r p,                -- SEQ
         qual r p]               -- QUAL
        ++ tags result p)

-- the two lines of one pair
def pairLines (chrs : ChromosomeList) (r1 r2 : FQ.Read) (result : PairResult) : List UInt8 :=
  (mateLine chrs r1 .one result) ++ (mateLine chrs r2 .two result)

-- the lines of every pair, in order
def body (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) :
    List UInt8 :=
  (List.map (fun ((r1, r2), result) => pairLines chrs r1 r2 result) (List.zip pairs results)).flatten

def samFile (chrs : ChromosomeList) (pairs : List (FQ.Read × FQ.Read)) (results : List PairResult) :
    List UInt8 :=
  (header chrs) ++ (body chrs pairs results)

end Spec.SamSpec
