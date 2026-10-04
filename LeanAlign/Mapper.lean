/-!
# Read mapper: input and output shapes (pure; not yet wired into `Main.lean`)

Input, for the genome file and for the reads file: lines alternate `>name`
and a sequence line.  Empty lines are skipped.

Output ("partial SAM"): one line per read with the 11 mandatory SAM fields,
tab separated.  QNAME, RNAME, POS (1-based) and CIGAR are filled; the other
seven are `NA` for now.

The index, the seeding and the theorem against a mapping spec are not written
yet.
-/

namespace LeanAlign
namespace Mapper

/-- A named sequence: a chromosome or a read. -/
structure Named where
  name : String
  seq : Array Char

/-- `>name` line, then a sequence line. -/
def parseNamed : List String → Except String (List Named)
  | [] => .ok []
  | [_] => .error "odd number of lines"
  | n :: s :: rest =>
    if n.startsWith ">" then
      match parseNamed rest with
      | .ok xs => .ok ({ name := String.ofList (n.toList.drop 1), seq := s.toList.toArray } :: xs)
      | .error e => .error e
    else .error "expected a '>name' line"

/-- Where one read maps. -/
structure Hit where
  read : String
  chromosome : String
  position : Nat        -- 1-based
  cigar : String

/-- QNAME FLAG RNAME POS MAPQ CIGAR RNEXT PNEXT TLEN SEQ QUAL -/
def partialSamLine (h : Hit) : String :=
  "\t".intercalate [h.read, "NA", h.chromosome, toString h.position, "NA", h.cigar,
    "NA", "NA", "NA", "NA", "NA"]

end Mapper
end LeanAlign
