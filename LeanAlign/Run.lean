import AlignmentWfaU32Kernel3

/-!
# Bytes in, bytes out (pure)

`run sc input` is the whole computation of the tool: decode the input file,
align every pair with the proved kernel `wfaAlignU3`, and encode the result.
Nothing here runs in `IO`.

Input (`.seq`): lines alternate `>A` and `<B`; each such pair of lines is one
pair of sequences.  Empty lines are skipped.

Output: one line per pair, `score<TAB>cigar`.  The CIGAR uses `M` for a
column that consumes a letter of both sequences (match or mismatch), `I` for a
letter of B only, `D` for a letter of A only.

What is proved about `run` is in `spec/Run.lean`.
-/

namespace LeanAlign

open AlignmentSpec

/-- Scores the tool uses: match 0, mismatch −4, gap open −6, gap extend −2
(a gap of length k scores −6 − 2k). -/
def scoring : Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

/-- The kernel the tool runs.  Its theorems: `wfaAlignU3_score`,
`wfaAlignU3_sound`, `wfaAlignU3_isSome` (codecs/wfa_u32). -/
def alignPair (sc : Scoring) (a b : Array Char) : Option (Array (Step × Nat) × Int) :=
  wfaAlignU3 sc a b

def stepLetter : Step → Char
  | .diag => 'M'
  | .gapX => 'I'
  | .gapY => 'D'

/-- Join neighbouring runs of the same step. -/
def mergeRuns : List (Step × Nat) → List (Step × Nat)
  | (s, n) :: (t, k) :: rest =>
    if s == t then mergeRuns ((s, n + k) :: rest) else (s, n) :: mergeRuns ((t, k) :: rest)
  | runs => runs
termination_by runs => runs.length

/-- Run-length CIGAR text. -/
def cigarText (c : Array (Step × Nat)) : String :=
  String.join ((mergeRuns c.toList).map fun (s, n) => (toString n).push (stepLetter s))

/-- One output line (without the newline). -/
def resultLine (r : Array (Step × Nat) × Int) : String :=
  toString r.2 ++ "\t" ++ cigarText r.1

/-- Pair up the lines: `>A` then `<B`.  Anything else is an error. -/
def readPairs : List String → Except String (List (Array Char × Array Char))
  | [] => .ok []
  | [_] => .error "odd number of sequence lines"
  | a :: b :: rest =>
    if a.startsWith ">" && b.startsWith "<" then
      match readPairs rest with
      | .ok ps => .ok (((a.toList.drop 1).toArray, (b.toList.drop 1).toArray) :: ps)
      | .error e => .error e
    else .error "expected a '>' line followed by a '<' line"

/-- Align every pair; one line each. -/
def alignLines (sc : Scoring) : List (Array Char × Array Char) → Except String (List String)
  | [] => .ok []
  | (a, b) :: rest =>
    match alignPair sc a b with
    | none => .error "kernel returned no result"   -- unreachable: `wfaAlignU3_isSome`
    | some r =>
      match alignLines sc rest with
      | .ok ls => .ok (resultLine r :: ls)
      | .error e => .error e

/-- The whole tool as a function from the input file's bytes to the output
file's bytes. -/
def run (sc : Scoring) (input : ByteArray) : Except String ByteArray :=
  match String.fromUTF8? input with
  | none => .error "input is not UTF-8"
  | some text =>
    match readPairs ((text.splitOn "\n").filter (· ≠ "")) with
    | .error e => .error e
    | .ok pairs =>
      match alignLines sc pairs with
      | .error e => .error e
      | .ok lines => .ok (String.join (lines.map (· ++ "\n"))).toUTF8

end LeanAlign
