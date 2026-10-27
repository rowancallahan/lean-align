-- Proofs/Answer.lean: Spec/Aligner.lean up to the two holes, unchanged (split out so Proofs/Bridge.lean can use it).
import Proofs.Mapping

/-! # 3. The aligner: what each answer proves. Statements only.
Scores are ≤ 0 and higher is better. Every answer reports a bound on the best proper pair, the
pair it found (if any), and what is known about uniqueness; these go into the output tags. -/

namespace Spec

-- settings: what counts as a proper pair's insert
structure InsertSettings where
  range         : Nat × Nat  -- allowed fragment length: min and max, both included
  dovetailSlack : Nat := 0

inductive Mate where
  | one
  | two
deriving DecidableEq, Repr

/-! ## What is reported -/

-- one mate's line in the output, as in SAM: where, how (CIGAR), and the score
structure MateReport where
  placement : Placement
  cigar     : Array (Step × Nat)
  score     : Int
deriving DecidableEq, Repr

structure PairReport where
  mate1 : MateReport
  mate2 : MateReport
deriving DecidableEq, Repr

-- the line this alignment would print
def GenomicAlignment.report {genome : Genome} {read : Read}
    (alignment : GenomicAlignment genome read) : MateReport :=
  ⟨alignment.placement, alignment.path.cigar, alignment.score⟩

-- the two lines this pair would print
def PairAlignment.report {genome : Genome} {mate1 mate2 : Read}
    (pair : PairAlignment genome mate1 mate2) : PairReport :=
  ⟨pair.first.report, pair.second.report⟩

/-! ## Best and unique -/

def PairAlignment.placements {genome : Genome} {mate1 mate2 : Read}
    (pair : PairAlignment genome mate1 mate2) : Placement × Placement :=
  (pair.first.placement, pair.second.placement)

-- proper, and no proper pair scores higher
def PairAlignment.IsBestProper {genome : Genome} {mate1 mate2 : Read}
    (insertSettings : InsertSettings) (pair : PairAlignment genome mate1 mate2) : Prop :=
  pair.IsProper insertSettings.range insertSettings.dovetailSlack ∧
  ∀ other : PairAlignment genome mate1 mate2,
    other.IsProper insertSettings.range insertSettings.dovetailSlack → other.score ≤ pair.score

-- best, and every proper pair at other placements scores strictly lower
def PairAlignment.IsUniqueBestProper {genome : Genome} {mate1 mate2 : Read}
    (insertSettings : InsertSettings) (pair : PairAlignment genome mate1 mate2) : Prop :=
  pair.IsBestProper insertSettings ∧
  ∀ other : PairAlignment genome mate1 mate2,
    other.IsProper insertSettings.range insertSettings.dovetailSlack →
    other.placements ≠ pair.placements → other.score < pair.score

/-! ## The answer -/

-- what is known about whether the best proper pair is unique
inductive Uniqueness where
  | unique       -- the reported pair is the unique best proper pair
  | multimapper  -- proved: the reported pair is a best proper pair, and another one ties with it
  | unknown      -- not checked
deriving DecidableEq, Repr

-- which router path answered: a performance record only, no claim
inductive Tier where
  | eachMateUnique      -- each mate the unique best on its own (cheapest test)
  | quickSearchUnique   -- pair search with both mates scoring at least -7: unique best pair
  | deepSearchUnique    -- pair search with both mates scoring at least -16: unique best pair
  | quickSearchTie      -- the -7 pair search found an exact tie
  | deepSearchTie       -- the -16 pair search found an exact tie
  | bestUnchecked       -- best proper pair proved, uniqueness not checked
  | stoppedEarly        -- stopped with a pair or bounds in hand, gap left
  | boundsOnly          -- no pair in hand, only score bounds
deriving DecidableEq, Repr

structure PairAnswer where
  found             : Option PairReport  -- a proper pair that was found (one of the tied ones for a multimapper)
  bestPossibleScore : Int                -- no proper pair scores higher
  uniqueness        : Uniqueness
  tier              : Tier
deriving Repr

inductive PairResult where
  | trimmedAway (mate : Mate)
  | aligned (answer : PairAnswer)
deriving Repr

def PairAnswer.Correct (insertSettings : InsertSettings) (genome : Genome) (mate1 mate2 : Read)
    (answer : PairAnswer) : Prop :=
  -- the pair found is a real proper pair, printed exactly
  (∀ report, answer.found = some report →
    ∃ pair : PairAlignment genome mate1 mate2,
      pair.report = report ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack) ∧
  -- the bound holds for every proper pair
  (∀ pair : PairAlignment genome mate1 mate2,
    pair.IsProper insertSettings.range insertSettings.dovetailSlack → pair.score ≤ answer.bestPossibleScore) ∧
  -- what is said about uniqueness is true
  (match answer.uniqueness with
   | .unique =>
       ∃ report, answer.found = some report ∧
       ∃ pair : PairAlignment genome mate1 mate2, pair.report = report ∧ pair.IsUniqueBestProper insertSettings
   | .multimapper =>
       ∃ report, answer.found = some report ∧
       ∃ pair other : PairAlignment genome mate1 mate2, pair.report = report ∧
         pair.IsBestProper insertSettings ∧ other.IsBestProper insertSettings ∧ pair.placements ≠ other.placements
   | .unknown => True)

-- `trimmed1`, `trimmed2` are the mates after trimming (`none` = trimmed away)
def PairResult.Correct (insertSettings : InsertSettings) (genome : Genome) (trimmed1 trimmed2 : Option Read) :
    PairResult → Prop
  | .trimmedAway .one => trimmed1 = none
  | .trimmedAway .two => trimmed2 = none
  | .aligned answer =>
      match trimmed1, trimmed2 with
      | some mate1, some mate2 => answer.Correct insertSettings genome mate1 mate2
      | _, _ => False  -- an aligned answer needs both mates

/-! ## Inputs as bytes, and the letters they stand for -/

-- a genome as read from its file: chromosome names, one byte per letter
abbrev GenomeFile := Array (String × ByteArray)

-- one byte per letter
def decodeRead (bytes : ByteArray) : Read :=
  bytes.toList.map fun byte => Char.ofNat byte.toNat

def GenomeFile.decode (byteGenome : GenomeFile) : Genome :=
  byteGenome.toList.map fun (name, sequence) => ⟨name, decodeRead sequence⟩

-- a pair of mates as bytes; a trimmed-away mate is `none`
def decodePair (bytes : Option ByteArray × Option ByteArray) : Option Read × Option Read :=
  (bytes.1.map decodeRead, bytes.2.map decodeRead)

-- the other direction, for stating the end-to-end theorem: letters to bytes, one byte per letter
def nucleotides : List Char := ['A', 'C', 'G', 'T', 'N']

def ReadIsDNA (read : Read) : Prop := ∀ letter ∈ read, letter ∈ nucleotides

def GenomeIsDNA (genome : Genome) : Prop := ∀ chromosome ∈ genome, ReadIsDNA chromosome.seq

def MatesAreDNA (mates : Option Read × Option Read) : Prop :=
  (∀ read ∈ mates.1, ReadIsDNA read) ∧ (∀ read ∈ mates.2, ReadIsDNA read)

def encodeRead (read : Read) : ByteArray :=
  ⟨(read.map fun letter => letter.toNat.toUInt8).toArray⟩

def Genome.encode (genome : Genome) : GenomeFile :=
  (genome.map fun chromosome => (chromosome.name, encodeRead chromosome.seq)).toArray

def encodePair (mates : Option Read × Option Read) : Option ByteArray × Option ByteArray :=
  (mates.1.map encodeRead, mates.2.map encodeRead)

end Spec
