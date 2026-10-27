import Proofs.Alignment

/-! # 2. Mapping, proved. Same statements as `Spec/Mapping.lean`, with the proofs filled in.
One read on the genome, then pairs.
Statements only. Scores use `defaultScoring`; higher is better, all scores are ≤ 0.
Positions are 0-based and half-open: a placement covers letters start ≤ i < stop. -/

namespace Spec

structure Chromosome where
  name : String
  seq  : List Char

abbrev Genome := List Chromosome

inductive Strand where
  | forward
  | reverse
deriving DecidableEq, Repr

-- A, C, G, T are complemented; other letters are kept
def complement : Char → Char
  | 'A' => 'T'
  | 'C' => 'G'
  | 'G' => 'C'
  | 'T' => 'A'
  | c => c

def reverseComplement (read : Read) : Read := (read.map complement).reverse

-- the read as it is aligned on a strand
def Strand.orient (strand : Strand) (read : Read) : Read :=
  match strand with
  | .forward => read
  | .reverse => reverseComplement read

/-! ## One read on the genome -/

structure Placement where
  chromosome : Nat  -- index in the genome
  start      : Nat
  stop       : Nat
  strand     : Strand
deriving DecidableEq, Repr

-- the genome letters under a placement; none if it does not fit its chromosome
def Placement.reference (genome : Genome) (placement : Placement) : Option Read :=
  match genome[placement.chromosome]? with
  | some chromosome =>
      if placement.start ≤ placement.stop ∧ placement.stop ≤ chromosome.seq.length then
        some ((chromosome.seq.drop placement.start).take (placement.stop - placement.start))
      else none
  | none => none

-- a placement that fits, and a path of the read (on its strand) against the letters there
structure GenomicAlignment (genome : Genome) (read : Read) where
  placement : Placement
  reference : Read
  fits      : placement.reference genome = some reference
  path      : Path (placement.strand.orient read) reference

def GenomicAlignment.score {genome : Genome} {read : Read}
    (alignment : GenomicAlignment genome read) : Int :=
  alignment.path.score defaultScoring

-- best anywhere, and every alignment at a different placement scores strictly lower (no ties)
def GenomicAlignment.IsUniqueBest {genome : Genome} {read : Read}
    (alignment : GenomicAlignment genome read) : Prop :=
  ∀ other : GenomicAlignment genome read,
    other.score ≤ alignment.score ∧
    (other.placement ≠ alignment.placement → other.score < alignment.score)

theorem scoreWalk_nonpos (scoring : Scoring) (steps : List Step) (query reference : Read)
    (previous : Option Step) : scoreWalk scoring steps query reference previous ≤ 0 := by
  have := scoring.hMatch; have := scoring.hMismatch; have := scoring.hGapOpen; have := scoring.hGapExtend
  fun_induction scoreWalk scoring steps query reference previous <;> (try split) <;> omega

theorem GenomicAlignment.score_nonpos {genome : Genome} {read : Read}
    (alignment : GenomicAlignment genome read) : alignment.score ≤ 0 :=
  scoreWalk_nonpos _ _ _ _ _

-- the read against an empty stretch at the start of the first chromosome: all gapY
def GenomicAlignment.empty (chromosome : Chromosome) (rest : Genome) (read : Read) :
    GenomicAlignment (chromosome :: rest) read where
  placement := ⟨0, 0, 0, .forward⟩
  reference := []
  fits := by simp [Placement.reference]
  path := ⟨List.replicate read.length .gapY, by simp [Strand.orient, List.count_replicate],
    by simp [List.count_replicate]⟩

-- a non-empty genome always has a best alignment, so "best" is never vacuous
theorem exists_best (genome : Genome) (read : Read) (nonempty : genome ≠ []) :
    ∃ best : GenomicAlignment genome read,
      ∀ other : GenomicAlignment genome read, other.score ≤ best.score := by
  obtain ⟨chromosome, rest, rfl⟩ : ∃ c r, genome = c :: r := by
    cases genome with
    | nil => exact absurd rfl nonempty
    | cons c r => exact ⟨c, r, rfl⟩
  let start := GenomicAlignment.empty chromosome rest read
  apply Classical.byContradiction
  intro hno
  simp only [not_exists, Classical.not_forall, Int.not_le] at hno
  -- with no best, scores climb by at least one forever, past the ceiling of 0
  have climb : ∀ k : Nat, ∃ a : GenomicAlignment (chromosome :: rest) read, start.score + k ≤ a.score := by
    intro k
    induction k with
    | zero => exact ⟨start, by simp⟩
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hno a
      exact ⟨b, by omega⟩
  obtain ⟨a, ha⟩ := climb (start.score.natAbs + 1)
  have := a.score_nonpos
  omega

/-! ## A read pair on the genome -/

-- an alignment of each mate
structure PairAlignment (genome : Genome) (mate1 mate2 : Read) where
  first  : GenomicAlignment genome mate1
  second : GenomicAlignment genome mate2

def PairAlignment.score {genome : Genome} {mate1 mate2 : Read}
    (pair : PairAlignment genome mate1 mate2) : Int :=
  pair.first.score + pair.second.score

def PairAlignment.IsProper {genome : Genome} {mate1 mate2 : Read}
    (pair : PairAlignment genome mate1 mate2) (fragmentRange : Nat × Nat) (dovetailSlack : Nat) : Prop :=
  let (minFragment, maxFragment) := fragmentRange
  let first := pair.first.placement
  let second := pair.second.placement
  let (forwardMate, reverseMate) := if first.strand = .forward then (first, second) else (second, first)
  let fragment := reverseMate.stop - forwardMate.start
  -- same chromosome, opposite strands
  first.chromosome = second.chromosome ∧
  first.strand ≠ second.strand ∧
  -- facing each other: the forward mate starts no later than the reverse mate stops
  forwardMate.start ≤ reverseMate.stop ∧
  -- fragment (forward start to reverse stop) within the allowed range
  minFragment ≤ fragment ∧
  fragment ≤ maxFragment ∧
  -- no dovetailing: neither mate reaches past the other's outer end by more than the slack
  forwardMate.start ≤ reverseMate.start + dovetailSlack ∧
  forwardMate.stop ≤ reverseMate.stop + dovetailSlack

end Spec

#print axioms Spec.exists_best
