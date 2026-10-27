import new_spec.statements.Alignment

/-!
# 2. Placing reads on a genome: one read, pairs, uniqueness, floors

Statements only: every proof is `sorry`. Imports only Alignment.

These are the definitions the proofs use, with the same bodies and the same signs, renamed
to full names: spec/MapSpec.lean, spec/PairSpec.lean, spec/PairSpecU.lean, `pairSpecT`
(codecs/PairDispatch.lean), `PairTieOk` (codecs/PairLadder.lean), and `MateFloor`,
`strandRead`, `CigarOk` (codecs/TierRouter.lean). Scores are at most 0 and are maximized;
a threshold keeps windows scoring at least the threshold (a penalty cap `P` is the
threshold `-P`). The frozen `getBestAlignment sc` is written out in `bestAlignment`.

Name in the proofs → name here:
  Window.chr, Window.len → Window.chromosome, Window.length
  windowSeq → windowSequence        Strand.fwd, Strand.rev → Strand.forward, Strand.reverse
  revComp → reverseComplement       hitsBoth → hitsBothStrands
  mapSpecBoth → mapReadBothStrands  pairSpecT → mapPairEachMate
  fwdRev → forwardReverse           fragLen → fragmentLength
  properPairU → properPairNoDovetail
  pairScoreD → pairScore            bestPairD → bestPair
  dcost0 → noDistanceCost           dcost1k → distanceCostPerKilobase
  pairSpecUT → mapPairBest          PairTieOk → PairTie

Build (after Alignment):

    lake env lean -o .lake/build/lib/lean/new_spec/statements/Mapping.olean new_spec/statements/Mapping.lean
-/

namespace NewSpec

/-- The frozen `getBestAlignment`: every alignment, scored with `scoring`, the best kept. -/
def bestAlignment (scoring : Scoring) (read reference : List Char) : Option (List Step × Int) :=
  ((allPaths read reference).map fun path => (path, scoreWalk scoring path read reference none)).maxOn?
    fun item => item.2

/-! ## Genome and windows (MapSpec) -/

structure Chromosome where
  name : String
  seq : List Char

abbrev Genome := List Chromosome

/-- Chromosome index, 0-based start, length. -/
structure Window where
  chromosome : Nat
  start : Nat
  length : Nat
deriving DecidableEq, Repr

/-- The letters of a window; `none` when it does not fit in its chromosome. -/
def windowSequence (genome : Genome) (window : Window) : Option (List Char) :=
  match genome[window.chromosome]? with
  | some chromosome =>
    if window.start + window.length ≤ chromosome.seq.length then
      some ((chromosome.seq.drop window.start).take window.length)
    else none
  | none => none

/-- Optimal global alignment score of the read against the window. -/
def windowScore (scoring : Scoring) (read : List Char) (genome : Genome) (window : Window) :
    Option Int :=
  match windowSequence genome window with
  | some reference =>
    match bestAlignment scoring read reference with
    | some best => some best.2
    | none => none
  | none => none

/-- Every window of every chromosome. -/
def allWindows (genome : Genome) : List Window :=
  (List.range genome.length).flatMap fun index =>
    let n := match genome[index]? with
      | some chromosome => chromosome.seq.length
      | none => 0
    (List.range (n + 1)).flatMap fun start =>
      (List.range (n - start + 1)).map fun length =>
        { chromosome := index, start := start, length := length }

/-- The windows among `windows` whose score is at least `threshold`, with their scores. -/
def hitsOf (score : Window → Option Int) (threshold : Int) (windows : List Window) :
    List (Window × Int) :=
  windows.filterMap fun window =>
    match score window with
    | some s => if threshold ≤ s then some (window, s) else none
    | none => none

/-! ## Both strands and proper pairs (PairSpec) -/

inductive Strand where
  | forward
  | reverse
deriving DecidableEq, Repr

/-- Complement of one letter; letters other than A, C, G, T are kept. -/
def complement : Char → Char
  | 'A' => 'T' | 'C' => 'G' | 'G' => 'C' | 'T' => 'A'
  | c => c

def reverseComplement (read : List Char) : List Char := (read.map complement).reverse

/-- A placement: a window and the strand the read is aligned on. -/
abbrev Placement := Window × Strand

/-- The hit that beats every hit at a different key, if there is one. -/
def selectUniqueBy {α : Type} [DecidableEq α] (hits : List (α × Int)) : Option (α × Int) :=
  hits.find? fun a => hits.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)

/-- Hits on both strands, each tagged with its strand. -/
def hitsBothStrands (scoring : Scoring) (threshold : Int) (genome : Genome) (read : List Char) :
    List (Placement × Int) :=
  (hitsOf (windowScore scoring read genome) threshold (allWindows genome)).map
    (fun hit => ((hit.1, Strand.forward), hit.2)) ++
  (hitsOf (windowScore scoring (reverseComplement read) genome) threshold (allWindows genome)).map
    (fun hit => ((hit.1, Strand.reverse), hit.2))

/-- Where the read maps over both strands, with its score; `none` = unmapped. -/
def mapReadBothStrands (scoring : Scoring) (threshold : Int) (genome : Genome) (read : List Char) :
    Option (Placement × Int) :=
  selectUniqueBy (hitsBothStrands scoring threshold genome read)

/-- Proper pair: same chromosome, opposite strands, facing, fragment length
(forward mate start to reverse mate end) in `[minFragment, maxFragment]`. -/
def properPair (minFragment maxFragment : Nat) (first second : Placement) : Bool :=
  let (forwardMate, reverseMate) := if first.2 = Strand.forward then (first, second) else (second, first)
  decide (forwardMate.1.chromosome = reverseMate.1.chromosome) &&
    decide (forwardMate.2 = Strand.forward) && decide (reverseMate.2 = Strand.reverse) &&
    decide (forwardMate.1.start ≤ reverseMate.1.start + reverseMate.1.length) &&
    decide (minFragment ≤ reverseMate.1.start + reverseMate.1.length - forwardMate.1.start) &&
    decide (reverseMate.1.start + reverseMate.1.length - forwardMate.1.start ≤ maxFragment)

/-! ## Each mate at its own threshold, then the proper-pair test (PairDispatch) -/

/-- Each mate maps on its own at its own threshold; then the proper-pair test. -/
def mapPairEachMate (threshold1 threshold2 : Int) (minFragment maxFragment : Nat) (genome : Genome)
    (mate1 mate2 : List Char) : Option ((Placement × Int) × (Placement × Int)) :=
  match mapReadBothStrands defaultScoring threshold1 genome mate1,
        mapReadBothStrands defaultScoring threshold2 genome mate2 with
  | some hit1, some hit2 =>
    if properPair minFragment maxFragment hit1.1 hit2.1 then some (hit1, hit2) else none
  | _, _ => none

/-! ## Pair-level uniqueness (PairSpecU) -/

/-- A pair of hits: (placement, score) of mate 1 and of mate 2. -/
abbrev PairHit := (Placement × Int) × (Placement × Int)

/-- The two placements ordered (forward-strand one, other one). -/
def forwardReverse (first second : Placement) : Placement × Placement :=
  if first.2 = Strand.forward then (first, second) else (second, first)

/-- Fragment length: forward mate start to reverse mate end. -/
def fragmentLength (first second : Placement) : Nat :=
  (forwardReverse first second).2.1.start + (forwardReverse first second).2.1.length -
    (forwardReverse first second).1.1.start

/-- Proper pair with no dovetailing beyond `dovetailSlack` letters. -/
def properPairNoDovetail (dovetailSlack minFragment maxFragment : Nat) (first second : Placement) :
    Bool :=
  properPair minFragment maxFragment first second &&
    decide ((forwardReverse first second).1.1.start ≤
      (forwardReverse first second).2.1.start + dovetailSlack) &&
    decide ((forwardReverse first second).1.1.start + (forwardReverse first second).1.1.length ≤
      (forwardReverse first second).2.1.start + (forwardReverse first second).2.1.length + dovetailSlack)

/-- Pair score: summed mate scores minus the distance cost of the fragment. -/
def pairScore (distanceCost : Nat → Nat) (pair : PairHit) : Int :=
  pair.1.2 + pair.2.2 - (distanceCost (fragmentLength pair.1.1 pair.2.1) : Int)

/-- All proper pairs `(hit1, hit2)`, `hit1` from `hits1`, `hit2` from `hits2`. -/
def properPairs (dovetailSlack minFragment maxFragment : Nat) (hits1 hits2 : List (Placement × Int)) :
    List PairHit :=
  hits1.flatMap fun hit1 =>
    (hits2.filter fun hit2 => properPairNoDovetail dovetailSlack minFragment maxFragment hit1.1 hit2.1).map
      fun hit2 => (hit1, hit2)

/-- The proper pair whose score beats every other proper pair at different
placements, if there is one. -/
def bestPair (distanceCost : Nat → Nat) (dovetailSlack minFragment maxFragment : Nat)
    (hits1 hits2 : List (Placement × Int)) : Option PairHit :=
  (properPairs dovetailSlack minFragment maxFragment hits1 hits2).find? fun pair =>
    (properPairs dovetailSlack minFragment maxFragment hits1 hits2).all fun other =>
      decide (pairScore distanceCost other < pairScore distanceCost pair) ||
        decide (other.1.1 = pair.1.1 ∧ other.2.1 = pair.2.1)

/-- Default distance cost: none; pairs are ranked by `penalty1 + penalty2` only. -/
def noDistanceCost : Nat → Nat := fun _ => 0

/-- Optional distance cost: 0 up to 1000 letters, then +1 per full extra 1000 letters. -/
def distanceCostPerKilobase (fragment : Nat) : Nat := (fragment - 1000) / 1000

/-- Where a pair maps under pair-level uniqueness, mate 1 at `threshold1`, mate 2 at
`threshold2`; `none` = not reported. -/
def mapPairBest (scoring : Scoring) (distanceCost : Nat → Nat) (dovetailSlack minFragment maxFragment : Nat)
    (threshold1 threshold2 : Int) (genome : Genome) (mate1 mate2 : List Char) : Option PairHit :=
  bestPair distanceCost dovetailSlack minFragment maxFragment
    (hitsBothStrands scoring threshold1 genome mate1) (hitsBothStrands scoring threshold2 genome mate2)

/-- A proved tie: proper pairs exist at these thresholds, but none is the unique best. -/
def PairTie (distanceCost : Nat → Nat) (dovetailSlack minFragment maxFragment : Nat)
    (threshold1 threshold2 : Int) (genome : Genome) (mate1 mate2 : List Char) : Prop :=
  mapPairBest defaultScoring distanceCost dovetailSlack minFragment maxFragment
      threshold1 threshold2 genome mate1 mate2 = none ∧
    ∃ pair, pair ∈ properPairs dovetailSlack minFragment maxFragment
      (hitsBothStrands defaultScoring threshold1 genome mate1)
      (hitsBothStrands defaultScoring threshold2 genome mate2)

/-! ## Floors and alignments of one mate (TierRouter) -/

/-- Every placement of the mate (any score) has penalty at least `floor`. -/
def MateFloor (genome : Genome) (mate : List Char) (floor : Nat) : Prop :=
  ∀ threshold, ∀ hit ∈ hitsBothStrands defaultScoring threshold genome mate, (floor : Int) ≤ -hit.2

/-- The read on a strand. -/
def strandRead (mate : List Char) : Strand → List Char
  | .forward => mate
  | .reverse => reverseComplement mate

/-- A reported CIGAR is a real alignment of the read (on the placement's strand) to the
placement's window, with the reported score. -/
def CigarOk (genome : Genome) (mate : List Char) (hit : Placement × Int) (cigar : List (Step × Nat)) :
    Prop :=
  ∃ reference, windowSequence genome hit.1.1 = some reference ∧
    IsMonotoneWalk (expandCigar cigar.toArray) (strandRead mate hit.1.2) reference ∧
    walkScore (strandRead mate hit.1.2) reference (expandCigar cigar.toArray) = hit.2

theorem mateFloor_zero (genome : Genome) (mate : List Char) : MateFloor genome mate 0 := by
  sorry

end NewSpec
