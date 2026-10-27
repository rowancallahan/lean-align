/-! # 1. Alignment. Statements only; imports nothing. -/

namespace Spec

structure Scoring where
  matchScore    : Int
  mismatchScore : Int
  gapOpen       : Int
  gapExtend     : Int
  hMatch     : matchScore ≤ 0
  hMismatch  : mismatchScore < 0
  hGapOpen   : gapOpen ≤ 0
  hGapExtend : gapExtend < 0
deriving Repr, DecidableEq

-- a length-k gap scores -(6 + 2k)
def defaultScoring : Scoring := ⟨0, -4, -6, -2, by decide, by decide, by decide, by decide⟩

abbrev Read := List Char

inductive Step where
  | diag  -- one letter from query and reference
  | gapX  -- one letter from the reference only
  | gapY  -- one letter from the query only
deriving Repr, DecidableEq

-- a complete alignment: the steps use up exactly the query and exactly the reference
structure Path (query reference : Read) where
  steps : List Step
  usesQuery     : steps.count .diag + steps.count .gapY = query.length
  usesReference : steps.count .diag + steps.count .gapX = reference.length

-- a gap pays gapOpen only when the previous step was not the same kind of gap
def scoreWalk (scoring : Scoring) : List Step → Read → Read → Option Step → Int
  | [], _, _, _ => 0
  | .diag :: rest, q :: query, r :: reference, _ =>
      (if q = r then scoring.matchScore else scoring.mismatchScore) +
        scoreWalk scoring rest query reference (some .diag)
  | .gapX :: rest, query, _ :: reference, previous =>
      (if previous = some .gapX then scoring.gapExtend else scoring.gapOpen + scoring.gapExtend) +
        scoreWalk scoring rest query reference (some .gapX)
  | .gapY :: rest, _ :: query, reference, previous =>
      (if previous = some .gapY then scoring.gapExtend else scoring.gapOpen + scoring.gapExtend) +
        scoreWalk scoring rest query reference (some .gapY)
  | _, _, _, _ => 0  -- unreachable for a valid path

def Path.score {query reference : Read} (path : Path query reference) (scoring : Scoring) : Int :=
  scoreWalk scoring path.steps query reference none

/-! ## CIGAR: the path's steps as merged runs -/

def encodeCigar : List Step → List (Step × Nat)
  | [] => []
  | step :: rest =>
      match encodeCigar rest with
      | [] => [(step, 1)]
      | (next, count) :: cigar =>
          if step = next then (step, count + 1) :: cigar
          else (step, 1) :: (next, count) :: cigar

-- the path written as merged runs
def Path.cigar {query reference : Read} (path : Path query reference) : Array (Step × Nat) :=
  (encodeCigar path.steps).toArray

def decodeCigar (cigar : Array (Step × Nat)) : List Step :=
  cigar.toList.flatMap fun (step, count) => List.replicate count step

-- encodeCigar loses nothing: decoding the CIGAR gives back the path's steps
theorem cigar_decodes {query reference : Read} (path : Path query reference) :
    decodeCigar path.cigar = path.steps := by
  sorry

/-! ## The naive aligner -/

-- one more step in front of a valid path gives a valid path
def Path.addDiag {query reference : Read} (q r : Char) (path : Path query reference) :
    Path (q :: query) (r :: reference) :=
  ⟨.diag :: path.steps, by simp [← path.usesQuery]; omega, by simp [← path.usesReference]; omega⟩

def Path.addGapX {query reference : Read} (r : Char) (path : Path query reference) :
    Path query (r :: reference) :=
  ⟨.gapX :: path.steps, by simp [← path.usesQuery], by simp [← path.usesReference]; omega⟩

def Path.addGapY {query reference : Read} (q : Char) (path : Path query reference) :
    Path (q :: query) reference :=
  ⟨.gapY :: path.steps, by simp [← path.usesQuery]; omega, by simp [← path.usesReference]⟩

-- every path, built from the empty path one step at a time, so each one is valid
def allPaths : (query reference : Read) → List (Path query reference)
  | [], [] => [⟨[], rfl, rfl⟩]
  | [], r :: reference => (allPaths [] reference).map (Path.addGapX r)
  | q :: query, [] => (allPaths query []).map (Path.addGapY q)
  | q :: query, r :: reference =>
      (allPaths query reference).map (Path.addDiag q r) ++
      (allPaths (q :: query) reference).map (Path.addGapX r) ++
      (allPaths query (r :: reference)).map (Path.addGapY q)

theorem allPaths_ne_nil (query reference : Read) : allPaths query reference ≠ [] := by
  sorry

-- allPaths misses nothing: every path of these two reads is in the list
theorem allPaths_complete {query reference : Read} (path : Path query reference) :
    path ∈ allPaths query reference := by
  sorry

-- THE NAIVE ALIGNER. Its tie-break does not constrain a fast kernel.
def alignSpec (scoring : Scoring) (query reference : Read) : Path query reference :=
  (allPaths query reference).maxOn (fun path => path.score scoring) (allPaths_ne_nil query reference)

theorem alignSpec_optimal (scoring : Scoring) (query reference : Read) :
    ∀ other : Path query reference,
      other.score scoring ≤ (alignSpec scoring query reference).score scoring := by
  sorry

/-! ## Kernel slot: plain data out, each answer proves its claim -/

inductive AlignmentResult where
  | optimal (cigar : Array (Step × Nat)) (score : Int)
  | bounded (cigar : Array (Step × Nat)) (score : Int) (slack : Nat)
  | unaligned (threshold : Int)
deriving Repr, DecidableEq

def AlignmentResult.Correct (scoring : Scoring) (query reference : Read) : AlignmentResult → Prop
  -- an optimal result is the best scoring path anywhere
  | .optimal returnedCigar returnedScore =>
      ∃ path : Path query reference,
        path.cigar = returnedCigar ∧
        path.score scoring = returnedScore ∧
        ∀ other : Path query reference, other.score scoring ≤ returnedScore

  -- A bounded result is is no better than its score plus slack and no worse than its score
  | .bounded returnedCigar returnedScore slack =>
      ∃ path : Path query reference,
        path.cigar = returnedCigar ∧
        path.score scoring = returnedScore ∧
        ∀ other : Path query reference, other.score scoring ≤ (returnedScore + slack)

  -- an unalighed result is no better than threshold (important so not everything goes here)
  | .unaligned threshold =>
      ∀ path : Path query reference,
        path.score scoring < threshold

abbrev AlignmentKernel := Read → Read → AlignmentResult

def AlignmentKernelCorrect (scoring : Scoring) (kernel : AlignmentKernel) : Prop :=
  ∀ query reference, (kernel query reference).Correct scoring query reference

-- a perfect kernel: correct, and every answer is the optimal case
def AlignmentKernelExact (scoring : Scoring) (kernel : AlignmentKernel) : Prop :=
  AlignmentKernelCorrect scoring kernel ∧
    ∀ query reference,
      ∃ cigar score,
        kernel query reference = .optimal cigar score

/-! ## Examples (`#guard` runs the definitions; each line must evaluate to true) -/

def gapPath : Path [] ['A', 'C'] := ⟨[.gapX, .gapX], by decide, by decide⟩
#guard gapPath.score defaultScoring == -10
#guard gapPath.cigar == #[(.gapX, 2)]

-- encodeCigar merges neighbouring equal steps; equal steps that are not neighbours stay apart
#guard encodeCigar [] == []
#guard encodeCigar [.diag, .diag, .diag] == [(.diag, 3)]
#guard encodeCigar [.gapX, .gapX, .gapY, .gapY, .gapY] == [(.gapX, 2), (.gapY, 3)]
#guard encodeCigar [.diag, .gapX, .diag] == [(.diag, 1), (.gapX, 1), (.diag, 1)]
#guard decodeCigar (encodeCigar [.diag, .diag, .gapX, .gapY]).toArray == [.diag, .diag, .gapX, .gapY]

-- allPaths lists every valid path once: 1, 3, 5, 13, ... paths
#guard (allPaths [] []).map (·.steps) == [[]]
#guard (allPaths [] ['A', 'C']).map (·.steps) == [[.gapX, .gapX]]
#guard (allPaths ['A'] ['C']).map (·.steps) == [[.diag], [.gapX, .gapY], [.gapY, .gapX]]
#guard (allPaths ['A', 'C'] ['G']).length == 5
#guard (allPaths ['A', 'C'] ['G', 'T']).length == 13
#guard ((allPaths ['A', 'C'] ['G', 'T']).map (·.steps)).eraseDups.length == 13

-- alignSpec picks a best path: a mismatch (-4) beats a gap on each side (-8 each)
#guard (alignSpec defaultScoring ['A', 'C'] ['A', 'C']).steps == [.diag, .diag]
#guard (alignSpec defaultScoring ['A'] ['C']).score defaultScoring == -4
#guard (alignSpec defaultScoring ['A', 'C'] ['A', 'G', 'C']).score defaultScoring == -8

end Spec
