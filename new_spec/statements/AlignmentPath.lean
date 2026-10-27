/-!
# 1. Alignment, path design (draft for Rowan to go through)

Statements only: every proof is `sorry`. Imports nothing. Sits next to Alignment.lean
(the verbatim version) until one is chosen.

The path is the object. A CIGAR is the same alignment written as merged runs; both
conversions are inverses. Scores are maximized and are at most 0 (same signs as before).

Old name → name here:
  sc0 / defaultScoring → defaultScoring; xConsumed, yConsumed → Step.queryConsumed,
  Step.referenceConsumed; walkScore → Path.score; expandCigar → decodeRuns;
  unitCigar → encodeRuns (now merges equal neighbours); AlignmentSound → carried by
  `Path` and `Cigar`; AlignmentOptimal → Path.IsOptimal.

Build from the repository root:

    lake env lean new_spec/statements/AlignmentPath.lean
-/

namespace NewSpec

/-- Scoring values, with the requirements every scoring must meet. -/
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

/-- A length-k gap scores gapOpen + k * gapExtend, here -(6 + 2k). -/
def defaultScoring : Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2
    hMatch := by decide, hMismatch := by decide
    hGapOpen := by decide, hGapExtend := by decide }

abbrev Read := List Char

inductive Step where
  | diag  -- one letter from query and reference (match or mismatch)
  | gapX  -- one letter from the reference only
  | gapY  -- one letter from the query only
deriving Repr, BEq, DecidableEq

def Step.queryConsumed : Step → Nat
  | .diag => 1
  | .gapX => 0
  | .gapY => 1

def Step.referenceConsumed : Step → Nat
  | .diag => 1
  | .gapX => 1
  | .gapY => 0

/-- The steps consume exactly the query and exactly the reference. -/
def IsMonotoneWalk (steps : List Step) (query reference : Read) : Prop :=
  (steps.map Step.queryConsumed).sum = query.length ∧
  (steps.map Step.referenceConsumed).sum = reference.length

instance (steps : List Step) (query reference : Read) :
    Decidable (IsMonotoneWalk steps query reference) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Path: a complete alignment of these two sequences -/

structure Path (query reference : Read) where
  steps : List Step
  hWalk : IsMonotoneWalk steps query reference
deriving Repr, DecidableEq

/-- Same body as the proved `scoreWalk`. A gap pays gapOpen only when the previous
step was not the same kind of gap. The last case is never reached by a valid walk. -/
def scoreWalk (scoring : Scoring) : List Step → Read → Read → Option Step → Int
  | [], _, _, _ => 0
  | .diag :: rest, q :: query, r :: reference, _ =>
      (if q = r then scoring.matchScore else scoring.mismatchScore) +
        scoreWalk scoring rest query reference (some .diag)
  | .gapX :: rest, query, _ :: reference, previous =>
      (if previous = some .gapX then scoring.gapExtend
       else scoring.gapOpen + scoring.gapExtend) +
        scoreWalk scoring rest query reference (some .gapX)
  | .gapY :: rest, _ :: query, reference, previous =>
      (if previous = some .gapY then scoring.gapExtend
       else scoring.gapOpen + scoring.gapExtend) +
        scoreWalk scoring rest query reference (some .gapY)
  | _, _, _, _ => 0

def Path.score {query reference : Read} (path : Path query reference) (scoring : Scoring) : Int :=
  scoreWalk scoring path.steps query reference none

/-- No valid path scores higher under this scoring. -/
def Path.IsOptimal {query reference : Read} (path : Path query reference) (scoring : Scoring) :
    Prop :=
  ∀ other : Path query reference, other.score scoring ≤ path.score scoring

/-! ## CIGAR: the same path as merged runs -/

/-- Merge consecutive equal steps into one run. -/
def encodeSteps : List Step → List (Step × Nat)
  | [] => []
  | step :: rest =>
      match encodeSteps rest with
      | [] => [(step, 1)]
      | (next, count) :: runs =>
          if step = next then (step, count + 1) :: runs
          else (step, 1) :: (next, count) :: runs

def encodeRuns (steps : List Step) : Array (Step × Nat) := (encodeSteps steps).toArray

def decodeRuns (runs : Array (Step × Nat)) : List Step :=
  runs.toList.flatMap fun (step, count) => List.replicate count step

theorem decode_encode (steps : List Step) : decodeRuns (encodeRuns steps) = steps := by
  sorry

/-- A CIGAR is the encoding of some valid path, so its runs are merged and positive. -/
structure Cigar (query reference : Read) where
  runs : Array (Step × Nat)
  hFromPath : ∃ path : Path query reference, encodeRuns path.steps = runs
deriving Repr, DecidableEq

def Path.cigar {query reference : Read} (path : Path query reference) : Cigar query reference :=
  { runs := encodeRuns path.steps, hFromPath := ⟨path, rfl⟩ }

def Cigar.path {query reference : Read} (cigar : Cigar query reference) : Path query reference :=
  { steps := decodeRuns cigar.runs
    hWalk := by
      obtain ⟨original, hEncoding⟩ := cigar.hFromPath
      rw [← hEncoding, decode_encode]
      exact original.hWalk }

theorem Path.cigar_path {query reference : Read} (path : Path query reference) :
    path.cigar.path = path := by
  sorry

theorem Cigar.path_cigar {query reference : Read} (cigar : Cigar query reference) :
    cigar.path.cigar = cigar := by
  sorry

/-! ## The naive aligner -/

/-- Every monotone step list, branching three ways until both sequences are used. -/
def allPaths : Read → Read → List (List Step)
  | [], [] => [[]]
  | [], _ :: reference => (allPaths [] reference).map (Step.gapX :: ·)
  | _ :: query, [] => (allPaths query []).map (Step.gapY :: ·)
  | q :: query, r :: reference =>
      ((allPaths query reference).map (Step.diag :: ·)) ++
      ((allPaths (q :: query) reference).map (Step.gapX :: ·)) ++
      ((allPaths query (r :: reference)).map (Step.gapY :: ·))

theorem monotone_iff_enumerated (query reference : Read) (steps : List Step) :
    IsMonotoneWalk steps query reference ↔ steps ∈ allPaths query reference := by
  sorry

/-- The enumerated step lists, each with its validity proof. -/
def enumeratedPaths (query reference : Read) : List (Path query reference) :=
  (allPaths query reference).attach.map fun candidate =>
    { steps := candidate.val
      hWalk := (monotone_iff_enumerated query reference candidate.val).mpr candidate.property }

/-- There is always at least one path (two empty sequences: the empty path). -/
theorem enumeratedPaths_ne_nil (query reference : Read) : enumeratedPaths query reference ≠ [] := by
  sorry

/-- THE NAIVE ALIGNER: score every path, keep a best one. Its tie-break does not
constrain a fast kernel's choice among equally good paths. -/
def alignSpec (scoring : Scoring) (query reference : Read) : Path query reference :=
  (enumeratedPaths query reference).maxOn (fun path => path.score scoring)
    (enumeratedPaths_ne_nil query reference)

theorem alignSpec_optimal (scoring : Scoring) (query reference : Read) :
    (alignSpec scoring query reference).IsOptimal scoring := by
  sorry

/-! ## Slot for a fast kernel

A kernel returns plain data (runs, scores); its internals are unconstrained. Each answer
says how much it guarantees. -/

/-- No valid path scores more than `slack` above this path. `slack = 0` is optimal. -/
def Path.IsWithin {query reference : Read} (path : Path query reference) (scoring : Scoring)
    (slack : Nat) : Prop :=
  ∀ other : Path query reference, other.score scoring ≤ path.score scoring + slack

inductive AlignmentResult where
  /-- The runs are an optimal alignment with this score. -/
  | optimal (runs : Array (Step × Nat)) (score : Int)
  /-- The runs are an alignment with this score; the best score is at most `slack` higher. -/
  | bounded (runs : Array (Step × Nat)) (score : Int) (slack : Nat)
  /-- No alignment; every path scores below `threshold`. -/
  | unaligned (threshold : Int)
deriving Repr, DecidableEq

/-- What each answer proves about these two sequences. -/
def AlignmentResult.Correct (scoring : Scoring) (query reference : Read) : AlignmentResult → Prop
  | .optimal runs score =>
    ∃ path : Path query reference,
      path.cigar.runs = runs ∧ path.score scoring = score ∧ path.IsOptimal scoring
  | .bounded runs score slack =>
    ∃ path : Path query reference,
      path.cigar.runs = runs ∧ path.score scoring = score ∧ path.IsWithin scoring slack
  | .unaligned threshold =>
    ∀ path : Path query reference, path.score scoring < threshold

abbrev AlignmentKernel := Read → Read → AlignmentResult

/-- Every answer the kernel gives proves its claim. -/
def AlignmentKernelCorrect (scoring : Scoring) (kernel : AlignmentKernel) : Prop :=
  ∀ query reference, (kernel query reference).Correct scoring query reference

/-! ## Examples -/

#guard encodeRuns [.diag, .diag, .gapX, .gapX, .diag] == #[(.diag, 2), (.gapX, 2), (.diag, 1)]

def gapPath : Path [] ['A', 'C'] := { steps := [.gapX, .gapX], hWalk := by decide }

#guard gapPath.score defaultScoring == -10
#guard gapPath.cigar.runs == #[(.gapX, 2)]

end NewSpec
