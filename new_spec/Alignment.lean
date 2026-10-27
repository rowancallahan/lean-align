import WfaU3

/-!
# 1. Alignment: a real walk, its exact score, and optimality

Read/edit in order: Alignment.lean, Mapping.lean, Pairing.lean.
These are review specs; the existing implementation and specs are untouched.
The examples use tiny inputs because the naive reference enumerates EVERY path.

Run from the repository root (repeat these commands after editing dependencies):

    mkdir -p .lake/build/lib/lean/new_spec
    lake env lean -o .lake/build/lib/lean/new_spec/Alignment.olean new_spec/Alignment.lean
    lake env lean -o .lake/build/lib/lean/new_spec/Mapping.olean new_spec/Mapping.lean
    lake env lean -o .lake/build/lib/lean/new_spec/Pairing.olean new_spec/Pairing.lean

No IO/CLI or output-file behavior is specified here. All functions below are pure.
We reuse the frozen scoring recursion and path enumerator so the existing kernel
proofs apply directly. Use Go to Definition on `scoreWalk` or `allPaths` to read
their bodies in spec/AlignmentSpec.lean; these are NOT unproved kernel slots.
-/

namespace NewSpec

abbrev Step := AlignmentSpec.Step
abbrev Scoring := AlignmentSpec.Scoring
abbrev Read := List Char
abbrev Cigar := Array (Step × Nat)

/-- Scores are maximized. Penalties are their negatives, and are minimized.
A length-k gap costs 6 + 2*k, including the extension on its first column.
A penalty cap is NOT a count of mismatches/indels. -/
def sc0 : Scoring :=
  { matchScore := 0, mismatchScore := -4, gapOpen := -6, gapExtend := -2 }

/-- x is the read; y is the reference window. `gapX` consumes only y,
`gapY` only x. These are structured steps, not SAM I/D text conventions. -/
def IsMonotoneWalk (path : List Step) (x y : Read) : Prop :=
  (path.map AlignmentSpec.xConsumed).sum = x.length ∧
  (path.map AlignmentSpec.yConsumed).sum = y.length

instance (path : List Step) (x y : Read) : Decidable (IsMonotoneWalk path x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Start the affine scorer with no previous step. On a diagonal, score the
two letters; on a gap, pay extension plus opening if the gap type changed.
Only scores of valid walks carry semantic meaning. -/
def walkScore (x y : Read) (path : List Step) : Int :=
  AlignmentSpec.scoreWalk sc0 path x y none

def expandCigar (runs : Cigar) : List Step :=
  runs.toList.flatMap fun (step, count) => List.replicate count step

/-- THE NAIVE ALIGNER: enumerate all paths, score them, select a maximum.
Its internal path tie-break does not constrain a fast kernel's CIGAR. -/
def alignSpec (x y : Read) : Option (List Step × Int) :=
  ((AlignmentSpec.allPaths x y).map fun p => (p, walkScore x y p)).maxOn? Prod.snd

def AlignmentSound (x y : Read) (runs : Cigar) (score : Int) : Prop :=
  IsMonotoneWalk (expandCigar runs) x y ∧
  walkScore x y (expandCigar runs) = score

def AlignmentOptimal (x y : Read) (score : Int) : Prop :=
  ∀ path, IsMonotoneWalk path x y → walkScore x y path ≤ score

/-- Slot for a replacement alignment kernel: totality, soundness AND optimality. -/
def AlignmentKernelCorrect (kernel : Read → Read → Option (Cigar × Int)) : Prop :=
  ∀ x y, (∃ result, kernel x y = some result) ∧
    ∀ runs score, kernel x y = some (runs, score) →
      AlignmentSound x y runs score ∧ AlignmentOptimal x y score

theorem monotone_iff_enumerated (x y : Read) (path : List Step) :
    IsMonotoneWalk path x y ↔ path ∈ AlignmentSpec.allPaths x y :=
  (AlignmentSpec.mem_allPaths_iff_isMonotoneWalk path x y).symm

theorem alignSpec_sound_optimal (x y : Read) (path : List Step) (score : Int)
    (h : alignSpec x y = some (path, score)) :
    IsMonotoneWalk path x y ∧ walkScore x y path = score ∧ AlignmentOptimal x y score := by
  obtain ⟨hv, hs⟩ := AlignmentSpec.getBestAlignment_returns_a_valid_walk sc0 x y path score h
  exact ⟨hv, hs, fun p hp =>
    AlignmentSpec.getBestAlignment_returns_a_maximum_score sc0 x y path score p h hp⟩

def alignFast (x y : Read) : Option (Cigar × Int) :=
  AlignmentSpec.wfaAlignU3 sc0 x.toArray y.toArray

/-- Actual existing U3 implementation, not an assumed correctness field. -/
theorem alignFast_correct : AlignmentKernelCorrect alignFast := by
  intro x y
  constructor
  · exact Option.isSome_iff_exists.mp (AlignmentSpec.wfaAlignU3_isSome sc0 x.toArray y.toArray)
  · intro runs score h
    have hs := AlignmentSpec.wfaAlignU3_sound sc0 x.toArray y.toArray runs score h
    have he := AlignmentSpec.wfaAlignU3_score sc0 x.toArray y.toArray
    obtain ⟨⟨path, best⟩, hb⟩ := AlignmentSpec.getBestAlignment_returns_some sc0 x y
    change (match AlignmentSpec.wfaAlignU3 sc0 x.toArray y.toArray with
      | some r => some r.2 | none => none) =
      (match AlignmentSpec.getBestAlignment sc0 x y with
      | some r => some r.2 | none => none) at he
    change AlignmentSpec.wfaAlignU3 sc0 x.toArray y.toArray = some (runs, score) at h
    rw [h, hb] at he
    have hscore : score = best := Option.some.inj he
    refine ⟨hs, ?_⟩
    intro p hp
    rw [hscore]
    exact AlignmentSpec.getBestAlignment_returns_a_maximum_score sc0 x y path best p hb hp

-- Edit these examples first. `#guard` is executable; `example` is a proof.
#guard walkScore ['A'] ['C'] [.diag] == -4
#guard walkScore [] ['A', 'C'] [.gapX, .gapX] == -10
#guard alignSpec ['A', 'C'] ['A', 'C'] == some ([.diag, .diag], 0)
#guard alignSpec ['A'] ['C'] == some ([.diag], -4)
example : IsMonotoneWalk [.diag, .gapX] ['A'] ['A', 'C'] := by decide
example : ¬ IsMonotoneWalk [.diag] ['A'] ['A', 'C'] := by decide

-- A returned CIGAR has the reported score AND no valid walk scores higher.
example (runs : Cigar) (score : Int) (h : alignFast ['A'] ['C'] = some (runs, score)) :
    AlignmentSound ['A'] ['C'] runs score ∧ AlignmentOptimal ['A'] ['C'] score :=
  (alignFast_correct _ _).2 runs score h

end NewSpec
