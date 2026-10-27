import new_spec.Alignment
import SeedMapper

/-!
# 2. Genome-wide mapping, candidate/index contracts, and penalty bounds

Both-strand definitions follow PairSpec.lean on claude/upbeat-goldberg-kizkfd,
inspected at f23e892775855f38f2edbb0233ed37fe99550a5c (2026-10-07).
The local checkout is older, so these definitions are in a separate namespace.
The concrete fast examples below use locally available proved kernels.
The latest packed tier router's adapter is described separately in Pairing.lean.

Coordinates are zero-based, on the original genome, for BOTH strands.
We keep the existing genome/window types to reuse their proofs:
  Chromosome = { name : String, seq : List Char }
  Genome = List Chromosome
  Window = { chr : Nat, start : Nat, len : Nat }
`allWindows` includes length-zero windows. The thresholds decide which qualify.
-/

namespace NewSpec

abbrev Genome := MapSpec.Genome
abbrev Window := MapSpec.Window

inductive Strand where | fwd | rev
deriving DecidableEq, Repr

abbrev Placement := Window × Strand
abbrev Hit := Placement × Int

def complement : Char → Char
  | 'A' => 'T' | 'C' => 'G' | 'G' => 'C' | 'T' => 'A'
  | c => c

def revComp (read : Read) : Read := (read.map complement).reverse
def strandRead (read : Read) : Strand → Read
  | .fwd => read
  | .rev => revComp read

/-- Reject invalid chromosome numbers and windows extending beyond the end. -/
def windowSeq (genome : Genome) (window : Window) : Option Read :=
  match genome[window.chr]? with
  | none => none
  | some chromosome =>
    if window.start + window.len ≤ chromosome.seq.length then
      some ((chromosome.seq.drop window.start).take window.len)
    else none

/-- Enumerate every start 0..n and every length 0..n-start, per chromosome. -/
def allWindows (genome : Genome) : List Window := MapSpec.allWindows genome

def windowScore (genome : Genome) (read : Read) (window : Window) : Option Int :=
  (windowSeq genome window).bind fun reference => (alignSpec read reference).map Prod.snd

/-- Keep exactly those windows meeting the inclusive score threshold. -/
def hitsBoth (threshold : Int) (genome : Genome) (read : Read) : List Hit :=
  (MapSpec.hitsOf (windowScore genome read) threshold (allWindows genome)).map
    (fun h => ((h.1, Strand.fwd), h.2)) ++
  (MapSpec.hitsOf (windowScore genome (revComp read)) threshold (allWindows genome)).map
    (fun h => ((h.1, Strand.rev), h.2))

/-- Unique BEST placement, not "only one placement below the penalty cap".
Equal scores at distinct keys are ambiguous. Duplicate copies of a key are OK
when their scores agree, as they do for the exhaustive specification. -/
def selectUniqueBy {α : Type} [DecidableEq α] (hits : List (α × Int)) : Option (α × Int) :=
  hits.find? fun a => hits.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)

/-- THE NAIVE MAPPER: every chromosome, every window, both strands. -/
def mapReadSpec (maxPenalty : Nat) (genome : Genome) (read : Read) : Option Hit :=
  selectUniqueBy (hitsBoth (-(maxPenalty : Int)) genome read)

/-- Runnable baseline: exhaustive windows, using the proved fast scorer.
This is not the latest seeded/packed tier router. It is a small concrete example
of the scorer-replacement proof you can edit without pulling another branch. -/
def hitsBothFast (threshold : Int) (genome : Genome) (read : Read) : List Hit :=
  (MapSpec.hitsOf (MapSpec.kernelScore sc0 read genome) threshold (allWindows genome)).map
    (fun h => ((h.1, Strand.fwd), h.2)) ++
  (MapSpec.hitsOf (MapSpec.kernelScore sc0 (revComp read) genome) threshold (allWindows genome)).map
    (fun h => ((h.1, Strand.rev), h.2))

def mapReadFast (maxPenalty : Nat) (genome : Genome) (read : Read) : Option Hit :=
  selectUniqueBy (hitsBothFast (-(maxPenalty : Int)) genome read)

theorem windowScore_eq_old (genome : Genome) (read : Read) (window : Window) :
    windowScore genome read window = MapSpec.windowScore sc0 read genome window := by
  have hw : windowSeq genome window = MapSpec.windowSeq genome window := by
    unfold windowSeq MapSpec.windowSeq
    cases genome[window.chr]? <;> rfl
  unfold windowScore MapSpec.windowScore
  rw [hw]
  cases MapSpec.windowSeq genome window with
  | none => rfl
  | some reference =>
    change (AlignmentSpec.getBestAlignment sc0 read reference).map Prod.snd = _
    cases h : AlignmentSpec.getBestAlignment sc0 read reference <;> simp [h]

theorem mapReadFast_eq_spec (maxPenalty : Nat) (genome : Genome) (read : Read) :
    mapReadFast maxPenalty genome read = mapReadSpec maxPenalty genome read := by
  have h (r : Read) : MapSpec.kernelScore sc0 r genome = windowScore genome r := by
    funext w
    exact (MapSpec.kernelScore_eq sc0 r genome w).trans (windowScore_eq_old genome r w).symm
  simp only [mapReadFast, mapReadSpec, hitsBothFast, hitsBoth, h]

/-! Candidate and index slots. A candidate generator must cover ALL qualifying
placements, including ties; finding one good candidate does not establish uniqueness. -/

def CandidatesComplete (maxPenalty : Nat) (genome : Genome) (read : Read)
    (candidates : List Placement) : Prop :=
  ∀ hit ∈ hitsBoth (-(maxPenalty : Int)) genome read, hit.1 ∈ candidates

def CandidateScoreCorrect (genome : Genome) (read : Read)
    (score : Placement → Option Int) : Prop :=
  ∀ p, score p = windowScore genome (strandRead read p.2) p.1

/-- Semantic contract for the concrete SeedMapper.Index in THIS checkout.
It is deliberately not claimed to be the contract for the newer Mz packed index. -/
def IndexMapFastCorrect (genome : Genome) (index : MapSpec.Index) : Prop :=
  index.genome = genome ∧ MapSpec.LookupComplete genome index.l0 index.lookup

theorem createIndex_correct (seedLength : Nat) (genome : Genome) :
    IndexMapFastCorrect genome (MapSpec.buildIndex seedLength genome) :=
  ⟨rfl, MapSpec.buildIndex_complete seedLength genome⟩

/-- The builder theorem is a real lookup-completeness proof, not just reflexivity
of `index = createIndex genome`. This adapter is forward-strand only. -/
theorem indexed_forward_eq_spec (maxPenalty : Nat) (genome : Genome)
    (index : MapSpec.Index) (read : Read) (hIndex : IndexMapFastCorrect genome index) :
    MapSpec.mapWithIndex sc0 (-(maxPenalty : Int)) index read =
      MapSpec.mapSpec sc0 (-(maxPenalty : Int)) genome read := by
  unfold MapSpec.mapWithIndex
  rw [hIndex.1]
  exact MapSpec.mapWith_eq_mapSpec _ _ _ sc0 (by unfold MapSpec.ValidScoring sc0; decide) _ _ _ hIndex.2
    (MapSpec.kernelScore_eq sc0 read genome)

/-! Bounds follow the latest TierRouter.MateFloor / CeilEv semantics.
A ceiling witnesses SOME placement, not its optimality or uniqueness.
Reported CIGAR scores can be worse than the optimal score of their window. -/

def MateFloor (genome : Genome) (read : Read) (lowerPenalty : Nat) : Prop :=
  ∀ threshold, ∀ hit ∈ hitsBoth threshold genome read, (lowerPenalty : Int) ≤ -hit.2

def MateCeiling (genome : Genome) (read : Read) (upperPenalty : Nat) : Prop :=
  hitsBoth (-(upperPenalty : Int)) genome read ≠ []

def CigarOk (genome : Genome) (read : Read) (hit : Hit) (runs : Cigar) : Prop :=
  ∃ reference, windowSeq genome hit.1.1 = some reference ∧
    AlignmentSound (strandRead read hit.1.2) reference runs hit.2

structure MateBounds where
  lowerPenalty : Nat
  upperPenalty : Nat
  reported : Option (Hit × Option Cigar) := none

def MateBoundsCorrect (genome : Genome) (read : Read) (bounds : MateBounds) : Prop :=
  MateFloor genome read bounds.lowerPenalty ∧
  MateCeiling genome read bounds.upperPenalty ∧
  ∀ hit cigar, bounds.reported = some (hit, cigar) →
    hit.2 = -(bounds.upperPenalty : Int) ∧
    (∃ score, hit.2 ≤ score ∧ (hit.1, score) ∈ hitsBoth hit.2 genome read) ∧
    ∀ runs, cigar = some runs → CigarOk genome read hit runs

/-- An attained global minimum penalty. No uniqueness assumption is needed. -/
def BestPenalty (genome : Genome) (read : Read) (penalty : Int) : Prop :=
  (∃ threshold, ∃ hit ∈ hitsBoth threshold genome read, -hit.2 = penalty) ∧
  ∀ threshold, ∀ hit ∈ hitsBoth threshold genome read, penalty ≤ -hit.2

theorem hit_meets_threshold {threshold : Int} {genome : Genome} {read : Read} {hit : Hit}
    (h : hit ∈ hitsBoth threshold genome read) : threshold ≤ hit.2 := by
  rcases List.mem_append.mp h with h | h <;>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h <;>
    exact ((MapSpec.mem_hitsOf _ _ _ _ _).mp hx).2.2

theorem hit_has_window_score {threshold : Int} {genome : Genome} {read : Read} {hit : Hit}
    (h : hit ∈ hitsBoth threshold genome read) :
    windowScore genome (strandRead read hit.1.2) hit.1.1 = some hit.2 := by
  rcases List.mem_append.mp h with h | h <;>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h <;>
    exact ((MapSpec.mem_hitsOf _ _ _ _ _).mp hx).2.1

theorem hit_rethreshold {oldThreshold newThreshold : Int} {genome : Genome} {read : Read} {hit : Hit}
    (h : hit ∈ hitsBoth oldThreshold genome read) (hScore : newThreshold ≤ hit.2) :
    hit ∈ hitsBoth newThreshold genome read := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    obtain ⟨hw, hs, _⟩ := (MapSpec.mem_hitsOf _ _ _ _ _).mp hx
    exact List.mem_append_left _ (List.mem_map.mpr ⟨x,
      (MapSpec.mem_hitsOf _ _ _ _ _).mpr ⟨hw, hs, hScore⟩, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    obtain ⟨hw, hs, _⟩ := (MapSpec.mem_hitsOf _ _ _ _ _).mp hx
    exact List.mem_append_right _ (List.mem_map.mpr ⟨x,
      (MapSpec.mem_hitsOf _ _ _ _ _).mpr ⟨hw, hs, hScore⟩, rfl⟩)

/-- A selected exact read is globally optimal: comparison includes every
threshold, hence every scored placement, not just a candidate shortlist.
Every DIFFERENT qualifying placement has a strictly worse score. -/
theorem mapReadSpec_best (maxPenalty : Nat) (genome : Genome) (read : Read) (best : Hit)
    (h : mapReadSpec maxPenalty genome read = some best) :
    best ∈ hitsBoth (-(maxPenalty : Int)) genome read ∧
    (∀ threshold, ∀ other ∈ hitsBoth threshold genome read, other.2 ≤ best.2) ∧
    (∀ other ∈ hitsBoth (-(maxPenalty : Int)) genome read, other.1 ≠ best.1 → other.2 < best.2) := by
  unfold mapReadSpec selectUniqueBy at h
  have hm := List.mem_of_find?_eq_some h
  have hall0 := List.find?_some h
  have hall := List.all_eq_true.mp hall0
  have hstrict : ∀ other ∈ hitsBoth (-(maxPenalty : Int)) genome read,
      other.1 ≠ best.1 → other.2 < best.2 := by
    intro other ho hne
    have hc := hall other ho
    simpa [hne] using hc
  refine ⟨hm, ?_, hstrict⟩
  intro threshold other ho
  by_cases hcap : -(maxPenalty : Int) ≤ other.2
  · have hc := hit_rethreshold ho hcap
    by_cases hkey : other.1 = best.1
    · have hs := hit_has_window_score hc
      rw [hkey] at hs
      have heq := hs.symm.trans (hit_has_window_score hm)
      exact Int.le_of_eq (Option.some.inj heq)
    · exact Int.le_of_lt (hstrict other hc hkey)
  · have hb := hit_meets_threshold hm
    omega

/-- Useful weakest floor: under sc0 every alignment penalty is nonnegative. -/
theorem mateFloor_zero (genome : Genome) (read : Read) : MateFloor genome read 0 := by
  intro threshold hit hmem
  have hs := hit_has_window_score hmem
  unfold windowScore at hs
  cases hw : windowSeq genome hit.1.1 with
  | none => simp [hw] at hs
  | some reference =>
    cases ha : alignSpec (strandRead read hit.1.2) reference with
    | none => simp [hw, ha] at hs
    | some result =>
      have heq : result.2 = hit.2 := by simpa [hw, ha] using hs
      have hscore := (alignSpec_sound_optimal _ _ result.1 result.2 ha).2.1
      have hn := MapSpec.scoreWalk_add_errs_le sc0
        (by unfold MapSpec.ValidScoring sc0; decide) 0 (by decide) (by decide) (by decide)
        result.1 (strandRead read hit.1.2) reference none 0
      change walkScore _ _ result.1 + 0 * _ ≤ 0 at hn
      rw [hscore, heq] at hn
      omega

/-- The promised interval for a bounded result: lower ≤ optimum ≤ upper. -/
theorem bounded_result_interval {genome : Genome} {read : Read} {bounds : MateBounds}
    {optimum : Int} (h : MateBoundsCorrect genome read bounds)
    (hBest : BestPenalty genome read optimum) :
    (bounds.lowerPenalty : Int) ≤ optimum ∧ optimum ≤ (bounds.upperPenalty : Int) := by
  obtain ⟨threshold, hit, hmem, heq⟩ := hBest.1
  constructor
  · simpa [heq] using h.1 threshold hit hmem
  · obtain ⟨candidate, hc⟩ := List.exists_mem_of_ne_nil _ h.2.1
    have hp := hBest.2 _ candidate hc
    have ht := hit_meets_threshold hc
    omega

-- Tiny examples: both strands, ties, distinct placement keys, inclusive caps.
def toyGenome : Genome := [⟨"toy", ['A', 'C']⟩]
#guard mapReadSpec 0 toyGenome ['A', 'C'] = some ((⟨0, 0, 2⟩, .fwd), 0)
#guard mapReadSpec 0 toyGenome ['G', 'T'] = some ((⟨0, 0, 2⟩, .rev), 0)
#guard mapReadSpec 0 [⟨"repeat", ['A', 'A']⟩] ['A'] = none
#guard mapReadSpec 0 [⟨"palindrome", ['A', 'T']⟩] ['A', 'T'] = none
#guard selectUniqueBy [(0, (0 : Int)), (1, -4)] = some (0, 0)
#guard selectUniqueBy [(0, (0 : Int)), (1, 0)] = none
#guard hitsBoth (-4) [⟨"one", ['A']⟩] ['C'] ≠ []
#guard hitsBoth (-3) [⟨"one", ['A']⟩] ['C'] = []
#guard mapReadFast 0 toyGenome ['G', 'T'] = mapReadSpec 0 toyGenome ['G', 'T']

-- A genuinely BOUNDED example: this reports A-versus-C at penalty 4,
-- although the same genome contains an exact A match at penalty 0.
-- Its CIGAR is sound, but it is not an optimal genome-wide mapping.
-- `decide +native` evaluates these tiny closed examples (like #guard);
-- the general soundness/interval proofs above do not depend on native evaluation.
def demoBounds : MateBounds :=
  { lowerPenalty := 0, upperPenalty := 4,
    reported := some (((⟨0, 1, 1⟩, .fwd), -4), some #[(.diag, 1)]) }

theorem demoBounds_correct : MateBoundsCorrect toyGenome ['A'] demoBounds := by
  refine ⟨mateFloor_zero _ _, ?_, ?_⟩
  · change hitsBoth (-4) toyGenome ['A'] ≠ []
    decide +native
  · intro hit cigar h
    have heq : (((⟨0, 1, 1⟩, Strand.fwd), (-4 : Int)), some #[(AlignmentSpec.Step.diag, 1)]) = (hit, cigar) :=
      Option.some.inj h
    cases heq
    refine ⟨rfl, ⟨-4, by decide, by decide +native⟩, ?_⟩
    intro runs hr
    cases Option.some.inj hr
    exact ⟨['C'], rfl, by constructor <;> decide⟩

theorem demoBestPenalty : BestPenalty toyGenome ['A'] 0 := by
  refine ⟨⟨0, ((⟨0, 0, 1⟩, .fwd), 0), by decide +native, rfl⟩, ?_⟩
  exact mateFloor_zero _ _

example : (demoBounds.lowerPenalty : Int) ≤ 0 ∧ 0 ≤ (demoBounds.upperPenalty : Int) :=
  bounded_result_interval demoBounds_correct demoBestPenalty

end NewSpec
