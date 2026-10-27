import new_spec.Mapping
import Init.Data.List.Perm

/-!
# 3. One trimmed pair, conditional exactness/bounds, and all pairs

This is the main review file. Start with ProperPair and mapPairSpec.
Inputs are ALREADY TRIMMED; minimum length is a hypothesis at the public theorem.
The tiny examples intentionally use a smaller minimum. No trimming or file IO here.

Latest source reviewed: claude/upbeat-goldberg-kizkfd @ f23e892775855f38f2edbb0233ed37fe99550a5c.
Its `MapSpec.Fast.tierPair_sound` (codecs/TierOpt.lean) proves `TierOk`:
  T1        -> independent unique mates, at the returned c1/c2 caps;
  T1g/T1u   -> unique best proper pair, for EVERY pair of caps >= g0;
  T1gm/T1um -> a proved best-pair tie, for EVERY pair of caps >= g0;
  T2b       -> a globally best proper pair, possibly tied;
  T2        -> per-mate floors AND ceilings (not necessarily a proper pair);
  T3        -> floors only; NOT evidence that the read is unmappable.
T0 means a mate was trimmed away; it is excluded from our present input type.

The result contract below gives readable names to these semantic claims. It is
NOT yet a compiled adapter to that remote router: this checkout lacks TierOpt.
That adapter must translate its types/tags and discharge the exact hypotheses:
  cutOk G offs ns = true;
  GenomeBytes ((cutAll G offs ns).map Mz.unpack) genome;
  Mz.check2P index G = true;
  Encodes packedMate1 reads.mate1; Encodes packedMate2 reads.mate2.
Then use `tierPair_sound` and case-split on the tag. Do not replace the checked
Mz index hypothesis with the older SeedMapper.Index contract in Mapping.lean.
The operational g0 <= 7 / <= 16 and fastT certificates remain in TierOk; this
public view retains their semantic conclusions, not those search-strategy details.

The exact baseline theorem below IS connected to executable local code and
checked here. `TierKernelCorrect` is explicitly a proof slot for the newer router.
-/

namespace NewSpec

structure ReadPair where
  mate1 : Read
  mate2 : Read
deriving DecidableEq, Repr

structure FragmentBounds where
  minLength : Nat
  maxLength : Nat

structure PairMappingConfig where
  fragmentBounds : FragmentBounds
  minReadLength : Nat := 30
  mate1MaxPenalty : Nat
  mate2MaxPenalty : Nat
  dovetailSlack : Nat := 0

abbrev PairHit := Hit × Hit

def InputLengths (config : PairMappingConfig) (reads : ReadPair) : Prop :=
  config.minReadLength ≤ reads.mate1.length ∧ config.minReadLength ≤ reads.mate2.length
instance (config : PairMappingConfig) (reads : ReadPair) : Decidable (InputLengths config reads) :=
  inferInstanceAs (Decidable (_ ∧ _))

def forwardReverse (a b : Placement) : Placement × Placement :=
  if a.2 = .fwd then (a, b) else (b, a)

/-- Length from the forward start to the reverse end, in reference bases.
Only interpreted as a fragment length when ProperPair holds. -/
def fragmentLength (a b : Placement) : Nat :=
  let (forward, reverse) := forwardReverse a b
  reverse.1.start + reverse.1.len - forward.1.start

/-- The EXISTING per-mate mode's orientation test, spelled out for review.
It permits overlap/dovetail: it checks forward.start <= reverse.end, NOT
forward.start <= reverse.start. Do not mistake this for an already agreed
stronger orientation rule. Edit this definition if your intended rule differs. -/
def ProperPair (bounds : FragmentBounds) (a b : Placement) : Prop :=
  let (forward, reverse) := forwardReverse a b
  forward.1.chr = reverse.1.chr ∧ forward.2 = .fwd ∧ reverse.2 = .rev ∧
  forward.1.start ≤ reverse.1.start + reverse.1.len ∧
  bounds.minLength ≤ fragmentLength a b ∧ fragmentLength a b ≤ bounds.maxLength
instance (bounds : FragmentBounds) (a b : Placement) : Decidable (ProperPair bounds a b) := by
  unfold ProperPair; infer_instance

/-- The newer pair-unique mode's extra no-dovetail checks, with explicit slack.
At slack zero: forward.start <= reverse.start AND forward.end <= reverse.end.
Overlapping mates can still be proper. -/
def ProperPairUnique (config : PairMappingConfig) (a b : Placement) : Prop :=
  let (forward, reverse) := forwardReverse a b
  ProperPair config.fragmentBounds a b ∧
  forward.1.start ≤ reverse.1.start + config.dovetailSlack ∧
  forward.1.start + forward.1.len ≤ reverse.1.start + reverse.1.len + config.dovetailSlack
instance (config : PairMappingConfig) (a b : Placement) : Decidable (ProperPairUnique config a b) := by
  unfold ProperPairUnique; infer_instance

/-- Independent uniqueness: pairing does not rescue either mate's ambiguity. -/
def mapPairAtCaps (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (mate1MaxPenalty mate2MaxPenalty : Nat) : Option PairHit :=
  match mapReadSpec mate1MaxPenalty genome reads.mate1,
        mapReadSpec mate2MaxPenalty genome reads.mate2 with
  | some a, some b => if ProperPair config.fragmentBounds a.1 b.1 then some (a, b) else none
  | _, _ => none

def mapPairSpec (config : PairMappingConfig) (genome : Genome) (reads : ReadPair) : Option PairHit :=
  mapPairAtCaps config genome reads config.mate1MaxPenalty config.mate2MaxPenalty

def processPairFast (config : PairMappingConfig) (genome : Genome) (reads : ReadPair) : Option PairHit :=
  if InputLengths config reads then
    match mapReadFast config.mate1MaxPenalty genome reads.mate1,
          mapReadFast config.mate2MaxPenalty genome reads.mate2 with
    | some a, some b => if ProperPair config.fragmentBounds a.1 b.1 then some (a, b) else none
    | _, _ => none
  else none

/-- Composition for the executable baseline, including rejection (`none`).
It reuses the proved fast alignment scorer over exhaustive windows. -/
theorem processPairFast_eq_spec (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (hLength : InputLengths config reads) :
    processPairFast config genome reads = mapPairSpec config genome reads := by
  simp only [processPairFast, hLength, if_pos, mapReadFast_eq_spec, mapPairSpec, mapPairAtCaps]

/-! Pair-level uniqueness is a separate policy. The latest tier router uses
dcost0: pair score = the sum of mate scores, with no fragment-length penalty. -/

def pairScore (pair : PairHit) : Int := pair.1.2 + pair.2.2
def pairKey (pair : PairHit) : Placement × Placement := (pair.1.1, pair.2.1)

def properPairs (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (mate1MaxPenalty mate2MaxPenalty : Nat) : List PairHit :=
  (hitsBoth (-(mate1MaxPenalty : Int)) genome reads.mate1).flatMap fun a =>
    ((hitsBoth (-(mate2MaxPenalty : Int)) genome reads.mate2).filter
      fun b => decide (ProperPairUnique config a.1 b.1)).map fun b => (a, b)

def selectUniquePair (pairs : List PairHit) : Option PairHit :=
  pairs.find? fun p => pairs.all fun q => decide (pairScore q < pairScore p) || decide (pairKey q = pairKey p)

def mapPairUniqueSpec (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (mate1MaxPenalty mate2MaxPenalty : Nat) : Option PairHit :=
  selectUniquePair (properPairs config genome reads mate1MaxPenalty mate2MaxPenalty)

/-- Matches the existing PairTieOk: there are proper candidates, but no unique
best. Keeping nonemptiness is essential: no candidates is not a proved tie. -/
def PairTie (pairs : List PairHit) : Prop :=
  selectUniquePair pairs = none ∧ pairs ≠ []

def PairOptimal (config : PairMappingConfig) (genome : Genome) (reads : ReadPair) (pair : PairHit) : Prop :=
  (∃ cap1 cap2, pair ∈ properPairs config genome reads cap1 cap2) ∧
  ∀ cap1 cap2, ∀ other ∈ properPairs config genome reads cap1 cap2, pairScore other ≤ pairScore pair

/-- Optional extra certificate: every proper pair has penalty STRICTLY > G0,
for any two per-mate search caps at least G0. `none` makes no pair-floor claim. -/
def PairFloorCorrect (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (floor : Option Nat) : Prop :=
  ∀ bound, floor = some bound → ∀ cap1 cap2, bound ≤ cap1 → bound ≤ cap2 →
    ∀ pair ∈ properPairs config genome reads cap1 cap2, pairScore pair < -(bound : Int)

/-- A semantic view of the tier result, not a file/output-format specification. -/
inductive PairResult where
  | exactMates (cap1 cap2 : Nat) (pair : PairHit)
  | exactPair (guaranteeCap : Nat) (pair : PairHit)
  | tiedPair (guaranteeCap : Nat)
  | optimalPair (pair : PairHit)
  | bounded (mate1 mate2 : MateBounds) (pairFloor : Option Nat)
  | floors (mate1Lower mate2Lower : Nat) (pairFloor : Option Nat)

def PairResultCorrect (config : PairMappingConfig) (genome : Genome) (reads : ReadPair) : PairResult → Prop
  | .exactMates cap1 cap2 pair => mapPairAtCaps config genome reads cap1 cap2 = some pair
  | .exactPair guarantee pair =>
    ∀ cap1 cap2, guarantee ≤ cap1 → guarantee ≤ cap2 →
      mapPairUniqueSpec config genome reads cap1 cap2 = some pair
  | .tiedPair guarantee =>
    ∀ cap1 cap2, guarantee ≤ cap1 → guarantee ≤ cap2 →
      PairTie (properPairs config genome reads cap1 cap2)
  | .optimalPair pair => PairOptimal config genome reads pair
  | .bounded b1 b2 pairFloor =>
    MateBoundsCorrect genome reads.mate1 b1 ∧ MateBoundsCorrect genome reads.mate2 b2 ∧
      PairFloorCorrect config genome reads pairFloor
  | .floors lower1 lower2 pairFloor =>
    MateFloor genome reads.mate1 lower1 ∧ MateFloor genome reads.mate2 lower2 ∧
      PairFloorCorrect config genome reads pairFloor

/-- This slot must be filled by a concrete implementation theorem. In particular,
an index checker or a heuristic alone does not supply this proof. Capture the
genome/index assumptions when constructing `run` and its proof. `Supported`
exposes any byte-encoding/domain assumptions; already trimmed does not imply them. -/
def TierKernelCorrect (config : PairMappingConfig) (genome : Genome)
    (Supported : ReadPair → Prop) (run : ReadPair → PairResult) : Prop :=
  ∀ reads, InputLengths config reads → Supported reads → PairResultCorrect config genome reads (run reads)

/-- Conditional exactness for the newer router interface: only its exact branch
asserts equality to the unique-pair reference. The proof slot is explicit. -/
theorem exact_result_matches_spec (config : PairMappingConfig) (genome : Genome)
    (Supported : ReadPair → Prop) (run : ReadPair → PairResult)
    (hKernel : TierKernelCorrect config genome Supported run)
    (reads : ReadPair) (hLength : InputLengths config reads) (hSupported : Supported reads)
    (guarantee cap1 cap2 : Nat) (pair : PairHit)
    (hResult : run reads = .exactPair guarantee pair) (h1 : guarantee ≤ cap1) (h2 : guarantee ≤ cap2) :
    mapPairUniqueSpec config genome reads cap1 cap2 = some pair := by
  have h := hKernel reads hLength hSupported
  rw [hResult] at h
  exact h cap1 cap2 h1 h2

theorem exact_mates_match_spec (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (cap1 cap2 : Nat) (pair : PairHit)
    (h : PairResultCorrect config genome reads (.exactMates cap1 cap2 pair)) :
    mapPairAtCaps config genome reads cap1 cap2 = some pair := h

/-- T2b certifies optimality even when uniqueness cannot be claimed. -/
theorem optimal_result_no_better_pair (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (pair : PairHit) (h : PairResultCorrect config genome reads (.optimalPair pair))
    (cap1 cap2 : Nat) (other : PairHit) (hOther : other ∈ properPairs config genome reads cap1 cap2) :
    pairScore other ≤ pairScore pair := h.2 cap1 cap2 other hOther

/-- A bounded result gives intervals for BOTH mate optima, without asserting
unique placements, a proper reported pair, or an exact optimal CIGAR. -/
theorem bounded_pair_intervals (config : PairMappingConfig) (genome : Genome) (reads : ReadPair)
    (b1 b2 : MateBounds) (pairFloor : Option Nat)
    (h : PairResultCorrect config genome reads (.bounded b1 b2 pairFloor))
    (best1 best2 : Int) (h1 : BestPenalty genome reads.mate1 best1) (h2 : BestPenalty genome reads.mate2 best2) :
    ((b1.lowerPenalty : Int) ≤ best1 ∧ best1 ≤ (b1.upperPenalty : Int)) ∧
    ((b2.lowerPenalty : Int) ≤ best2 ∧ best2 ≤ (b2.upperPenalty : Int)) :=
  ⟨bounded_result_interval h.1 h1, bounded_result_interval h.2.1 h2⟩

/-! Process all / chunking. Each occurrence keeps its input and result together;
the List.Perm hypothesis preserves duplicate inputs. Add stable read IDs to the
input type if identical sequences with different IDs must remain distinguishable.
This models pure chunk evaluation, not a proof of a scheduler or parallel IO. -/

def processAll {Input Result : Type} (process : Input → Result) (inputs : List Input) : List (Input × Result) :=
  inputs.map fun input => (input, process input)

def processChunks {Input Result : Type} (process : Input → Result) (chunks : List (List Input)) :
    List (Input × Result) :=
  (chunks.map (processAll process)).flatten

/-- All results retain the one-pair contract; exact/bounded cases stay distinct. -/
theorem processAll_tier_correct (config : PairMappingConfig) (genome : Genome)
    (Supported : ReadPair → Prop) (run : ReadPair → PairResult)
    (hKernel : TierKernelCorrect config genome Supported run) (inputs : List ReadPair)
    (hInputs : ∀ reads ∈ inputs, InputLengths config reads ∧ Supported reads) :
    ∀ item ∈ processAll run inputs, PairResultCorrect config genome item.1 item.2 := by
  intro item hmem
  obtain ⟨reads, hr, rfl⟩ := List.mem_map.mp hmem
  exact hKernel reads (hInputs reads hr).1 (hInputs reads hr).2

theorem processChunks_perm_processAll {Input Result : Type} (process : Input → Result)
    (inputs : List Input) (chunks : List (List Input)) (hChunks : chunks.flatten.Perm inputs) :
    (processChunks process chunks).Perm (processAll process inputs) := by
  have heq : processChunks process chunks = processAll process chunks.flatten := by
    change (chunks.map (List.map (fun input => (input, process input)))).flatten =
      chunks.flatten.map (fun input => (input, process input))
    rw [List.map_flatten]
  rw [heq]
  exact hChunks.map (fun input => (input, process input))

theorem processAllFast_eq_spec (config : PairMappingConfig) (genome : Genome) (inputs : List ReadPair)
    (hLength : ∀ reads ∈ inputs, InputLengths config reads) :
    processAll (processPairFast config genome) inputs = processAll (mapPairSpec config genome) inputs := by
  apply List.map_congr_left
  intro reads hmem
  rw [processPairFast_eq_spec config genome reads (hLength reads hmem)]

theorem processChunksFast_perm_spec (config : PairMappingConfig) (genome : Genome)
    (inputs : List ReadPair) (chunks : List (List ReadPair))
    (hLength : ∀ reads ∈ inputs, InputLengths config reads) (hChunks : chunks.flatten.Perm inputs) :
    (processChunks (processPairFast config genome) chunks).Perm
      (processAll (mapPairSpec config genome) inputs) := by
  rw [← processAllFast_eq_spec config genome inputs hLength]
  exact processChunks_perm_processAll _ inputs chunks hChunks

-- Readable, runnable paired examples. Bounds are inclusive.
def demoConfig : PairMappingConfig :=
  { fragmentBounds := ⟨2, 2⟩, minReadLength := 1, mate1MaxPenalty := 0, mate2MaxPenalty := 0 }
def demoReads : ReadPair := ⟨['A'], ['G']⟩
def demoPair : PairHit := (((⟨0, 0, 1⟩, .fwd), 0), ((⟨0, 1, 1⟩, .rev), 0))

#guard mapPairSpec demoConfig toyGenome demoReads = some demoPair
#guard processPairFast demoConfig toyGenome demoReads = some demoPair
#guard mapPairUniqueSpec demoConfig toyGenome demoReads 0 0 = some demoPair
#guard processPairFast { demoConfig with minReadLength := 30 } toyGenome demoReads = none
example : ProperPair demoConfig.fragmentBounds demoPair.1.1 demoPair.2.1 := by decide
example : ¬ ProperPair ⟨3, 10⟩ demoPair.1.1 demoPair.2.1 := by decide
example : ¬ ProperPair ⟨0, 10⟩ (⟨0, 0, 1⟩, .fwd) (⟨0, 1, 1⟩, .fwd) := by decide

-- Existing broad orientation versus the newer no-dovetail rule: review this!
example : ProperPair ⟨0, 10⟩ (⟨0, 2, 2⟩, .fwd) (⟨0, 1, 2⟩, .rev) := by decide
example : ¬ ProperPairUnique { demoConfig with fragmentBounds := ⟨0, 10⟩ }
    (⟨0, 2, 2⟩, .fwd) (⟨0, 1, 2⟩, .rev) := by decide

-- Pair-only uniqueness can rescue an ambiguous mate. This is a DIFFERENT mode.
def rescueGenome : Genome := [⟨"two-As", ['A', 'A', 'C']⟩]
#guard mapPairSpec demoConfig rescueGenome demoReads = none
#guard mapPairUniqueSpec demoConfig rescueGenome demoReads 0 0 =
  some ((((⟨0, 1, 1⟩, .fwd), 0), ((⟨0, 2, 1⟩, .rev), 0)))
#guard selectUniquePair [demoPair, (((⟨0, 2, 1⟩, .fwd), 0), demoPair.2)] = none

-- A concrete bounded-pair certificate, including the meaningful nonoptimal
-- reported CIGAR from Mapping.lean. No proper-pair claim is made for T2.
example : PairResultCorrect demoConfig toyGenome ⟨['A'], ['A']⟩
    (.bounded demoBounds demoBounds none) := by
  refine ⟨demoBounds_correct, demoBounds_correct, ?_⟩
  intro bound h
  cases h

-- Reordering is allowed; losing a duplicate is not.
example : ([[2], [], [1, 1]] : List (List Nat)).flatten.Perm [1, 2, 1] := by decide
example : ¬ ([[2], [1]] : List (List Nat)).flatten.Perm [1, 2, 1] := by decide
example : (processChunks (fun n : Nat => n + 10) [[2], [], [1, 1]]).Perm
    (processAll (fun n : Nat => n + 10) [1, 2, 1]) :=
  processChunks_perm_processAll _ _ _ (by decide)

end NewSpec
