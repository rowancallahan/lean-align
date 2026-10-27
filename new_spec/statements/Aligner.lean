import new_spec.statements.Mapping

/-!
# 3. The aligner, and what each of its answers proves

Statements only: every proof is `sorry`. Imports only Mapping.

Each answer is mapped (T1, T1g, T1u) or unmapped with a reason (trimmed away, T1gm,
T1um, T2b, T2, T3). Each router tag's claim is the router's `TierOk`
(codecs/TierRouter.lean), copied with the same signs: scores and thresholds, a cap `P`
entering as the threshold `-(P : Int)`. Not carried over: the T1g / T1gm condition that
the enumerated mate passes `fastT`, which refers to implementation code.
The tier constructors keep the router's tag names until Rowan names them.

Name in the proofs → name here:
  TierCfg.lo, .hi, .usl → PairConfig.minFragment, .maxFragment, .dovetailSlack
  MateX → MateBounds; cd → floor, pl → placement, pH → ceiling, rs → ceilingChecked,
    cg → hasCigar, runs → cigar; MateX.ok → MateBounds.hasCeiling
  CeilEv → CeilingEvidence, CeilOk → CeilingOk, FloorOk → FloorsOk
  c1, c2 → cap1, cap2; g0 → guaranteeCap; pf → noPairWithin; G0 → pairGuarantee

`buildIndex` and `alignPair` are the two definitions the implementation fills in
(comparator `definition_names`). They are separate so the index can be built once,
saved, and supplied to the aligner as data. The theorem assumes the index bytes are
`buildIndex`'s output; at run time a saved index is checked by its hash, and that check
stands in for the assumption (trusted, not proved).

Build (after Mapping):

    lake env lean -o .lake/build/lib/lean/new_spec/statements/Aligner.olean new_spec/statements/Aligner.lean
-/

namespace NewSpec

/-- The router's pair settings (`TierCfg`). -/
structure PairConfig where
  minFragment : Nat
  maxFragment : Nat
  dovetailSlack : Nat := 0

inductive Mate where
  | one
  | two
deriving DecidableEq, Repr

/-- One mate's tier-2 evidence: the router's `MateX` fields that `TierOk` reads. -/
structure MateBounds where
  floor : Nat := 0
  placement : Option (Placement × Int) := none
  ceiling : Nat := 1000000
  ceilingChecked : Bool := true
  hasCigar : Bool := false
  cigar : List (Step × Nat) := []

def MateBounds.hasCeiling (bounds : MateBounds) : Bool :=
  decide (bounds.ceiling < 1000000) && bounds.ceilingChecked

/-- What a claimed ceiling means: a placement within it exists; a reported alignment is a real one. -/
def CeilingEvidence (genome : Genome) (mate : List Char) (bounds : MateBounds) : Prop :=
  bounds.hasCeiling = true → hitsBothStrands defaultScoring (-(bounds.ceiling : Int)) genome mate ≠ [] ∧
    (bounds.hasCigar = true → ∃ hit, bounds.placement = some hit ∧ hit.2 = -(bounds.ceiling : Int) ∧
      CigarOk genome mate hit bounds.cigar) ∧
    ∀ hit, bounds.placement = some hit → hit.2 = -(bounds.ceiling : Int) ∧
      ∃ score, hit.2 ≤ score ∧ (hit.1, score) ∈ hitsBothStrands defaultScoring hit.2 genome mate

/-- A ceiling (tier 2). -/
def CeilingOk (genome : Genome) (mate : List Char) (bounds : MateBounds) : Prop :=
  bounds.hasCeiling = true ∧ CeilingEvidence genome mate bounds

/-- Proved floors: per mate, and every proper pair scoring below `-pairGuarantee` when
the guarantee found no proper pair within it. -/
def FloorsOk (config : PairConfig) (genome : Genome) (mate1 mate2 : List Char)
    (floor1 floor2 : Nat) (noPairWithin : Option Nat) : Prop :=
  MateFloor genome mate1 floor1 ∧ MateFloor genome mate2 floor2 ∧
    ∀ pairGuarantee, noPairWithin = some pairGuarantee → ∀ cap1 cap2 : Nat,
      pairGuarantee ≤ cap1 → pairGuarantee ≤ cap2 →
      ∀ pair ∈ properPairs config.dovetailSlack config.minFragment config.maxFragment
          (hitsBothStrands defaultScoring (-(cap1 : Int)) genome mate1)
          (hitsBothStrands defaultScoring (-(cap2 : Int)) genome mate2),
        pairScore noDistanceCost pair < -(pairGuarantee : Int)

/-- A reported pair, by the tier that proved it. -/
inductive Mapped where
  /-- T1: each mate unique on its own at `cap1`, `cap2`, and a proper pair. -/
  | t1 (cap1 cap2 : Nat) (hit1 hit2 : Placement × Int)
  /-- T1g: the unique best proper pair at every pair of caps `≥ guaranteeCap` (`≤ 7`). -/
  | t1g (guaranteeCap : Nat) (hit1 hit2 : Placement × Int)
  /-- T1u: the unique best proper pair at every pair of caps `≥ guaranteeCap` (`≤ 16`). -/
  | t1u (guaranteeCap : Nat) (hit1 hit2 : Placement × Int)

/-- Why a pair is not reported, with what was proved about it. -/
inductive Unmapped where
  /-- T0: a mate was trimmed away. Nothing is searched. -/
  | trimmedAway (mate : Mate)
  /-- T1gm: a proved best-pair tie at every pair of caps `≥ guaranteeCap` (`≤ 7`). -/
  | t1gm (guaranteeCap : Nat)
  /-- T1um: a proved best-pair tie at every pair of caps `≥ guaranteeCap` (`≤ 16`). -/
  | t1um (guaranteeCap : Nat)
  /-- T2b: a globally best proper pair, possibly tied (uniqueness not proved). -/
  | t2b (hit1 hit2 : Placement × Int)
  /-- T2: per-mate floors and ceilings; not necessarily a proper pair. -/
  | t2 (bounds1 bounds2 : MateBounds) (noPairWithin : Option Nat)
  /-- T3: floors only; not evidence that the pair is unmappable. -/
  | t3 (floor1 floor2 : Nat) (noPairWithin : Option Nat)

/-- The aligner's answer for one pair. -/
inductive PairResult where
  | mapped (result : Mapped)
  | unmapped (reason : Unmapped)

/-- What each mapped tier proves (`TierOk`). -/
def MappedCorrect (config : PairConfig) (genome : Genome) (mate1 mate2 : List Char) : Mapped → Prop
  | .t1 cap1 cap2 hit1 hit2 =>
    mapPairEachMate (-(cap1 : Int)) (-(cap2 : Int)) config.minFragment config.maxFragment
      genome mate1 mate2 = some (hit1, hit2)
  | .t1g guaranteeCap hit1 hit2 => guaranteeCap ≤ 7 ∧
    ∀ cap1 cap2 : Nat, guaranteeCap ≤ cap1 → guaranteeCap ≤ cap2 →
      mapPairBest defaultScoring noDistanceCost config.dovetailSlack config.minFragment config.maxFragment
        (-(cap1 : Int)) (-(cap2 : Int)) genome mate1 mate2 = some (hit1, hit2)
  | .t1u guaranteeCap hit1 hit2 => guaranteeCap ≤ 16 ∧
    ∀ cap1 cap2 : Nat, guaranteeCap ≤ cap1 → guaranteeCap ≤ cap2 →
      mapPairBest defaultScoring noDistanceCost config.dovetailSlack config.minFragment config.maxFragment
        (-(cap1 : Int)) (-(cap2 : Int)) genome mate1 mate2 = some (hit1, hit2)

/-- What each unmapped reason proves (`TierOk`). `trimmed1`, `trimmed2` are the trimmed
mates (`none` = trimmed away). -/
def UnmappedCorrect (config : PairConfig) (genome : Genome) (trimmed1 trimmed2 : Option (List Char))
    (mate1 mate2 : List Char) : Unmapped → Prop
  | .trimmedAway .one => trimmed1 = none
  | .trimmedAway .two => trimmed2 = none
  | .t1gm guaranteeCap => guaranteeCap ≤ 7 ∧
    ∀ cap1 cap2 : Nat, guaranteeCap ≤ cap1 → guaranteeCap ≤ cap2 →
      PairTie noDistanceCost config.dovetailSlack config.minFragment config.maxFragment
        (-(cap1 : Int)) (-(cap2 : Int)) genome mate1 mate2
  | .t1um guaranteeCap => guaranteeCap ≤ 16 ∧
    ∀ cap1 cap2 : Nat, guaranteeCap ≤ cap1 → guaranteeCap ≤ cap2 →
      PairTie noDistanceCost config.dovetailSlack config.minFragment config.maxFragment
        (-(cap1 : Int)) (-(cap2 : Int)) genome mate1 mate2
  | .t2b hit1 hit2 =>
    (hit1, hit2) ∈ properPairs config.dovetailSlack config.minFragment config.maxFragment
      (hitsBothStrands defaultScoring hit1.2 genome mate1)
      (hitsBothStrands defaultScoring hit2.2 genome mate2) ∧
    ∀ threshold1 threshold2 : Int,
      ∀ pair ∈ properPairs config.dovetailSlack config.minFragment config.maxFragment
          (hitsBothStrands defaultScoring threshold1 genome mate1)
          (hitsBothStrands defaultScoring threshold2 genome mate2),
        pairScore noDistanceCost pair ≤ pairScore noDistanceCost (hit1, hit2)
  | .t2 bounds1 bounds2 noPairWithin =>
    FloorsOk config genome mate1 mate2 bounds1.floor bounds2.floor noPairWithin ∧
    CeilingOk genome mate1 bounds1 ∧ CeilingOk genome mate2 bounds2
  | .t3 floor1 floor2 noPairWithin =>
    FloorsOk config genome mate1 mate2 floor1 floor2 noPairWithin

/-- What the answer proves: its tier's claim if mapped, its reason's claim if not. -/
def PairResultCorrect (config : PairConfig) (genome : Genome) (trimmed1 trimmed2 : Option (List Char))
    (mate1 mate2 : List Char) : PairResult → Prop
  | .mapped result => MappedCorrect config genome mate1 mate2 result
  | .unmapped reason => UnmappedCorrect config genome trimmed1 trimmed2 mate1 mate2 reason

/-! ## The index and the aligner -/

/-- One byte per letter. -/
def decode (bytes : ByteArray) : List Char := bytes.toList.map fun byte => Char.ofNat byte.toNat

def decodeGenome (chromosomes : Array (String × ByteArray)) : Genome :=
  chromosomes.toList.map fun (name, sequence) => ⟨name, decode sequence⟩

/-- THE INDEX BUILDER. Filled in by the implementation. Plain bytes, so it can be
saved and supplied separately. -/
def buildIndex (genome : Array (String × ByteArray)) : ByteArray :=
  sorry

/-- THE ALIGNER. Filled in by the implementation. A trimmed-away mate is `none`. -/
def alignPair (config : PairConfig) (genome : Array (String × ByteArray)) (index : ByteArray)
    (mate1 mate2 : Option ByteArray) : PairResult :=
  sorry

/-- Every answer the aligner gives proves its claim, given the index built from this
genome (`tierPair_sound`). -/
theorem alignPair_correct (config : PairConfig) (genome : Array (String × ByteArray))
    (index : ByteArray) (hIndex : index = buildIndex genome) (mate1 mate2 : Option ByteArray) :
    PairResultCorrect config (decodeGenome genome) (mate1.map decode) (mate2.map decode)
      ((mate1.map decode).getD []) ((mate2.map decode).getD [])
      (alignPair config genome index mate1 mate2) := by
  sorry

end NewSpec
