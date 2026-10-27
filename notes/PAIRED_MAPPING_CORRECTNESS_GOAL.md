# Goal: one readable correctness theorem for paired-end mapping

Recorded from Rowan's review of the paired-end work on
`claude/upbeat-goldberg-kizkfd`, inspected at commit `9d42442`.

This note records the intended interface and proof goal. The names and Lean
statements below are proposed, not declarations that have been implemented or
checked. No mapping implementation or existing specification is changed by
this note.

## Immediate scope

Assemble a single, readable theorem connecting the fast genome-wide mapper
for one read pair to the exhaustive paired-end specification. Reuse the
existing component proofs. Output formatting, file writing, CLI behavior,
and parallel IO are outside this stage.

The two input mates are already trimmed. The mapping theorem assumes both
meet the required minimum length; it does not prove the trimming operation.
Upstream processing discards mates that are too short after trimming.
Any length-dependent penalty limits use the trimmed lengths.

## Intended mapping behavior

For each mate, search all valid windows of all chromosomes on both strands.
The reverse strand is represented explicitly in the placement, with
coordinates on the original reference chromosome.

Each mate must independently have a unique highest-scoring placement within
its own inclusive penalty limit. Worse alternative placements are allowed;
a tie between distinct best placements makes that mate ambiguous. Pairing
does not resolve a mate's ambiguity in this speed version.

Return the two placements and their individual scores exactly when both
mates qualify and their placements form a proper pair. Otherwise return
`none`.

`ProperPair` must be a separately readable definition requiring:

- the same chromosome;
- opposite strands;
- orientation towards each other;
- fragment length within configurable inclusive bounds.

Distance bounds may be loose. Name them `minLength` and `maxLength`, with
units of reference bases, rather than leaving `lo` and `hi` unexplained.
The exact orientation inequalities and treatment of overlapping placements
still need review. The inspected draft checks forward start <= reverse end;
that condition must not silently be treated as Rowan's final definition of
"towards each other."

The current fast mapper uses match score 0, mismatch penalty 4, and gap
penalty 6 + 2*k for a gap of length k. A penalty limit is a weighted alignment
penalty, not an unweighted error count or error percentage.

## Readable public inputs

```lean
structure ReadPair where
  mate1 : List Char
  mate2 : List Char

structure FragmentBounds where
  minLength : Nat
  maxLength : Nat

structure PairMappingConfig where
  fragmentBounds : FragmentBounds
  minReadLength : Nat
  mate1MaxPenalty : Nat
  mate2MaxPenalty : Nat
```

The supported relationship between read length and penalty limits must match
the chosen fast implementation. This note does not choose a new numerical
minimum or claim every configuration runs on the fast path.

Both the reference and fast interface should receive the same `config`,
`genome`, and `reads`. Byte encodings, packed copies, offsets, and proofs that
these representations agree belong behind the public wrapper. Existing
representation assumptions must be discharged, not dropped.

Already trimmed does not by itself assert an A/C/G/T-only alphabet. If the
selected implementation needs that condition, expose it as an explicit
input requirement or discharge it through the upstream interface.

## The combined theorem

Proposed public statement (proof omitted):

```lean
theorem mapPairFast_eq_spec
    (config : PairMappingConfig)
    (genome : Genome)
    (index : GenomeIndex)
    (reads : ReadPair)
    (hIndex : IndexMapFastCorrect genome index)
    (hLength :
      config.minReadLength <= reads.mate1.length ∧
      config.minReadLength <= reads.mate2.length) :
    mapPairFast config genome index reads =
      mapPairSpec config genome reads
```

Meaning: given the correct index for this mapper and genome, and two trimmed
mates meeting the minimum length, the fast implementation returns exactly
the exhaustive specification's answer. Equality includes `none`: it covers
finding every qualifying pair and rejecting pairs that do not qualify.

## Index correctness: tie it to the mapper's index contract

Use the name `IndexMapFastCorrect`, rather than an unexplained generic
`IndexCorrect`. It must refer to the index consumed by this particular fast
mapper and to the supplied genome.

Rowan's concrete interpretation is equality with the designated indexing
function's result. The simplest definition is:

```lean
def IndexMapFastCorrect (genome : Genome) (index : GenomeIndex) : Prop :=
  index = createIndex genome
```

Here `createIndex` is the designated builder for this index algorithm and
configuration. If its behavior depends on seed length or other indexing
parameters, those parameters must also appear in the contract or be fixed
explicitly. The mapper cannot accept an index built for a different genome
or incompatible indexing configuration.

With this equality definition, `IndexMapFastCorrect genome (createIndex
genome)` is reflexive. That alone does not establish the builder's semantic
correctness: the proof of mapper correctness must still show that the
builder's lookups satisfy the properties the mapper relies on.

A more general, recommended formulation is to define `IndexMapFastCorrect`
by the actual index contract needed by the mapper, including the required
lookup completeness and representation properties. Then prove:

```lean
theorem createIndex_correct (genome : Genome) :
    IndexMapFastCorrect genome (createIndex genome)
```

This permits different valid layouts or builders when they satisfy the same
contract. It does not require their index values to be structurally equal.
Equality to the designated builder's result is then a sufficient way to
establish correctness, by substitution and `createIndex_correct`.

The final predicate definition must be reviewed before implementation;
exact builder equality and semantic contract satisfaction are alternatives,
not interchangeable claims.

If an executable Boolean checker is also provided, distinguish it from the
proposition and prove its soundness:

```lean
checkIndexMapFast genome index = true →
  IndexMapFastCorrect genome index
```

The existing branch's concrete mapper theorems assume successful index
checks (or abstract lookup correctness), along with encoding and genome
layout assumptions. They do not yet express the proposed public builder
interface merely by changing the assumption's name.

## Existing proof ingredients to reuse

At the inspected branch commit:

- `spec/PairSpec.lean`: `pairSpec`, `mapSpecBoth`, and `properPair`.
- `codecs/FastGenPair.lean`: `pairFastGB_eq_pairSpec`, with concrete hashed
  and minimizer index versions.
- `codecs/PairDispatch.lean`: `pairSpecT` and
  `pairDispatch_eq_pairSpecT` for separate per-mate thresholds; word-kernel
  variants also have connecting theorems.

The immediate work is to review the definitions, provide readable wrappers,
and assemble the existing proofs into the combined statement. Source was
inspected; no new wrapper theorem has been compiled during this review.

## Later: process all pairs

The sequential specification will apply the one-pair specification to all
input pairs. The parallel result need only agree up to permutation, retaining
the association between each input pair and its result and preserving
multiplicities. No pairs may be lost or duplicated.

`ParMap.parMap_eq_map` already establishes the stronger ordered equality for
the existing pure parallel mapper and can be composed with the one-pair
theorem. A different collector that returns results in completion order
needs its own permutation connection. None of this requires an output-file
specification at the current stage.
