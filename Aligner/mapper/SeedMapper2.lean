import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import WfaU3                      -- the proved pairwise codec
import MapperWalk2                -- pool: clean seed and window shape from the affine cost
import MapperLists                -- pool: list and table lemmas
import SeedMapper                 -- LookupComplete, Index, kernelScore and their lemmas

/-!
# Codec `indexMapper2`: seed-and-index read mapper with sharper bounds

Same plan as `indexMapper`, with bounds that use the affine gap cost
(`pool/mapper/MapperWalk2.lean`):

* the read is cut into `seedBound sc T + 1` seeds (4 for the default scoring
  and `T = −12`, instead of 7);
* each seed hit gives only the windows whose start shift `s` and end shift
  `t` satisfy `shapeOk (gapBound sc T) (gapBound2 sc T) s t`
  (19 for the default scoring, instead of 169).

A seed hit can also be filtered by `keep` before its windows are made.
`keep` may drop a hit only where the full seed does not occur in the genome
(`KeepComplete`).  Two instances: keep everything (`mapWith2`), or keep a hit
only when the whole seed matches the genome there (`mapWith2V`).
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- The allowed (start shift, end shift) pairs. -/
def shapes (d d2 : Nat) : List (Int × Int) :=
  ((List.range (2 * d + 1)).flatMap fun (a : Nat) =>
    (List.range (2 * d + 1)).map fun (b : Nat) => ((a : Int) - d, (b : Int) - d)).filter
    fun st => decide (shapeOk d d2 st.1 st.2)

example : (shapes 3 0).length = 19 := by decide +kernel

/-! ## The theorems

    mapWith2  lookup score l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read                                                  (mapWith2_eq_mapSpec)
    mapWith2V … = mapSpec sc T g read                                        (mapWith2V_eq_mapSpec)
    indexMapper2 l0 sc T g read = mapSpec sc T g read                        (indexMapper2_eq_mapSpec)
    indexMapper2V l0 sc T g read = mapSpec sc T g read                       (indexMapper2V_eq_mapSpec)
    mapReads2 l0 sc T g reads = reads.map (mapSpec sc T g)                   (mapReads2_eq_mapSpec)
    mapReads2V l0 sc T g reads = reads.map (mapSpec sc T g)                  (mapReads2V_eq_mapSpec)

given `ValidScoring sc`, and for `mapWith2`/`mapWith2V` a complete lookup
(`LookupComplete g l0 lookup`) and a scorer equal to `windowScore`. -/

/-! ## Proof -/

/-- `keep` accepts every place where the seed occurs. -/
def KeepComplete (g : Genome) (keep : List Char → Nat × Nat → Bool) : Prop :=
  ∀ (c : Nat) (chromosome : Chromosome) (p : Nat) (w : List Char), g[c]? = some chromosome →
    p + w.length ≤ chromosome.seq.length → (chromosome.seq.drop p).take w.length = w →
    keep w (c, p) = true

theorem keepAll_complete (g : Genome) : KeepComplete g (fun _ _ => true) :=
  fun _ _ _ _ _ _ _ => rfl

theorem mem_shapes (d d2 : Nat) (s t : Int) (h : shapeOk d d2 s t) : (s, t) ∈ shapes d d2 := by
  unfold shapes
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true h⟩
  have h1 := h.1
  rw [List.mem_flatMap]
  refine ⟨(s + d).toNat, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_map]
  refine ⟨(t + d).toNat, List.mem_range.mpr (by omega), ?_⟩
  simp only [Prod.mk.injEq]
  omega

end MapSpec

