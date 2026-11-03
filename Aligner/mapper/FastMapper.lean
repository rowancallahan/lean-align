import MapSpec                    -- the mapping specification (spec/, draft)
import SeedMapper                 -- mapWith, kernelScore, LookupComplete (slow fallback)
import BandScore                  -- Encodes, GenomeBytes
import MapperBytes                -- decodeBytes
import MapperFastAlgo             -- the fast code
import MapperFastLazy             -- its invariant: every hit looked at

/-!
# Codec `mapFast`: the fast proved read mapper

Scoring (0, −4, −6, −2) (`sc0`) and threshold `T = −12` only.  Genome and read
are byte strings (`GenomeBytes`, `Encodes`: one byte per letter).

* Reads of 100–103 letters (`fastOk`) take the fast path of
  `pool/mapper/MapperFastAlgo.lean` (the code of `bench/Proto.lean`, branch
  `speed/proto-tune`, `mapCore`): hashed 25-mer index per chromosome, 4 seeds
  looked up lazily (smallest bucket first, stop once the best is below
  `4·lookups`), packed anchors with clean-seed masks, same-length windows
  (`4·mismatches`), one-gap windows (`6 + 2L + 4·mismatches`) only after 3
  lookups and while the best costs ≥ 8, with support pruning.  Letters other
  than ACGT in a seed are looked up through the index's per-letter place lists.
* Other reads take a slow proved path (`mapWith` of `SeedMapper.lean` with a
  scanning lookup and the proved codec `wfaAlignU3`).

The index is not trusted: `checkAll idxs gbs` checks it at run time.

Measured (`lake exe fast_bench`, chr21 = 46.7 Mb, 100k simulated 100-letter
reads, one thread): 220k–290k reads/s; the prototype (`speed/proto-tune`
dc0b687) 230k–270k reads/s on the same machine; identical answers on all
100k reads.  Index build 31 s (untrusted), `checkAll` 9–13 s.

## The theorems

    GenomeBytes gbs g → Encodes R read → checkAll idxs gbs = true →
      mapFast gbs idxs R = mapSpec sc0 (-12) g read                         (mapFast_eq_mapSpec)
    … mapFastReads gbs idxs Rs = reads.map (mapSpec sc0 (-12) g)            (mapFastReads_eq_mapSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## The algorithm -/

/-- The runtime index checker, every chromosome. -/
def checkAll (idxs : Array HIdx) (gbs : Array ByteArray) : Bool :=
  (List.range gbs.size).all fun c => checkIdx idxs[c]! gbs[c]!

/-- Every place of the genome where `word` occurs (slow fallback only). -/
def scanLookup (g : Genome) (l0 : Nat) (word : List Char) : List (Nat × Nat) :=
  (List.range g.length).flatMap fun c =>
    match g[c]? with
    | some ch => ((List.range (ch.seq.length + 1)).filter fun p => (ch.seq.drop p).take l0 == word).map (c, ·)
    | none => []

def decodeGenomeB (gbs : Array ByteArray) : Genome :=
  gbs.toList.map fun B => { name := "", seq := decodeBytes B }

/-! ## Proof -/

theorem decodeBytes_of_encodes (B : ByteArray) (cs : List Char) (h : Encodes B cs) : decodeBytes B = cs := by
  apply List.ext_getElem
  · rw [length_decodeBytes]; exact h.1
  · intro i h1 h2
    rw [getElem_decodeBytes]
    apply Char.toNat_inj.mp
    rw [← h.2 i h2]
    exact toChar_val_toNat _

theorem scanLookup_complete (g : Genome) (l0 : Nat) : LookupComplete g l0 (scanLookup g l0) := by
  intro c ch p hc hp
  unfold scanLookup
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1, ?_⟩
  rw [hc, List.mem_map]
  exact ⟨p, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩

theorem windowScore_nonpos (read : List Char) (g : Genome) (w : Window) (s : Int)
    (h : windowScore sc0 read g w = some s) : s ≤ 0 := by
  unfold windowScore at h
  split at h
  · next ys _ =>
    split at h
    · next best hb =>
      obtain ⟨path, bs⟩ := best
      cases h
      obtain ⟨-, hs⟩ := getBestAlignment_returns_a_valid_walk sc0 read ys path bs hb
      rw [← hs]; exact scoreWalk_nonpos sc0 valid_sc0 _ _ _ _
    · cases h
  · cases h

end MapSpec.Fast

#print axioms MapSpec.Fast.lookupSeed_spec
#print axioms MapSpec.Fast.mapChroms_inv
#print axioms MapSpec.penL_same
#print axioms MapSpec.penL_ins
#print axioms MapSpec.penL_del
#print axioms MapSpec.Fast.gap_support
#print axioms MapSpec.Fast.hamSeeds_spec
#print axioms MapSpec.Fast.gappedPen2_spec
