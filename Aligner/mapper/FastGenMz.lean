import FastMapperMz
import FastGen

/-!
# The general fast mapper through a minimizer index

`LookG` instance for `Mz.MzIdx`: the word at read offset `s` is looked up with its
prepared code and minimizer bucket (`mzPrep` of `seedHashAt R s`), or through the
index's runs when it has a letter other than ACGT.  `mzLookS_ok`: through an index
passing `Mz.check`, these are exactly the word's places (`LookOkS`), so

    GenomeBytes gbs g → Encodes R read → checkAllMz idxs gbs = true →
      mapFastTMz P gbs idxs R = mapSpec sc0 (-P) g read                (mapFastTMz_eq_mapSpec)
-/

namespace MapSpec.Fast

open MapSpec

/-- Places of the word at `R[s ..]` as `(p + base)·16`. -/
def mzLookS (ix : Mz.MzIdx) (G R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupP ix G R s p base 0 else lookupSeedA ix G R s base 0

instance : LookG Mz.MzIdx MzP := ⟨mzPrep, mzSize, mzLookS⟩

theorem mzLookS_eq (ix : Mz.MzIdx) (G R : ByteArray) (s base : Nat) :
    mzLookS ix G R s base (mzPrep ix (seedHashAt R s)) = (Mz.lookupSeed ix G R s).map (anc base 0) := by
  rw [seedHashAt_spec]
  split
  · next ha =>
    have e : ∀ y, mzLookS ix G R s base (mzPrep ix (some y)) = lookupCodeA ix G R s (unmix y) base 0 := fun y => by
      unfold mzLookS mzPrep lookupP lookupCodeA
      dsimp only
      rw [if_pos rfl]
    rw [e]
    unfold hashAt
    rw [unmix_mix _ (by rw [hashWord_toNat]; exact Nat.lt_of_lt_of_le (wN_lt R s q) (by decide)),
      hashWord_toNat, wN_eq, lookupCodeA_eq, Mz.lookupSeed_eq_lookupCode ix G R s
        (fun i hi => acgt_mz _ ((allACGT_word R s).1 ha i hi))]
    rfl
  · show lookupSeedA ix G R s base 0 = _
    rw [lookupA_eq]

theorem mzLookS_ok (ix : Mz.MzIdx) (G R : ByteArray) (s base : Nat) (hc : Mz.check ix G = true) :
    LookOkS G R s base 0 (mzLookS ix G R s base (mzPrep ix (seedHashAt R s))) := by
  have hf : anc base 0 = fun p => (p + base) * 16 + 0 := funext fun p => rfl
  unfold LookOkS
  rw [mzLookS_eq, hf, Array.toList_map]
  refine ⟨List.Pairwise.map _ (fun (a b : Nat) (hab : a < b) => show (a + base) * 16 + 0 < (b + base) * 16 + 0 by
    omega) (Mz.lookupSeed_sorted hc R s), fun e => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Mz.lookupSeed_mem hc R s p).1 hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Mz.lookupSeed_mem hc R s p).2 hp, rfl⟩

theorem lookAllG_mz (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (hchk : checkAllMz idxs gbs = true) :
    LookAllG gbs idxs := by
  intro c hc R s base _
  unfold checkAllMz at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact mzLookS_ok idxs[c]! gbs[c]! R s base (by rw [← Mz.check2_eq]; exact hchk c hc)

/-! ## One entry point: the tuned 100–103 bp path at `T = −12`, the general path otherwise -/

end MapSpec.Fast

