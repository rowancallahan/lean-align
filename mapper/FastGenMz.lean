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

/-- Map one read at threshold `−P` through minimizer indexes. -/
def mapFastTMz (P : Nat) (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (R : ByteArray) : Option (Window × Int) :=
  mapFastTG P gbs idxs R

/-- **Minimizer indexes.** -/
theorem mapFastTMz_eq_mapSpec (P : Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hchk : checkAllMz idxs gbs = true) :
    mapFastTMz P gbs idxs R = mapSpec sc0 (-(P : Int)) g read :=
  mapFastTG_eq_mapSpec P g read gbs idxs R hg hr (lookAllG_mz gbs idxs hchk)

/-! ## One entry point: the tuned 100–103 bp path at `T = −12`, the general path otherwise -/

/-- Map one read at `T = −P` (hashed indexes). -/
def mapAuto (P : Nat) (gbs : Array ByteArray) (idxs : Array HIdx) (R : ByteArray) : Option (Window × Int) :=
  if P = 12 ∧ fastOk R = true then mapFast gbs idxs R else mapFastT P gbs idxs R

theorem mapAuto_eq_mapSpec (P : Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray)
    (idxs : Array HIdx) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hchk : checkAll idxs gbs = true) :
    mapAuto P gbs idxs R = mapSpec sc0 (-(P : Int)) g read := by
  unfold mapAuto
  split
  · next h => rw [mapFast_eq_mapSpec g read gbs idxs R hg hr hchk, h.1]; rfl
  · exact mapFastT_eq_mapSpec P g read gbs idxs R hg hr hchk

/-- Map one read at `T = −P` (minimizer indexes). -/
def mapAutoMz (P : Nat) (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (R : ByteArray) : Option (Window × Int) :=
  if P = 12 ∧ fastOk R = true then mapFastMz gbs idxs R else mapFastTMz P gbs idxs R

theorem mapAutoMz_eq_mapSpec (P : Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hchk : checkAllMz idxs gbs = true) :
    mapAutoMz P gbs idxs R = mapSpec sc0 (-(P : Int)) g read := by
  unfold mapAutoMz
  split
  · next h => rw [mapFastMz_eq_mapSpec g read gbs idxs R hg hr hchk, h.1]; rfl
  · exact mapFastTMz_eq_mapSpec P g read gbs idxs R hg hr hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastTMz_eq_mapSpec
#print axioms MapSpec.Fast.mapAuto_eq_mapSpec
#print axioms MapSpec.Fast.mapAutoMz_eq_mapSpec
