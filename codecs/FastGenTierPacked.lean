import FastGenTier
import FastGenPairPacked

/-!
# Codec `pairTier1P`: the tier-1 pair mapper over a packed genome

`pairTier1` (codecs/FastGenTier.lean: cap from the read length) with the
chromosomes `PGen` views of one packed genome and the minimizer index bundled with
it (`PkMz`, codecs/FastGenPairPacked.lean); no byte genome at run time.

    cutOk G offs ns → Mz.check2P ix G → GenomeBytes ((cutAll G offs ns).map Mz.unpack) g → …
      pairTier1P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2
                                                                        (pairTier1P_mz_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

def mapTier1P (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (Placement × Int) :=
  match capOf R.size with
  | some P => decodeP pgs.size P (mapChromsGB P ix ByteArray.empty offs pgs R)
  | none => none

def pairTier1P (lo hi : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapTier1P ix offs pgs R1, mapTier1P ix offs pgs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem mapTier1P_eq (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapTier1P ix offs pgs R = mapTier1 ix (Mz.unpack ix.2) offs (pgs.map Mz.unpack) R := by
  unfold mapTier1P mapTier1
  cases capOf R.size with
  | none => rfl
  | some P =>
    simp only []
    rw [mapChromsGB_same (sameA_unpack pgs) sameG_default P ix (G := ByteArray.empty) (G' := Mz.unpack ix.2)
      (fun _ _ _ _ => rfl)]
    simp

/-- **Tier-1 pairs on a packed genome with one minimizer index.** -/
theorem pairTier1P_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairTier1P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 := by
  have e : pairTier1P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 =
      pairTier1 lo hi ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R1 R2 := by
    unfold pairTier1P pairTier1; rw [mapTier1P_eq, mapTier1P_eq]; rfl
  rw [e]
  refine pairTier1_eq lo hi g m1 m2 _ R1 R2 _ _ offs hg h1 h2 (catOk_cut G offs ns hcut) ?_
  intro R' s base hs
  show LookOkS (Mz.unpack G) R' s base 0 (mzLookSP ix G R' s base (mzPrep ix (seedHashAt R' s)))
  rw [mzLookSP_eq (Mz.rep_unpack G)]
  exact mzLookS_ok ix _ R' s base (by rw [← Mz.check2_eq, ← Mz.check2P_eq (Mz.rep_unpack G)]; exact hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.pairTier1P_mz_eq
