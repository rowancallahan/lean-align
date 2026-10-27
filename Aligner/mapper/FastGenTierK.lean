import FastGenTier
import FastGenK250

/-!
# Codec `pairTier1K`: the tier-1 pair mapper with the word kernels

`pairTier1` with `mapChromsGBK` (word kernels over the packed chromosomes `pvs`)
in place of `mapChromsGB` at cap 16.  Extra hypothesis: `checkPGs pvs gbs` (runtime check that
the packed chromosomes spell the byte ones).

    … → pairTier1K lo hi ix G offs gbs pvs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- One read at its tier-1 cap: word kernels at cap 16 (faster from 150 letters),
byte kernels at cap 12 (100–149 letters: the word kernels' read packing does not pay). -/
def mapTier1K {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Option (Placement × Int) :=
  match capOf R.size with
  | some P => decodeP gbs.size P
      (if P = 16 then mapChromsGBK P ix G offs gbs pvs R else mapChromsGB P ix G offs gbs R)
  | none => none

/-- A pair at the mates' tier-1 caps, word kernels. -/
def pairTier1K {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapTier1K ix G offs gbs pvs R1, mapTier1K ix G offs gbs pvs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem pairTier1K_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hpg : checkPGs pvs gbs = true)
    (R1 R2 : ByteArray) :
    pairTier1K lo hi ix G offs gbs pvs R1 R2 = pairTier1 lo hi ix G offs gbs R1 R2 := by
  have h : ∀ R, mapTier1K ix G offs gbs pvs R = mapTier1 ix G offs gbs R := fun R => by
    unfold mapTier1K mapTier1
    cases capOf R.size with
    | none => rfl
    | some P => simp only [mapChromsGBK_eq P ix G offs gbs pvs hpg, ite_self]
  unfold pairTier1K pairTier1
  rw [h, h]
  cases mapTier1 ix G offs gbs R1 <;> cases mapTier1 ix G offs gbs R2 <;> rfl

theorem pairTier1K_hashed_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairTier1K lo hi ix G offs gbs pvs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 := by
  rw [pairTier1K_eq lo hi ix G offs gbs pvs hpg]
  exact pairTier1_hashed_eq lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

theorem pairTier1K_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairTier1K lo hi ix G offs gbs pvs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 := by
  rw [pairTier1K_eq lo hi ix G offs gbs pvs hpg]
  exact pairTier1_mz_eq lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.pairTier1K_hashed_eq
#print axioms MapSpec.Fast.pairTier1K_mz_eq
