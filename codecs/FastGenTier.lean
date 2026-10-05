import FastGenPair
import PairSpecTier

/-!
# Codec `pairTier1`: the tier-1 pair mapper (cap from the read length)

Every read takes the proved indexed general path (`mapChromsGB`: one concatenated
index, both strands interleaved) at its own cap `capOf n` (`n ≥ 150` → `−16`,
`100 ≤ n < 150` → `−12`); shorter reads are not mapped.  The cap always leaves enough
25-letter seeds (`fastT`), so no slow path is ever taken.

    … → mapTier1 ix G offs gbs R = mapSpecTier1 sc0 g read                         (mapTier1_eq)
    … → pairTier1 lo hi ix G offs gbs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2      (pairTier1_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- One read at its tier-1 cap. -/
def mapTier1 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) : Option (Placement × Int) :=
  match capOf R.size with
  | some P => decodeP gbs.size P (mapChromsGB P ix G offs gbs R)
  | none => none

/-- A pair at the mates' tier-1 caps. -/
def pairTier1 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapTier1 ix G offs gbs R1, mapTier1 ix G offs gbs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem sbound_16 : sbound 16 = 5 := by rw [sbound_eq]; decide
theorem sbound_12 : sbound 12 = 3 := by rw [sbound_eq]; decide

/-- The cap leaves enough seeds for the indexed path. -/
theorem capOf_seeds (n P : Nat) (h : capOf n = some P) : 0 < n / 25 ∧ sbound P < n / 25 := by
  unfold capOf at h
  split at h
  · cases h; rw [sbound_16]; omega
  · split at h
    · cases h; rw [sbound_12]; omega
    · cases h

theorem mapTier1_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (g : Genome) (read : List Char)
    (gbs : Array ByteArray) (R : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    mapTier1 ix G offs gbs R = mapSpecTier1 sc0 g read := by
  unfold mapTier1 mapSpecTier1
  rw [← hr.1]
  cases hc : capOf R.size with
  | none => rfl
  | some P =>
    simp only []
    obtain ⟨hm, hsb⟩ := capOf_seeds R.size P hc
    obtain ⟨S, hi, hall⟩ := mapChromsGB_inv P read g gbs R hg hr ix G offs hcat hlk hm hsb
    rw [hg.1]
    exact decodeP_eq P g read S _ hi hall

/-- **The tier-1 pair mapper is the tier-1 pair specification.** -/
theorem pairTier1_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    pairTier1 lo hi ix G offs gbs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 := by
  unfold pairTier1 pairSpecTier1
  rw [mapTier1_eq g m1 gbs R1 ix G offs hg h1 hcat hlk, mapTier1_eq g m2 gbs R2 ix G offs hg h2 hcat hlk]
  cases mapSpecTier1 sc0 g m1 <;> cases mapSpecTier1 sc0 g m2 <;> rfl

theorem pairTier1_hashed_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) :
    pairTier1 lo hi ix G offs gbs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 :=
  pairTier1_eq lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_hashed G ix hchk)

theorem pairTier1_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) :
    pairTier1 lo hi ix G offs gbs R1 R2 = pairSpecTier1 sc0 lo hi g m1 m2 :=
  pairTier1_eq lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_mz G ix hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.pairTier1_hashed_eq
#print axioms MapSpec.Fast.pairTier1_mz_eq
