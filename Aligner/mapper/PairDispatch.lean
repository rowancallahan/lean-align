import FastGenPair
import FastGenK250

/-!
# Codec `pairDispatch`: each mate at a threshold set by its length

For trimmed 2×250 reads: a mate of ≥ 150 letters is mapped at `T = −16`, one of
100–149 letters at `T = −12` (both on the general fast path, `fastT`; never the
specification fallback of `mapFastGB`).  Shorter mates are left to the caller
(`dispatchOk` false).  The specification is `pairSpec` with one threshold per
mate (`pairSpecT`; the same as `pairSpec` when both mates have the same one).

    … → pairDispatch lo hi ix G offs gbs R1 R2 =
          pairSpecT (-(penOf R1)) (-(penOf R2)) lo hi g m1 m2       (pairDispatch_eq_pairSpecT)
    pairSpecT T T lo hi g m1 m2 = pairSpec sc0 T lo hi g m1 m2      (pairSpecT_same)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Penalty bound by mate length. -/
def penOf (R : ByteArray) : Nat := if 150 ≤ R.size then 16 else 12

/-- Each mate at its own threshold, then the proper-pair test. -/
def pairDispatch {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGB (penOf R1) ix G offs gbs R1, mapFastGB (penOf R2) ix G offs gbs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-- `pairSpec` with a threshold per mate. -/
def pairSpecT (T1 T2 : Int) (lo hi : Nat) (g : Genome) (m1 m2 : List Char) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapSpecBoth sc0 T1 g m1, mapSpecBoth sc0 T2 g m2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem pairDispatch_eq_pairSpecT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    pairDispatch lo hi ix G offs gbs R1 R2 = pairSpecT (-(penOf R1 : Int)) (-(penOf R2 : Int)) lo hi g m1 m2 := by
  unfold pairDispatch pairSpecT
  rw [mapFastGB_eq_mapSpecBoth _ g m1 gbs R1 ix G offs hg h1 hcat hlk,
    mapFastGB_eq_mapSpecBoth _ g m2 gbs R2 ix G offs hg h2 hcat hlk]

end MapSpec.Fast

