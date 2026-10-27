import PairLadderF
import PairRegion

/-!
# Mode H: the region pipeline first, the cap ladder on what it leaves

`pairRegionKP` (codecs/PairRegion.lean) is `pairSpecT` (`pairRegionKP_mz_eq`): each mate's
unique best at its cap, kept when the two make a proper pair.  When it maps a pair
`(a, b)` that is also proper under `properPairU` (no dovetail beyond `sl`) and the
distance cost of its fragment is `0`, `(a, b)` is the pair-level answer too (`fastU_ok`:
each mate is at its strict minimum, so `pen a + pen b` is the unique least pair sum; for
`dcost0` the cost is always `0`).  Every other pair goes through the ladder (`ladderUF`).

    (pairUKH …).1 = pairSpecUT sc0 dc sl lo hi (−penOf R1) (−penOf R2) g m1 m2   (pairUKH_mz_eq)
    pairUKH … = (none, true) → PairTieOk …                                       (pairUKH_tie)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Mode H: `pairRegionKP`, accepted when proper under `properPairU` at distance cost `0`;
else the ladder (`a1`: mate 1 searched first at each rung). -/
def pairUKH {L Pp L2 Pp2 : Type} [LookG L Pp] [Inhabited Pp] [LookG L2 Pp2] [Inhabited Pp2]
    (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (ix : L) (rl : Nat → Nat → L2)
    (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option PairHit × Bool :=
  let lad := fun (_ : Unit) =>
    ladderUF dc sl lo hi (penOf R1) (penOf R2) (fun b c => hitsKPF ix G offs pgs (if b then R1 else R2) c) a1 caps
  match pairRegionKP lo hi ix rl G offs pgs R1 R2 with
  | some (a, b) => if properPairU sl lo hi a.1 b.1 && dc (fragLen a.1 b.1) == 0 then (some (a, b), true) else lad ()
  | none => lad ()

theorem penOf_le16 (R : ByteArray) : penOf R ≤ 16 := by
  unfold penOf; split <;> omega

theorem pairSpecT_some (T1 T2 : Int) (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (a b : Placement × Int)
    (h : pairSpecT T1 T2 lo hi g m1 m2 = some (a, b)) :
    mapSpecBoth sc0 T1 g m1 = some a ∧ mapSpecBoth sc0 T2 g m2 = some b := by
  unfold pairSpecT at h
  cases h1 : mapSpecBoth sc0 T1 g m1 <;> cases h2 : mapSpecBoth sc0 T2 g m2 <;> simp only [h1, h2] at h
  · cases h
  · cases h
  · cases h
  · next x y =>
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · cases h

section top
variable (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- The ladder alone, packed whole genome. -/
theorem ladderUF_kp_fst (P1 P2 : Nat) (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16) :
    (ladderUF dc sl lo hi P1 P2
      (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
      a1 caps).1 = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  rw [ladderUF_eq, ladderUR_fst]
  exact ladderU_eq dc sl lo hi P1 P2 g m1 m2
    (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c (by omega) x)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c (by omega) x) a1 caps

include hcut hg h1 h2 hchk in
theorem ladderUF_kp_snd (P1 P2 : Nat) (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16)
    (h : (ladderUF dc sl lo hi P1 P2
      (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
      a1 caps).2 = true) :
    ∃ w, w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2) := by
  rw [ladderUF_eq] at h
  exact ladderUR_snd dc sl lo hi P1 P2 g m1 m2
    (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c (by omega) x)
    (fun c hc x => hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c (by omega) x) a1 caps h

include hcut hg h1 h2 hchk in
/-- **Mode H, packed whole genome: the pair-level specification.** -/
theorem pairUKH_mz_eq :
    (pairUKH dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2).1 =
      pairSpecUT sc0 dc sl lo hi (-(penOf R1 : Int)) (-(penOf R2 : Int)) g m1 m2 := by
  have lad := ladderUF_kp_fst dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk
    (penOf R1) (penOf R2) (penOf_le16 R1) (penOf_le16 R2)
  have hr := pairRegionKP_mz_eq lo hi g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk
  unfold pairUKH
  rw [hr]
  split
  · next a b hab =>
    split
    · next hk =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨ha, hb⟩ := pairSpecT_some _ _ lo hi g m1 m2 a b hab
      exact (fastU_ok dc sl lo hi (penOf R1) (penOf R2) g m1 m2 a b ha hb hk.1 hk.2).symm
    · exact lad
  · exact lad

include hcut hg h1 h2 hchk in
/-- **Mode H: the answer kind `pairTie` is exact.** -/
theorem pairUKH_tie
    (h : pairUKH dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2 = (none, true)) :
    PairTieOk dc sl lo hi (-(penOf R1 : Int)) (-(penOf R2 : Int)) g m1 m2 := by
  have e := pairUKH_mz_eq dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk
  rw [h] at e
  refine ⟨e.symm, ?_⟩
  have snd := ladderUF_kp_snd dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk
    (penOf R1) (penOf R2) (penOf_le16 R1) (penOf_le16 R2)
  have hr := pairRegionKP_mz_eq lo hi g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk
  unfold pairUKH at h
  rw [hr] at h
  split at h
  · split at h
    · cases h
    · exact snd (by simpa using congrArg Prod.snd h)
  · exact snd (by simpa using congrArg Prod.snd h)

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pairUKH_mz_eq
#print axioms MapSpec.Fast.pairUKH_tie
