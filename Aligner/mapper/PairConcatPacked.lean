import PairConcat
import PairPacked

/-!
# Codec `pairFastCP`: one packed concatenated genome, one index

`pairFastC` (codecs/PairConcat.lean: one index over the concatenated genome `G`,
windows scored on each chromosome) with `G` a `PGen` and the chromosomes views
into it (`cutAll G offs ns`: chromosome `c` is `G[offs[c], offs[c] + ns[c])`,
sharing `G`'s arrays), so the genome is held once, at 2 bits per letter.

    … → pairFastCP lk lp lo hi ix G offs gbs R1 R2 = pairFastC lk lo hi ix G' offs gbs' R1 R2   (pairFastCP_eq)
    cutOk G offs ns → Mz.check2P ix G → GenomeBytes ((cutAll G offs ns).map Mz.unpack) g → …
      pairFastCP mzL mzLookP lo hi ix G offs (cutAll G offs ns) R1 R2 = pairSpec …    (pairFastCP_mz_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm (copies of `PairConcat` reading `PGen`s) -/

/-- Chromosome views: `c` is `G[offs[c], offs[c] + ns[c])`. -/
def cutAll (G : PGen) (offs ns : Array Nat) : Array PGen := (Array.range ns.size).map fun c => view G offs[c]! ns[c]!

/-- `G` is a whole packed genome and every chromosome lies inside it. -/
def cutOk (G : PGen) (offs ns : Array Nat) : Bool :=
  G.o == 0 && (List.range ns.size).all fun c => decide (offs[c]! + ns[c]! ≤ G.n)

/-! ## Proofs -/

section
variable {gbs : Array PGen} {gbsB : Array ByteArray} (hs : gbs.size = gbsB.size) (h : ∀ c : Nat, Rep gbs[c]! gbsB[c]!)
include hs h

variable {L Q : Type} [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q) {G : PGen} {GB : ByteArray}
  (hlp : ∀ ix R j p, lp ix G R j p = lk.look ix GB R j p)
include hlp

end

theorem cutAll_get (G : PGen) (offs ns : Array Nat) (c : Nat) (hc : c < ns.size) :
    (cutAll G offs ns)[c]! = view G offs[c]! ns[c]! := by
  simp [cutAll, hc]

/-- Every view spells its slice of the unpacked genome. -/
theorem catOk_cut (G : PGen) (offs ns : Array Nat) (hcut : cutOk G offs ns = true) :
    catOk (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) = true := by
  simp only [cutOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcut
  have hu : ∀ P : PGen, (Mz.unpack P).size = P.n := fun P => (Mz.rep_unpack P).1.symm
  have hg' : ∀ P : PGen, ∀ i, (Mz.unpack P).get! i = P.get i := fun P i => ((Mz.rep_unpack P).2 i).symm
  unfold catOk
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Array.size_map]
  intro c hc
  have hc' : c < ns.size := by simpa [cutAll] using hc
  rw [show ((cutAll G offs ns).map Mz.unpack)[c]! = Mz.unpack (view G offs[c]! ns[c]!) by
    simp [cutAll, hc']]
  refine ⟨by rw [hu, hu]; exact hcut.2 c hc', (eqRun_spec _ _ _ _ _).2 fun m hm => ?_⟩
  rw [hu] at hm
  rw [hg', hg']
  have hb := hcut.2 c hc'
  simp only [PGen.get, view, Nat.zero_add] at hm ⊢
  rw [if_pos (by omega), if_pos hm, Nat.add_assoc]
  rfl

end MapSpec.Fast

