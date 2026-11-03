import FastGenCoverE
import FastGenPair

/-!
# Mate floors from seeds with no exact copy

The read is cut into `k + 1` blocks of `L = read.length / (k + 1)` letters.  If the first `l`
letters of block `j` occur nowhere in the genome, every window has an edit (mismatch 4, gap ≥ 8
with `sc0`) touching that block, and the event pigeonhole (`exists_clean_seed_amongE`, through
`coverLE`) turns `|J|` such blocks into a penalty of at least `4·|J|`:

    (∀ j ∈ J, block j's first l letters occur in no chromosome) →
      windowScore sc0 read g w = some s → 4·|J| ≤ −s                     (floor_absent)

`floor_look`: the same from lookups in one index over the concatenated genome (`catOk`) that
return no places (`LookOkS`), as the whole-genome mapper's seeds (`l = q = 25`, `L = n / m`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

theorem seedBoundE_sc0 (s : Int) : seedBoundE sc0 s = ((-s) / 4).toNat := by
  unfold seedBoundE sc0
  rfl

/-- **Floor from absent blocks.** -/
theorem floor_absent (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (l : Nat) (hl0 : 0 < l) (k : Nat) (hk : l ≤ read.length / (k + 1)) (hl2 : 2 ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k)
    (habs : ∀ j ∈ J, ∀ c p, c < gbs.size → ¬ MatchAtL gbs[c]! p R (j * (read.length / (k + 1))) l)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) :
    4 * (J.length : Int) ≤ -s := by
  have h0 := windowScore_nonpos read g w s hs
  refine Int.not_lt.mp fun hc => ?_
  have hJl : seedBoundE sc0 s < J.length := by
    rw [seedBoundE_sc0]
    have : (-s) / 4 < (J.length : Int) := by omega
    omega
  obtain ⟨j, hj, p, a, b, hcg, hm, -⟩ :=
    coverLE g read gbs R hg hr s l hl0 k hk hl2 J hJn hJk hJl w s hs (Int.le_refl _)
  exact habs j hj w.chr p hcg hm

/-- A lookup that returns no places: the seed occurs in no chromosome. -/
theorem absent_of_look (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)
    (hcat : catOk G offs gbs = true) (R : ByteArray) (s base : Nat) (a : Array Nat)
    (hl : LookOkS G R s base 0 a) (he : a = #[]) :
    ∀ c p, c < gbs.size → ¬ MatchAtL gbs[c]! p R s q := by
  intro c p hc hm
  obtain ⟨hfit, heq⟩ := catOk_spec G offs gbs hcat c hc
  have hM : MatchAt G (offs[c]! + p) R s :=
    ⟨by have := hm.1; omega, fun i hi => by
      rw [Nat.add_assoc, heq _ (by have := hm.1; omega)]; exact hm.2 i hi⟩
  have := (hl.2 ((offs[c]! + p + base) * 16 + 0)).mpr ⟨_, hM, rfl⟩
  rw [he] at this
  simp at this

/-- **Floor from empty lookups** (the whole-genome mapper's seeds: `m = n / 25` blocks of
`n / m` letters, a 25-letter seed at each block start). -/
theorem floor_look {L Pp : Type} [LookG L Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hm : 0 < read.length / 25)
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j < read.length / 25)
    (base : Nat → Nat)
    (hlk : ∀ j ∈ J, LookOkS G R (j * (read.length / (read.length / 25))) (base j) 0
      (LookG.look ix G R (j * (read.length / (read.length / 25))) (base j)
        (LookG.prep ix (seedHashAt R (j * (read.length / (read.length / 25)))))))
    (hempty : ∀ j ∈ J, LookG.look ix G R (j * (read.length / (read.length / 25))) (base j)
        (LookG.prep ix (seedHashAt R (j * (read.length / (read.length / 25))))) = #[])
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) :
    4 * (J.length : Int) ≤ -s := by
  have hk1 : read.length / 25 - 1 + 1 = read.length / 25 := by omega
  have hL : 25 ≤ read.length / (read.length / 25) := by
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  refine floor_absent g read gbs R hg hr q (by decide) (read.length / 25 - 1) (by rw [hk1]; exact hL)
    (by rw [hk1]; omega) J hJn (fun j hj => by have := hJk j hj; omega) (fun j hj => ?_) w s hs
  rw [hk1]
  exact absent_of_look G offs gbs hcat R _ (base j) _ (hlk j hj) (hempty j hj)

theorem gapBound_sc0_zero (S : Int) (hS : -8 < S) : gapBound sc0 S = 0 ∧ gapBound2 sc0 S = 0 := by
  unfold gapBound gapBound2 sc0
  exact ⟨Int.toNat_eq_zero.mpr (by simp only [Int.neg_neg]; omega),
    Int.toNat_eq_zero.mpr (by simp only [Int.neg_neg]; omega)⟩

end MapSpec.Fast

#print axioms MapSpec.Fast.floor_absent
#print axioms MapSpec.Fast.absent_of_look
#print axioms MapSpec.Fast.floor_look
