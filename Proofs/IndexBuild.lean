import Proofs.Pack
import Proofs.Aligner
import MzBuildP

/-! # The built minimizer index passes the router's check

`check3P_buildLoaded`: for a genome of fewer than `2^32` letters, the minimizer index
`buildLoaded` makes passes `Mz.check3P` on the packed genome it is bundled with (`indexOk`'s middle
conjunct). Both builders `buildMz` may take are covered: the packed one (`Mz.check3P_buildWP`,
`Aligner/index/packed_genome/MzBuildP.lean`) and the view one, whose view spells what the packed
genome spells when `catOkV` passes (`repV_of_catOkV`, with `Pack.packAll_spec`). The core is
`Mz.check_buildW` (`Aligner/index/minimizer/MzBuildOk.lean`). -/

set_option linter.deprecated false

namespace Spec.Index
open MapSpec MapSpec.Fast Spec.Pack

theorem ofChroms_n (gbs : Array ByteArray) : (GV.ofChroms gbs).n = (catL gbs.toList).length := by
  unfold GV.ofChroms
  simp only [Id.run, ← Array.forIn_toList, List.forIn_pure_yield_eq_foldl, pure_bind]
  show (List.foldl (fun b a => b.push (b.back! + a.size)) #[0] gbs.toList).back! = _
  suffices h : ∀ (L : List ByteArray) (st : Array Nat) (m : Nat), st.back! = m →
      (List.foldl (fun b a => b.push (b.back! + a.size)) st L).back! = m + (catL L).length by
    have := h gbs.toList #[0] 0 rfl; omega
  intro L
  induction L with
  | nil => intro st m h; simp [catL, h]
  | cons b r ih =>
    intro st m h
    rw [List.foldl_cons, ih _ (m + b.size) (by simp [h]), catL, List.length_append, dl_len]; omega


theorem catL_cover : ∀ (L : List ByteArray) (m i : Nat), i < (catL L).length →
    ∃ c, ∃ hc : c < L.length, (offL m L)[c]! - m ≤ i ∧ i < (offL m L)[c]! - m + L[c].size
  | [], _, i, h => by simp [catL] at h
  | b :: r, m, i, h => by
    rw [catL, List.length_append, dl_len] at h
    by_cases hi : i < b.size
    · exact ⟨0, by simp, by simp [offL], by simp [offL]; omega⟩
    · obtain ⟨c, hc, h1, h2⟩ := catL_cover r (m + b.size) (i - b.size) (by omega)
      have hge := (offL_spec r (m + b.size) c hc).1
      refine ⟨c + 1, by simp; omega, ?_, ?_⟩
      · simp only [offL, List.getElem!_cons_succ]; omega
      · simp only [offL, List.getElem!_cons_succ, List.getElem_cons_succ]; omega

theorem eqRunV_sound (V : GV) (b : ByteArray) : ∀ k i j, eqRunV V b i j k = true →
    ∀ t < k, V.get (i + t) = b.get! (j + t) := by
  intro k
  induction k with
  | zero => intro i j _ t ht; omega
  | succ k ih =>
    intro i j h t ht
    simp only [eqRunV, Bool.and_eq_true, beq_iff_eq] at h
    by_cases t0 : t = 0
    · subst t0; simpa using h.1
    · have := ih (i + 1) (j + 1) h.2 (t - 1) (by omega)
      rwa [show i + 1 + (t - 1) = i + t by omega, show j + 1 + (t - 1) = j + t by omega] at this

/-- When `catOkV` passes, the view of the chromosomes spells what the packed genome spells. -/
theorem repV_of_catOkV (g : GenomeFile) (hN : (catG g).length < 2 ^ 32)
    (hcat : catOkV (GV.ofChroms (g.map (·.2))) (offsOf (g.map (·.2))) (g.map (·.2)) = true) :
    RepV (GV.ofChroms (g.map (·.2))) (Mz.unpack (packAll (g.map (·.2)))) := by
  obtain ⟨hn, ho, hraw, -, -⟩ := packAll_spec g hN
  have hrep := Mz.rep_unpack (packAll (g.map (·.2)))
  have hVn : (GV.ofChroms (g.map (·.2))).n = (catG g).length := ofChroms_n _
  refine ⟨by rw [hVn, ← hrep.1, hn], fun i => ?_⟩
  rw [← hrep.2]
  generalize hV : GV.ofChroms (g.map (·.2)) = V at hVn hcat
  generalize hP : packAll (g.map (·.2)) = P at hn ho hraw
  by_cases hi : i < (catG g).length
  · have hget : P.get i = (catG g)[i]! := by
      unfold PGen.get; rw [if_pos (by omega), ho, Nat.zero_add]; exact (hraw i (by omega)).1
    have hcg' : catG g = catL (g.map (·.2)).toList := rfl
    rw [hget, hcg']
    rw [hcg'] at hi
    obtain ⟨c, hc, h1, h2⟩ := catL_cover (g.map (·.2)).toList 0 i hi
    have hcg : c < (g.map (·.2)).size := by simpa using hc
    obtain ⟨_, _, h3⟩ := offL_spec (g.map (·.2)).toList 0 c hc
    unfold catOkV at hcat
    rw [List.all_eq_true] at hcat
    have hc' := hcat c (List.mem_range.mpr hcg)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    have hoff : (offsOf (g.map (·.2)))[c]! = (offL 0 (g.map (·.2)).toList)[c]! := by rw [offsOf_eq]; simp
    have hgc : (g.map (·.2))[c]! = (g.map (·.2)).toList[c] := by rw [getElem!_pos _ c hcg]; simp
    rw [hoff, hgc] at hc'
    have := eqRunV_sound V _ _ _ _ hc'.2 (i - (offL 0 (g.map (·.2)).toList)[c]!) (by omega)
    rw [show (offL 0 (g.map (·.2)).toList)[c]! + (i - (offL 0 (g.map (·.2)).toList)[c]!) = i by omega,
      Nat.zero_add] at this
    rw [this, ← h3 _ (by omega)]
    congr 1; omega
  · have h1 : P.get i = 0 := by unfold PGen.get; rw [if_neg (by omega)]
    have h2 : V.get i = 0 := by unfold GV.get; rw [if_neg (by omega)]
    rw [h1, h2]

/-- **The built minimizer index passes the router's index check** (`indexOk`'s middle conjunct),
for any genome of fewer than `2^32` letters. -/
theorem check3P_buildMz (g : GenomeFile) (hN : (catG g).length < 2 ^ 32) :
    Mz.check3P (buildMz (g.map (·.2)) (packAll (g.map (·.2)))) (packAll (g.map (·.2))) 4 = true := by
  have hn := (packAll_spec g hN).1
  unfold buildMz
  dsimp only
  split
  · next hcat => exact Mz.check3P_buildWV _ _ (repV_of_catOkV g hN hcat) (by omega) 4
  · exact Mz.check3P_buildWP _ (by omega) 4

end Spec.Index

namespace Spec

theorem check3P_buildLoaded (g : GenomeFile) (hN : (Pack.catG g).length < 2 ^ 32) :
    MapSpec.Mz.check3P (buildLoaded g).1 (buildLoaded g).2.1 4 = true :=
  Index.check3P_buildMz g hN

end Spec

#print axioms Spec.check3P_buildLoaded
