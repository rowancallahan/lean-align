import AlignmentWfaU32Run3
import AlignmentWfaU32Level3
import AlignmentWfaU32Loop3
import AlignmentWfaU32Kernel2

/-! Optimality of the executed block-layout run and the checked kernel. -/
namespace AlignmentSpec.U32Proof

theorem bwf_srcOf3 (m margin : Nat) (trace : Array BLevel)
    (hw : ∀ lv ∈ trace, BWF m margin lv) (p d : Nat) : BWF m margin (srcOf3 trace p d) := by
  rcases srcOf3_mem trace p d with he | he
  · rw [he]; exact bwf_empty m margin
  · exact hw _ he

theorem uLoop3_some (m n len margin pe po px : Nat) (xa ya : Array Char) (zeros : Array UInt32)
    (hz : ∀ i, zeros.getD i 0 = 0) (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30)
    (hlen : len = m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size)
    (hpe : 1 ≤ pe) (hpo : 1 ≤ po) (hpx : 1 ≤ px) :
    ∀ (fuel : Nat) (hist : List ULevel) (p : Nat) (trace : Array BLevel),
      (∀ lv ∈ hist, WF m margin lv) → (∀ lv ∈ trace, BWF m margin lv) → trace.size = p →
      (∀ d, 1 ≤ d → d ≤ max pe (max po px) → toU margin (srcOf3 trace p d) = frontAtU hist d) →
      ∀ (q : Nat) (tr : Array BLevel),
      uLoop3 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 m n pe po px zeros
        fuel p trace = some (q, tr) →
      wfaLoopO m n xa.toList ya.toList len pe po px fuel (hist.map (udenL len margin)) p = some q := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro hist p trace hwf hbw hp hrel q tr h
    simp only [uLoop3] at h
    cases hl : uLevel3 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 zeros
        (srcOf3 trace p pe) (srcOf3 trace p po) (srcOf3 trace p pe) (srcOf3 trace p po) (srcOf3 trace p px) with
    | none => rw [hl] at h; cases h
    | some lv =>
      rw [hl] at h
      simp only at h
      obtain ⟨he, wb⟩ := uLevel3_some m n len margin xa ya zeros _ _ _ _ _
        (bwf_srcOf3 m margin trace hbw p pe) (bwf_srcOf3 m margin trace hbw p po)
        (bwf_srcOf3 m margin trace hbw p pe) (bwf_srcOf3 m margin trace hbw p po)
        (bwf_srcOf3 m margin trace hbw p px) hz hm hb (by omega) hxa hm32 hn32 lv hl
      rw [hrel pe hpe (by omega), hrel po hpo (by omega), hrel px hpx (by omega)] at he
      have hd : udenL len margin (toU margin lv) =
          nextLevelO m n xa.toList ya.toList len pe po px (hist.map (udenL len margin)) := by
        rw [he]
        exact udenL_uLevel m n len margin pe po px xa ya hist hwf hm hb hlen hxa
      have hc : corner3 margin m n lv = cornerO m n (udenL len margin (toU margin lv)) := by
        rw [corner3_eq margin m n lv (by omega) wb.size wb.empty]
        exact cornerU_eq_cornerO m n len margin _ wb.view hm (by omega) (by omega)
      simp only [wfaLoopO]
      rw [← hd, ← hc]
      split
      · rename_i hcor
        rw [if_pos hcor] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1]
      · rename_i hcor
        rw [if_neg hcor] at h
        rw [← List.map_cons, ← List.map_take]
        apply ih _ _ _ ?_ ?_ ?_ ?_ q tr h
        · intro lv' hmem
          rcases List.mem_cons.mp (List.mem_of_mem_take hmem) with he | he
          · rw [he]; exact wb.view
          · exact hwf lv' he
        · intro lv' hmem
          rcases Array.mem_push.mp hmem with he | he
          · exact hbw lv' he
          · rw [he]; exact wb
        · rw [Array.size_push, hp]
        · exact srcRel_step margin _ trace hist p lv hp hrel

theorem bwf_seedB (m margin : Nat) (xa ya : Array Char) (hxa : xa.size = m)
    (hm : m + 2 < 2 ^ 30) : BWF m margin (seedB m margin xa ya) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toU_seedB]; exact wf_seedU m margin xa ya hxa hm
  · intro _
    unfold seedB
    simp only [Array.size_append, seedU_mf_size]
    change 1 + 2 * margin + (Array.replicate (2 * margin + 1) (0 : UInt32)).size +
      (Array.replicate (2 * margin + 1) (0 : UInt32)).size = _
    simp only [Array.size_replicate]
    omega
  · intro h; cases h

theorem uRun3_some (xa ya : Array Char) (pe po px fuel : Nat) (hb : xa.size + ya.size + 2 < 2 ^ 30)
    (hm32 : xa.size.toUInt32.toNat = xa.size) (hn32 : ya.size.toUInt32.toNat = ya.size)
    (hpe : 1 ≤ pe) (hpo : 1 ≤ po) (hpx : 1 ≤ px) (k : Nat) (hist : Array BLevel)
    (h : uRun3 xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32 hm32 hn32 pe po px fuel = some (k, hist)) :
    wfaRunOP xa.size ya.size xa.toList ya.toList pe po px fuel = some k := by
  unfold uRun3 at h
  unfold wfaRunOP
  simp only at h ⊢
  have ws := bwf_seedB xa.size (max pe (max po px) + 2) xa ya rfl (by omega)
  have hseed := udenL_seedU xa.size ya.size (xa.size + ya.size + 1)
    (max pe (max po px) + 2) xa ya rfl (by omega) (by omega) rfl
  have hc : corner3 (max pe (max po px) + 2) xa.size ya.size (seedB xa.size (max pe (max po px) + 2) xa ya) =
      cornerO xa.size ya.size (udenL (xa.size + ya.size + 1) (max pe (max po px) + 2)
        (seedU xa.size (max pe (max po px) + 2) xa ya)) := by
    rw [corner3_eq _ _ _ _ (by omega) ws.size ws.empty, toU_seedB]
    exact cornerU_eq_cornerO _ _ _ _ _ (by simpa only [toU_seedB] using ws.view)
      (by omega) (by omega) (by omega)
  rw [← hseed, ← hc]
  split
  · rename_i hcor
    rw [if_pos hcor] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  · rename_i hcor
    rw [if_neg hcor] at h
    have hp := uLoop3_some xa.size ya.size (xa.size + ya.size + 1) (max pe (max po px) + 2)
      pe po px xa ya _ (replicate_getD _) (by omega) hb rfl rfl hm32 hn32 hpe hpo hpx fuel
      [seedU xa.size (max pe (max po px) + 2) xa ya] 1 _
      (by intro lv hl; simp only [List.mem_singleton] at hl; rw [hl]; simpa only [toU_seedB] using ws.view)
      (by intro lv hl; simp only [Array.emptyWithCapacity_eq, Array.mem_push, Array.not_mem_empty, false_or] at hl; rw [hl]; exact ws)
      (by simp) (by
        intro d hd _
        have hr := srcRel_seed (max pe (max po px) + 2) (seedB xa.size (max pe (max po px) + 2) xa ya) d hd
        simpa [toU_seedB] using hr) k hist h
    simpa only [List.map_cons, List.map_nil] using hp

/-- Any accepted traceback has the optimum score when its corner level is
the reference run's level. The traceback generator itself is not trusted. -/
theorem acceptRuns_spec (sc : Scoring) (xa ya : Array Char) (L : Nat) (runs : List (Step × Nat))
    (hg : wfaGateB sc = true) (hL : wfaRunO sc xa.toList ya.toList = some L)
    (c : Array (Step × Nat)) (s : Int) (h : acceptRuns sc xa ya L runs = some (c, s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold acceptRuns at h
  split at h
  · cases h
  · rename_i score hcheck
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [checkRunsFast3_eq] at hcheck
      obtain ⟨hv, hs⟩ := checkRuns_sound sc xa ya _ score hcheck
      refine ⟨hv, hs, ?_⟩
      rw [← hs]
      apply offsets_certify_score sc xa.toList ya.toList hg _ hL
      simpa only [Array.length_toList, ← hs, beq_iff_eq] using hc
    · cases h

theorem certifiedRunsU3_spec (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : certifiedRunsU3 sc xa ya = some (c, s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold certifiedRunsU3 at h
  simp only at h
  split at h
  · rename_i hg
    obtain ⟨hg', hb, hpo⟩ := hg
    generalize hgdef : gcdU (wfaPe sc).toNat (gcdU (wfaPo sc).toNat (wfaPx sc).toNat) = g at h
    have heq : g = Nat.gcd (wfaPe sc).toNat (Nat.gcd (wfaPo sc).toNat (wfaPx sc).toNat) := by
      rw [← hgdef, gcdU_eq, gcdU_eq]
    obtain ⟨_, hpe, hpx⟩ := wfaGate_spec sc hg'
    have hgpos : 0 < g := by rw [heq]; exact Nat.gcd_pos_of_pos_left _ (by omega)
    have de : g ∣ (wfaPe sc).toNat := by rw [heq]; exact Nat.gcd_dvd_left _ _
    have do' : g ∣ (wfaPo sc).toNat := by
      rw [heq]; exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    have dx : g ∣ (wfaPx sc).toNat := by
      rw [heq]; exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    have pe1 : 1 ≤ (wfaPe sc).toNat / g := Nat.div_pos (Nat.le_of_dvd (by omega) de) hgpos
    have po1 : 1 ≤ (wfaPo sc).toNat / g := Nat.div_pos (Nat.le_of_dvd (by omega) do') hgpos
    have px1 : 1 ≤ (wfaPx sc).toNat / g := Nat.div_pos (Nat.le_of_dvd (by omega) dx) hgpos
    have certify (k : Nat)
        (hp : wfaRunOP xa.size ya.size xa.toList ya.toList ((wfaPe sc).toNat / g)
          ((wfaPo sc).toNat / g) ((wfaPx sc).toNat / g)
          ((xa.size + ya.size + 2) * ((wfaPo sc).toNat / g)) = some k)
        (runs : List (Step × Nat)) (ha : acceptRuns sc xa ya (g * k) runs = some (c, s)) :
        IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
        walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
        some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
      have hL := wfaRunO_lattice sc xa.toList ya.toList g hgpos de do' dx
        (by omega) hpo (by omega) k (by simpa only [Array.length_toList] using hp)
      exact acceptRuns_spec sc xa ya (g * k) runs hg' hL c s ha
    split at h
    · rename_i hsingle
      simp only [Bool.and_eq_true, beq_iff_eq] at hsingle
      cases hrun : uRunS xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32
          (toNat_toUInt32_of_lt xa.size (by omega)) (toNat_toUInt32_of_lt ya.size (by omega))
          ((xa.size + ya.size + 2) * ((wfaPo sc).toNat / g)) with
      | none => rw [hrun] at h; cases h
      | some r =>
        obtain ⟨k, hist⟩ := r
        rw [hrun] at h
        have hp := uRunS_some xa ya _ hb _ _ k hist hrun
        exact certify k (by simpa only [hsingle.1.1, hsingle.1.2, hsingle.2] using hp) _ h
    · cases hrun : uRun3 xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32
          (toNat_toUInt32_of_lt xa.size (by omega)) (toNat_toUInt32_of_lt ya.size (by omega))
          ((wfaPe sc).toNat / g) ((wfaPo sc).toNat / g) ((wfaPx sc).toNat / g)
          ((xa.size + ya.size + 2) * ((wfaPo sc).toNat / g)) with
      | none => rw [hrun] at h; cases h
      | some r =>
        obtain ⟨k, hist⟩ := r
        rw [hrun] at h
        exact certify k (uRun3_some xa ya _ _ _ _ hb _ _ pe1 po1 px1 k hist hrun) _ h
  · cases h

#print axioms uRun3_some
#print axioms certifiedRunsU3_spec
end AlignmentSpec.U32Proof

namespace AlignmentSpec
export U32Proof (certifiedRunsU3_spec)
end AlignmentSpec
