import AlignmentWfaU32Run2
import AlignmentWfaU32Level2
import AlignmentWfaU32Lattice
import AlignmentWfaU32LevelS
import AlignmentWfaU32

/-!
# `wfaAlignU2`: the second UInt32 kernel, proven

Chain: `uLoop2_some` (a level index the hot loop returns is the one the
proven offsets loop returns, via `uLevel2_some`), `uRun2_some` (same for the
run with divided penalties, `wfaRunOP`), `wfaRunO_lattice` (the corner level
of the original run is `g` times that), then the runtime certificate
(`checkRunsFast3` + the offsets identity) exactly as in `wfaAlignU`.
-/
namespace AlignmentSpec.U32Proof

theorem uLoop2_some (m n len margin pe po px : Nat) (xa ya : Array Char)
    (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30) (hlen : len = m + n + 1)
    (hxa : xa.size = m) (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size) :
    ∀ (fuel : Nat) (hist : List ULevel) (p : Nat) (trace : Array ULevel),
      (∀ lv ∈ hist, WF m margin lv) → ∀ (q : Nat) (tr : Array ULevel),
      uLoop2 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 m n pe po px
        fuel hist p trace = some (q, tr) →
      wfaLoopO m n xa.toList ya.toList len pe po px fuel (hist.map (udenL len margin)) p = some q := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro hist p trace hwf q tr h
    simp only [uLoop2] at h
    cases hl : uLevel2 len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32
        (frontAtU hist pe) (frontAtU hist po) (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px) with
    | none => rw [hl] at h; cases h
    | some lv =>
      rw [hl] at h
      simp only at h
      have hlv := uLevel2_some m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
        (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px)
        (frontAtU_wf m margin hist hwf pe) (frontAtU_wf m margin hist hwf po) (frontAtU_wf m margin hist hwf pe)
        (frontAtU_wf m margin hist hwf po) (frontAtU_wf m margin hist hwf px) hm hb (by omega) hxa hm32 hn32 lv hl
      subst hlv
      have hden := udenL_uLevel m n len margin pe po px xa ya hist hwf hm hb hlen hxa
      have wl : WF m margin (uLevel m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
          (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px)) :=
        wf_uLevel m n len margin xa ya _ _ _ _ _ (frontAtU_wf m margin hist hwf pe)
          (frontAtU_wf m margin hist hwf po) (frontAtU_wf m margin hist hwf pe)
          (frontAtU_wf m margin hist hwf po) (frontAtU_wf m margin hist hwf px) hm hb (by omega) hxa
      have hc : cornerU margin m n (uLevel m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
          (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px)) =
          cornerO m n (udenL len margin (uLevel m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
            (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px))) :=
        cornerU_eq_cornerO m n len margin _ wl hm (by omega) (by omega)
      simp only [wfaLoopO]
      rw [← hden, ← hc]
      split
      · rename_i hcor
        rw [if_pos hcor] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1]
      · rename_i hcor
        rw [if_neg hcor] at h
        rw [← List.map_cons, ← List.map_take]
        apply ih _ _ _ ?_ q tr h
        intro lv' hmem
        have := List.mem_of_mem_take hmem
        rcases List.mem_cons.mp this with h' | h'
        · rw [h']; exact wl
        · exact hwf lv' h'

theorem uRun2_some (xa ya : Array Char) (pe po px fuel : Nat) (hb : xa.size + ya.size + 2 < 2 ^ 30)
    (hm32 : xa.size.toUInt32.toNat = xa.size) (hn32 : ya.size.toUInt32.toNat = ya.size)
    (k : Nat) (hist : Array ULevel)
    (h : uRun2 xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32 hm32 hn32 pe po px fuel = some (k, hist)) :
    wfaRunOP xa.size ya.size xa.toList ya.toList pe po px fuel = some k := by
  unfold uRun2 at h
  unfold wfaRunOP
  simp only at h
  simp only
  have hseed := udenL_seedU xa.size ya.size (xa.size + ya.size + 1)
    (max pe (max po px) + 2) xa ya rfl (by omega) (by omega) rfl
  have ws := wf_seedU xa.size (max pe (max po px) + 2) xa ya rfl (by omega)
  have hc : cornerU (max pe (max po px) + 2) xa.size ya.size (seedU xa.size (max pe (max po px) + 2) xa ya) =
      cornerO xa.size ya.size (udenL (xa.size + ya.size + 1) (max pe (max po px) + 2)
        (seedU xa.size (max pe (max po px) + 2) xa ya)) :=
    cornerU_eq_cornerO xa.size ya.size (xa.size + ya.size + 1) (max pe (max po px) + 2) _ ws
      (by omega) (by omega) (by omega)
  rw [← hseed, ← hc]
  split
  · rename_i hcor
    rw [if_pos hcor] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  · rename_i hcor
    rw [if_neg hcor] at h
    have := uLoop2_some xa.size ya.size (xa.size + ya.size + 1) (max pe (max po px) + 2) pe po px xa ya
      (by omega) (by omega) rfl rfl hm32 hn32 fuel
      [seedU xa.size (max pe (max po px) + 2) xa ya] 1 _
      (by intro lv hl; simp only [List.mem_singleton] at hl; rw [hl]; exact ws) k hist h
    rw [List.map_cons, List.map_nil] at this
    exact this

-- ── the single-source path ──

theorem rget_eq_of_rdenF_eq (len : Nat) (f g : RFront) (h : rdenF len f = rdenF len g) (t : Nat)
    (ht : t < len) : rget f t = rget g t := by
  have h1 := bget_den len t (rtob f) ht
  have h2 := bget_den len t (rtob g) ht
  have hd : decodeR (rget f t) = decodeR (rget g t) := by
    rw [decodeR_rget, decodeR_rget]
    have hh : (bden len (rtob f))[t]? = (bden len (rtob g))[t]? := by
      show (rdenF len f)[t]? = (rdenF len g)[t]?
      rw [h]
    rw [h1, h2] at hh
    exact Option.some.inj hh
  unfold decodeR at hd
  by_cases hf : rget f t = 0 <;> by_cases hg : rget g t = 0
  · omega
  · rw [if_pos hf, if_neg hg] at hd; cases hd
  · rw [if_neg hf, if_pos hg] at hd; cases hd
  · rw [if_neg hf, if_neg hg] at hd
    have := Option.some.inj hd
    omega

theorem cornerU_of_mf (m n margin : Nat) (lv : ULevel) (R' : RLevel) (hb : m + 2 < 2 ^ 30)
    (hval : (uget margin lv (·.mf) n).toNat = rget R'.mf n) :
    cornerU margin m n lv = cornerR m n R' := by
  unfold cornerU cornerR
  rw [← hval]
  have hs : (m.toUInt32 + 1).toNat = m + 1 := by
    rw [UInt32.toNat_succ _ (by rw [toNat_toUInt32_of_lt m (by omega)]; omega),
      toNat_toUInt32_of_lt m (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [h, hs]
  · intro h; exact UInt32.toNat_inj.mp (by rw [h, hs])

theorem uLoopS_some (m n len margin : Nat) (xa ya : Array Char) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len = m + n + 1) (hxa : xa.size = m)
    (hm32 : m.toUInt32.toNat = xa.size) (hn32 : n.toUInt32.toNat = ya.size) :
    ∀ (fuel : Nat) (prev : ULevel) (R : RLevel) (p : Nat) (trace : Array ULevel),
      WFA m margin prev.w prev.mf →
      (∀ t, t < len → rget R.mf t = (uget margin prev (·.mf) t).toNat) →
      (∀ t, rget R.xf t ≤ rget R.mf t ∧ rget R.yf t ≤ rget R.mf t) →
      ∀ (q : Nat) (tr : Array ULevel),
      uLoopS len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 m n fuel prev p trace = some (q, tr) →
      wfaLoopO m n xa.toList ya.toList len 1 1 1 fuel [rdenL len R] p = some q := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro prev R p trace hw hR hinv q tr h
    simp only [uLoopS] at h
    cases hl : uLevelS len margin m.toUInt32 n.toUInt32 len.toUInt32 xa ya hm32 hn32 prev with
    | none => rw [hl] at h; cases h
    | some lv =>
      rw [hl] at h
      simp only at h
      obtain ⟨wlv, hval⟩ := uLevelS_some m n len margin xa ya prev R hw hR hinv hm hb hlen hxa hm32 hn32 lv hl
      have hden : nextLevelO m n xa.toList ya.toList len 1 1 1 [rdenL len R] =
          rdenL len (nextLevelR m n xa ya len 1 1 1 [R]) := by
        rw [rdenL_nextLevelR m n xa.toList ya.toList xa ya rfl rfl len 1 1 1 [R] hlen]; rfl
      have hc : cornerU margin m n lv = cornerO m n (rdenL len (nextLevelR m n xa ya len 1 1 1 [R])) := by
        rw [← cornerR_eq m n len (by omega)]
        exact cornerU_of_mf m n margin lv _ (by omega) (hval n (by omega))
      simp only [wfaLoopO]
      rw [hden, ← hc]
      split
      · rename_i hcor
        rw [if_pos hcor] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1]
      · rename_i hcor
        rw [if_neg hcor] at h
        have htake : (rdenL len (nextLevelR m n xa ya len 1 1 1 [R]) :: [rdenL len R]).take (max 1 (max 1 1)) =
            [rdenL len (nextLevelR m n xa ya len 1 1 1 [R])] := rfl
        rw [htake]
        exact ih lv _ (p + 1) _ wlv (fun t ht => (hval t ht).symm)
          (fun t => ⟨nextLevelR_xf_le_mf m n xa ya len 1 1 1 [R] t, nextLevelR_yf_le_mf m n xa ya len 1 1 1 [R] t⟩) q tr h

theorem uRunS_some (xa ya : Array Char) (fuel : Nat) (hb : xa.size + ya.size + 2 < 2 ^ 30)
    (hm32 : xa.size.toUInt32.toNat = xa.size) (hn32 : ya.size.toUInt32.toNat = ya.size)
    (k : Nat) (hist : Array ULevel)
    (h : uRunS xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32 hm32 hn32 fuel = some (k, hist)) :
    wfaRunOP xa.size ya.size xa.toList ya.toList 1 1 1 fuel = some k := by
  unfold uRunS at h
  unfold wfaRunOP
  simp only at h
  simp only
  have hseed := udenL_seedU xa.size ya.size (xa.size + ya.size + 1) 3 xa ya rfl (by omega) (by omega) rfl
  have ws := wf_seedU xa.size 3 xa ya rfl (by omega)
  have hc : cornerU 3 xa.size ya.size (seedU xa.size 3 xa ya) =
      cornerO xa.size ya.size (udenL (xa.size + ya.size + 1) 3 (seedU xa.size 3 xa ya)) :=
    cornerU_eq_cornerO xa.size ya.size (xa.size + ya.size + 1) 3 _ ws (by omega) (by omega) (by omega)
  rw [← hseed, ← hc]
  split
  · rename_i hcor
    rw [if_pos hcor] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  · rename_i hcor
    rw [if_neg hcor] at h
    have hRs : rdenL (xa.size + ya.size + 1) (seedR xa.size (xa.size + ya.size + 1) xa ya) =
        udenL (xa.size + ya.size + 1) 3 (seedU xa.size 3 xa ya) := by
      rw [hseed, rdenL_seedR xa.size _ xa.toList ya.toList xa ya rfl rfl (by omega)]
    rw [← hRs]
    have hmf : rdenF (xa.size + ya.size + 1) (seedR xa.size (xa.size + ya.size + 1) xa ya).mf =
        rdenF (xa.size + ya.size + 1) (toRF 3 (seedU xa.size 3 xa ya) (·.mf)) := by
      have := congrArg OLevelW.mf hRs
      simpa only [rdenL, udenL, toRLevel] using this
    apply uLoopS_some xa.size ya.size (xa.size + ya.size + 1) 3 xa ya (by omega) (by omega) rfl rfl hm32 hn32
      fuel (seedU xa.size 3 xa ya) (seedR xa.size (xa.size + ya.size + 1) xa ya) 1 _ ws.mf ?_ ?_ k hist h
    · intro t ht
      rw [rget_eq_of_rdenF_eq _ _ _ hmf t ht, rget_toRF xa.size 3 _ (fun x => x.mf) ws.mf (by omega)]
    · intro t
      exact ⟨seedR_xf_le_mf _ _ xa ya t, seedR_yf_le_mf _ _ xa ya t⟩

theorem uRunD_some (xa ya : Array Char) (pe po px fuel : Nat) (hb : xa.size + ya.size + 2 < 2 ^ 30)
    (hm32 : xa.size.toUInt32.toNat = xa.size) (hn32 : ya.size.toUInt32.toNat = ya.size)
    (k : Nat) (hist : Array ULevel)
    (h : uRunD xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32 hm32 hn32 pe po px fuel = some (k, hist)) :
    wfaRunOP xa.size ya.size xa.toList ya.toList pe po px fuel = some k := by
  unfold uRunD at h
  split at h
  · rename_i hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    subst h1 h2 h3
    exact uRunS_some xa ya fuel hb hm32 hn32 k hist h
  · exact uRun2_some xa ya pe po px fuel hb hm32 hn32 k hist h

theorem certifiedRunsU2_spec (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : certifiedRunsU2 sc xa ya = some (c, s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s ∧
    some s = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold certifiedRunsU2 at h
  simp only at h
  split at h
  · rename_i hg
    obtain ⟨hg', hb, hpo⟩ := hg
    cases hrun : uRunD xa.size ya.size xa ya xa.size.toUInt32 ya.size.toUInt32
        (toNat_toUInt32_of_lt xa.size (by omega)) (toNat_toUInt32_of_lt ya.size (by omega))
        ((wfaPe sc).toNat / gcdU (wfaPe sc).toNat (gcdU (wfaPo sc).toNat (wfaPx sc).toNat))
        ((wfaPo sc).toNat / gcdU (wfaPe sc).toNat (gcdU (wfaPo sc).toNat (wfaPx sc).toNat))
        ((wfaPx sc).toNat / gcdU (wfaPe sc).toNat (gcdU (wfaPo sc).toNat (wfaPx sc).toNat))
        ((xa.size + ya.size + 2) * ((wfaPo sc).toNat / gcdU (wfaPe sc).toNat (gcdU (wfaPo sc).toNat (wfaPx sc).toNat))) with
    | none => rw [hrun] at h; cases h
    | some r =>
      obtain ⟨k, hist⟩ := r
      rw [hrun] at h
      simp only at h
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
          obtain ⟨hr, hpe, hpx⟩ := wfaGate_spec sc hg'
          have hP' := uRunD_some xa ya _ _ _ _ hb _ _ k hist hrun
          rw [gcdU_eq, gcdU_eq] at hP'
          have hgpos : 0 < Nat.gcd (wfaPe sc).toNat (Nat.gcd (wfaPo sc).toNat (wfaPx sc).toNat) :=
            Nat.gcd_pos_of_pos_left _ (by omega)
          have hL := wfaRunO_lattice sc xa.toList ya.toList _ hgpos
            (Nat.gcd_dvd_left _ _)
            (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
            (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
            (by omega) hpo (by omega) k (by simpa only [Array.length_toList] using hP')
          rw [← gcdU_eq, ← gcdU_eq] at hL
          apply offsets_certify_score sc xa.toList ya.toList hg' _ hL
          simpa only [Array.length_toList, ← hs, beq_iff_eq] using hc
        · cases h
  · cases h

/-- The three kernel theorems and the function equality with `wfaAlign`. -/
theorem wfaAlignU2_score (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignU2 sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd := by
  unfold wfaAlignU2
  cases hc : compactSmall sc xa ya with
  | some r =>
    have h := wfaAlignHC_score sc xa ya
    simpa [wfaAlignHC, hc] using h
  | none =>
    cases hr : certifiedRunsU2 sc xa ya with
    | some r => exact (certifiedRunsU2_spec sc xa ya r.1 r.2 hr).2.2
    | none => exact wfaAlignK_score sc xa ya

theorem wfaAlignU2_sound (sc : Scoring) (xa ya : Array Char) (c : Array (Step × Nat)) (s : Int)
    (h : wfaAlignU2 sc xa ya = some (c, s)) :
    IsMonotoneWalk (expandCigar c) xa.toList ya.toList ∧
    walkScore sc xa.toList ya.toList (expandCigar c) = s := by
  unfold wfaAlignU2 at h
  cases hc : compactSmall sc xa ya with
  | some r =>
    apply wfaAlignHC_sound sc xa ya c s
    simpa [wfaAlignHC, hc] using h
  | none =>
    rw [hc] at h
    cases hr : certifiedRunsU2 sc xa ya with
    | some r =>
      rw [hr] at h
      cases h
      exact ⟨(certifiedRunsU2_spec sc xa ya c s hr).1, (certifiedRunsU2_spec sc xa ya c s hr).2.1⟩
    | none =>
      rw [hr] at h
      exact wfaAlignK_sound sc xa ya c s h

theorem wfaAlignU2_isSome (sc : Scoring) (xa ya : Array Char) : (wfaAlignU2 sc xa ya).isSome := by
  obtain ⟨best, hb⟩ := getBestAlignment_returns_some sc xa.toList ya.toList
  have h := wfaAlignU2_score sc xa ya
  rw [hb] at h
  cases hw : wfaAlignU2 sc xa ya with
  | none => rw [hw] at h; simp at h
  | some _ => rfl

theorem wfaAlignU2_score_eq_wfaAlign (sc : Scoring) (xa ya : Array Char) :
    (wfaAlignU2 sc xa ya).map Prod.snd = (wfaAlign sc xa.toList ya.toList).map Prod.snd := by
  rw [wfaAlignU2_score, wfaAlign_score]

theorem wfaAlignU2_score_fun_eq :
    (fun sc (xa ya : Array Char) => (wfaAlignU2 sc xa ya).map Prod.snd) =
      (fun sc (xa ya : Array Char) => (wfaAlign sc xa.toList ya.toList).map Prod.snd) := by
  funext sc xa ya; exact wfaAlignU2_score_eq_wfaAlign sc xa ya

end AlignmentSpec.U32Proof

namespace AlignmentSpec
export U32Proof (wfaAlignU2_score wfaAlignU2_sound wfaAlignU2_isSome wfaAlignU2_score_eq_wfaAlign
  wfaAlignU2_score_fun_eq certifiedRunsU2_spec)
end AlignmentSpec

#print axioms AlignmentSpec.U32Proof.wfaAlignU2_score
#print axioms AlignmentSpec.U32Proof.wfaAlignU2_sound
#print axioms AlignmentSpec.U32Proof.wfaAlignU2_isSome
#print axioms AlignmentSpec.U32Proof.wfaAlignU2_score_fun_eq
