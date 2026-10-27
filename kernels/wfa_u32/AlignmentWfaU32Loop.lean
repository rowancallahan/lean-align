import AlignmentWfaU32Step
import AlignmentWfaOffLoop

/-!
# The padded UInt32 run equals the proven offsets-only run

`uLoop`/`uRun` execute the padded UInt32 levels (`uLevel`) with the same
history window and trace array as `wfaLoopR`; `uRun_eq` shows the corner
level they return is exactly the one `wfaRunO` (AlignmentWfaOffLoop.lean,
proven to determine the optimal score) returns.
-/
namespace AlignmentSpec.U32Proof

def udenL (len margin : Nat) (lv : ULevel) : OLevelW := rdenL len (toRLevel margin lv)

def uLoop (m n len margin : Nat) (xa ya : Array Char) (pe po px : Nat) :
    Nat → List ULevel → Nat → Array ULevel → Option (Nat × Array ULevel)
  | 0, _, _, _ => none
  | fuel + 1, hist, p, trace =>
      let lv := uLevel m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
        (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px)
      let trace := trace.push lv
      if cornerU margin m n lv then some (p, trace)
      else uLoop m n len margin xa ya pe po px fuel
        ((lv :: hist).take (max pe (max po px))) (p + 1) trace

theorem frontAtU_wf (m margin : Nat) (hist : List ULevel) (hwf : ∀ lv ∈ hist, WF m margin lv)
    (d : Nat) : WF m margin (frontAtU hist d) := by
  unfold frontAtU
  cases h : hist[d - 1]? with
  | none => exact wf_uEmpty m margin
  | some lv => exact hwf lv (List.mem_of_getElem? h)

/-- One executed level denotes the offsets-model level built from the denoted history. -/
theorem udenL_uLevel (m n len margin pe po px : Nat) (xa ya : Array Char) (hist : List ULevel)
    (hwf : ∀ lv ∈ hist, WF m margin lv) (hm : 1 ≤ margin) (hb : m + n + 2 < 2 ^ 30)
    (hlen : len = m + n + 1) (hxa : xa.size = m) :
    udenL len margin (uLevel m n len margin xa ya (frontAtU hist pe) (frontAtU hist po)
        (frontAtU hist pe) (frontAtU hist po) (frontAtU hist px)) =
      nextLevelO m n xa.toList ya.toList len pe po px (hist.map (udenL len margin)) := by
  have hmap : hist.map (udenL len margin) = (hist.map (toRLevel margin)).map (rdenL len) := by
    rw [List.map_map]; rfl
  rw [hmap, ← rdenL_nextLevelR m n xa.toList ya.toList xa ya rfl rfl len pe po px _ hlen]
  unfold udenL
  apply rdenL_toRLevel_uLevel m n len margin pe po px xa ya _ _ _ _ _ (hist.map (toRLevel margin))
  · exact frontAtR_map_toRLevel margin hist pe (·.xf) (·.xf) (fun _ => rfl) rfl
  · exact frontAtR_map_toRLevel margin hist po (·.mf) (·.mf) (fun _ => rfl) rfl
  · exact frontAtR_map_toRLevel margin hist po (·.mf) (·.mf) (fun _ => rfl) rfl
  · exact frontAtR_map_toRLevel margin hist pe (·.yf) (·.yf) (fun _ => rfl) rfl
  · exact frontAtR_map_toRLevel margin hist px (·.mf) (·.mf) (fun _ => rfl) rfl
  · exact frontAtU_wf m margin hist hwf pe
  · exact frontAtU_wf m margin hist hwf po
  · exact frontAtU_wf m margin hist hwf pe
  · exact frontAtU_wf m margin hist hwf po
  · exact frontAtU_wf m margin hist hwf px
  · exact hm
  · exact hb
  · omega
  · exact hxa

theorem uLoop_eq (m n len margin pe po px : Nat) (xa ya : Array Char) (hm : 1 ≤ margin)
    (hb : m + n + 2 < 2 ^ 30) (hlen : len = m + n + 1) (hxa : xa.size = m) :
    ∀ (fuel : Nat) (hist : List ULevel) (p : Nat) (trace : Array ULevel),
      (∀ lv ∈ hist, WF m margin lv) →
      (uLoop m n len margin xa ya pe po px fuel hist p trace).map Prod.fst =
        wfaLoopO m n xa.toList ya.toList len pe po px fuel (hist.map (udenL len margin)) p := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist p trace hwf
    have hlv := udenL_uLevel m n len margin pe po px xa ya hist hwf hm hb hlen hxa
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
    simp only [uLoop, wfaLoopO]
    rw [← hlv, ← hc]
    split
    · rfl
    · rw [ih _ _ _ ?_, List.map_take, List.map_cons]
      intro lv' hmem
      have := List.mem_of_mem_take hmem
      rcases List.mem_cons.mp this with h | h
      · rw [h]; exact wl
      · exact hwf lv' h

-- ── seed and run ──

def seedU (m margin : Nat) (xa ya : Array Char) : ULevel :=
  ⟨m, 1,
   pushZeros margin ((pushZeros margin (Array.emptyWithCapacity (2 * margin + 1))).push
     ((lcpArr xa ya 0 0).toUInt32 + 1)),
   Array.replicate (2 * margin + 1) 0, Array.replicate (2 * margin + 1) 0⟩

theorem seed_arr_spec (margin : Nat) (v : UInt32) :
    ((pushZeros margin (Array.emptyWithCapacity (2 * margin + 1) : Array UInt32)).push v).size = margin + 1 ∧
    ∀ i, ((pushZeros margin (Array.emptyWithCapacity (2 * margin + 1) : Array UInt32)).push v)[i]? =
      if i < margin then some 0 else if i < margin + 1 then some ((fun _ => v) (0 + (i - margin))) else none := by
  have h0 : (Array.emptyWithCapacity (2 * margin + 1) : Array UInt32).size = 0 := rfl
  have hs : (pushZeros margin (Array.emptyWithCapacity (2 * margin + 1) : Array UInt32)).size = margin := by
    rw [pushZeros_size, h0, Nat.zero_add]
  refine ⟨by rw [Array.size_push, hs], ?_⟩
  intro i
  rw [Array.getElem?_push, hs, pushZeros_getElem?, h0, Nat.zero_add]
  by_cases h1 : i < margin
  · rw [if_neg (by omega), if_neg (Nat.not_lt_zero i), if_pos h1, if_pos h1]
  · by_cases h2 : i = margin
    · rw [if_pos h2, if_neg h1, if_pos (by omega)]
    · rw [if_neg h2, if_neg (Nat.not_lt_zero i), if_neg h1, if_neg h1, if_neg (by omega)]

theorem wfa_replicate (m margin w : Nat) (hw : w ≤ 1) : WFA m margin w (Array.replicate (2 * margin + 1) 0) :=
  ⟨fun i h _ => by simp, fun _ => by simp; omega, fun i h => by simp⟩

theorem wf_seedU (m margin : Nat) (xa ya : Array Char) (hxa : xa.size = m) (hb : m + 2 < 2 ^ 30) :
    WF m margin (seedU m margin xa ya) := by
  obtain ⟨hs, hg⟩ := seed_arr_spec margin ((lcpArr xa ya 0 0).toUInt32 + 1)
  refine ⟨?_, wfa_replicate m margin 1 (by omega), wfa_replicate m margin 1 (by omega)⟩
  show WFA m margin 1 _
  apply wfa_padded m margin m 1 _ (fun _ => (lcpArr xa ya 0 0).toUInt32 + 1) hs
  · intro i; rw [hg i]
  · intro t _ _
    have hl : lcpArr xa ya 0 0 ≤ m := by have := lcpArr_le_sub xa ya 0 0; omega
    rw [UInt32.toNat_succ _ (by rw [toNat_toUInt32_of_lt _ (by omega)]; omega), toNat_toUInt32_of_lt _ (by omega)]
    exact Nat.succ_le_succ hl


theorem ugetA_replicate (margin lo k t : Nat) : ugetA margin lo (Array.replicate k (0 : UInt32)) t = 0 := by
  rw [ugetA_eq, Array.getElem?_replicate]
  split <;> rfl

theorem udenL_seedU (m n len margin : Nat) (xa ya : Array Char) (hxa : xa.size = m)
    (hb : m + 2 < 2 ^ 30) (hm : 1 ≤ margin) (hlen : len = m + n + 1) :
    udenL len margin (seedU m margin xa ya) = seedO m len xa.toList ya.toList := by
  have ws := wf_seedU m margin xa ya hxa hb
  rw [← rdenL_seedR m len xa.toList ya.toList xa ya rfl rfl (by omega)]
  unfold udenL
  simp only [rdenL, toRLevel, seedR]
  congr 1
  · apply rdenF_ext
    intro t ht
    rw [rget_toRF m margin _ (fun x => x.mf) ws.mf hm]
    simp only [uget, seedU]
    obtain ⟨hs, hg⟩ := seed_arr_spec margin ((lcpArr xa ya 0 0).toUInt32 + 1)
    rw [ugetA_padded margin m 1 _ (fun _ => (lcpArr xa ya 0 0).toUInt32 + 1) hs hg hm]
    unfold rget
    dsimp only
    have hl : lcpArr xa ya 0 0 ≤ m := by have := lcpArr_le_sub xa ya 0 0; omega
    by_cases h : m ≤ t ∧ t < m + 1
    · rw [if_pos h, if_neg (by omega)]
      have e : t - m = 0 := by omega
      rw [e]
      simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some]
      rw [UInt32.toNat_succ _ (by rw [toNat_toUInt32_of_lt _ (by omega)]; omega),
        toNat_toUInt32_of_lt _ (by omega)]
    · rw [if_neg h]
      by_cases h2 : t < m
      · rw [if_pos h2]; rfl
      · rw [if_neg h2, Array.getElem?_eq_none (by simp; omega)]; rfl
  · apply rdenF_ext
    intro t ht
    rw [rget_toRF m margin _ (fun x => x.xf) ws.xf hm]
    simp only [uget, seedU, ugetA_replicate, rget]
    simp
  · apply rdenF_ext
    intro t ht
    rw [rget_toRF m margin _ (fun x => x.yf) ws.yf hm]
    simp only [uget, seedU, ugetA_replicate, rget]
    simp

def uRun (m n : Nat) (xa ya : Array Char) (pe po px : Nat) : Option (Nat × Array ULevel) :=
  let len := m + n + 1
  let margin := max pe (max po px) + 2
  let lv := seedU m margin xa ya
  if cornerU margin m n lv then some (0, #[lv])
  else uLoop m n len margin xa ya pe po px ((m + n + 2) * po + 1) [lv] 1 #[lv]

/-- The executed UInt32 run returns the corner level of the proven offsets-only run. -/
theorem uRun_eq (sc : Scoring) (xa ya : Array Char) (hb : xa.size + ya.size + 2 < 2 ^ 30) :
    (uRun xa.size ya.size xa ya (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat).map Prod.fst =
      wfaRunO sc xa.toList ya.toList := by
  unfold uRun wfaRunO
  simp only [Array.length_toList]
  have hseed := udenL_seedU xa.size ya.size (xa.size + ya.size + 1)
    (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) xa ya rfl (by omega) (by omega) rfl
  have ws := wf_seedU xa.size (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) xa ya rfl (by omega)
  have hc : cornerU (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) xa.size ya.size
      (seedU xa.size (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) xa ya) =
      cornerO xa.size ya.size (udenL (xa.size + ya.size + 1)
        (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2)
        (seedU xa.size (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) xa ya)) :=
    cornerU_eq_cornerO xa.size ya.size (xa.size + ya.size + 1)
      (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat) + 2) _ ws (by omega) (by omega) (by omega)
  rw [← hseed, ← hc]
  split
  · rfl
  · rw [uLoop_eq xa.size ya.size (xa.size + ya.size + 1) _ _ _ _ xa ya (by omega) (by omega) rfl rfl _ _ _ _
      (by intro lv h; simp only [List.mem_singleton] at h; rw [h]; exact ws)]
    rw [List.map_cons, List.map_nil, hseed]

end AlignmentSpec.U32Proof
