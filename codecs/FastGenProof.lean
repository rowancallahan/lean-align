import FastGenAlgo
import FastGenCover
import FastGenCoverL
import FastGenCoverE

/-!
# Proof of the general fast mapper (part 1: windows)

`cwT P read g w`: the specification's penalty of window `w`, capped at `P`
(`P + 1` = not a hit).  The kernel computes it capped at `lim + 1`
(`cwT_ker`), the banded scorer exactly (`bandPen_eq`).  Adding a window keeps
`InvP` (`addK_inv`, `addB_inv`), and so do folds of adds (`foldl_invP`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- The specification's penalty of a window, capped at `P`. -/
def cwT (P : Nat) (read : List Char) (g : Genome) (w : Window) : Nat :=
  match windowScore sc0 read g w with
  | some s => if -(P : Int) ≤ s then (-s).toNat else P + 1
  | none => P + 1

section
variable (P : Nat) (read : List Char) (g : Genome)

theorem cwT_le (w : Window) : cwT P read g w ≤ P + 1 := by
  unfold cwT; split
  · split <;> omega
  · omega

/-- The penalty capped at `Pc ≤ P`. -/
theorem cwT_cap (Pc : Nat) (hPc : Pc ≤ P) (w : Window) :
    cwT Pc read g w = if cwT P read g w ≤ Pc then cwT P read g w else Pc + 1 := by
  unfold cwT
  cases windowScore sc0 read g w with
  | none => simp; omega
  | some s =>
    simp only []
    by_cases h1 : -(Pc : Int) ≤ s
    · have h2 : -(P : Int) ≤ s := by omega
      have h3 : (-s).toNat ≤ Pc := by omega
      simp only [h1, h2, h3, if_true]
    · by_cases h2 : -(P : Int) ≤ s
      · have h3 : ¬ (-s).toNat ≤ Pc := by omega
        simp only [h1, h2, h3, if_true, if_false]
      · have h3 : ¬ P + 1 ≤ Pc := by omega
        simp only [h1, h2, h3, if_false]

theorem cwT_iff (w : Window) (s : Int) :
    (windowScore sc0 read g w = some s ∧ -(P : Int) ≤ s) ↔ (cwT P read g w ≤ P ∧ s = -(cwT P read g w : Int)) := by
  unfold cwT
  cases h : windowScore sc0 read g w with
  | none =>
    simp only [reduceCtorEq, false_and, false_iff, not_and]
    intro h1; omega
  | some t =>
    have := windowScore_nonpos read g w t h
    simp only [Option.some.injEq]
    by_cases ht : -(P : Int) ≤ t
    · rw [if_pos ht]; constructor
      · rintro ⟨rfl, -⟩; omega
      · rintro ⟨-, e⟩; omega
    · rw [if_neg ht]; constructor
      · rintro ⟨rfl, h2⟩; omega
      · rintro ⟨h1, -⟩; omega

end

/-- The kernel on chromosome `c` is the capped penalty, capped again at `lim + 1`. -/
theorem cwT_ker (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (c st len lim : Nat) (hc : c < gbs.size)
    (h1 : lim ≤ P) (h2 : lim ≤ 15) :
    min (cwT P read g ⟨c, st, len⟩) (lim + 1) = kerG R gbs[c]! st len lim := by
  rw [kerG_eq _ _ _ _ _ h2]
  obtain ⟨hsz, henc⟩ := hg
  have hc' : c < g.length := by omega
  have he := henc c hc hc'
  rw [getElem!_pos gbs c hc]
  unfold cwT windowScore windowSeq
  simp only [List.getElem?_eq_getElem hc']
  by_cases hfit : st + len ≤ g[c].seq.length
  · rw [if_pos hfit, if_pos (by rw [he.1]; exact hfit)]
    simp only []
    rw [← penQ_window P lim h1 h2 R gbs[c] read g[c].seq hr he st len hfit]
    congr 1
    unfold penQ
    cases getBestAlignment sc0 read ((g[c].seq.drop st).take len) with
    | none => rfl
    | some x => obtain ⟨path, bs⟩ := x; rfl
  · rw [if_neg hfit, if_neg (by rw [he.1]; exact hfit)]
    simp only []; omega

/-- The banded scorer gives the capped penalty exactly. -/
theorem bandPen_eq (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (w : Window) :
    bandPen P R gbs w = cwT P read g w := by
  have hf := bandScore_faithful sc0 valid_sc0 (-(P : Int)) _ (bandOf_ok sc0 valid_sc0 (-(P : Int))) read g R gbs hr hg w
  unfold bandPen cwT
  cases hb : bandScore sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs w with
  | none =>
    cases hw : windowScore sc0 read g w with
    | none => rfl
    | some t =>
      simp only []
      split
      · next ht => have := (hf t).2 ⟨hw, ht⟩; rw [hb] at this; cases this.1
      · rfl
  | some s =>
    simp only []
    by_cases hs : -(P : Int) ≤ s
    · rw [if_pos hs, (hf s).1 ⟨hb, hs⟩ |>.1]; simp [hs]
    · rw [if_neg hs]
      cases hw : windowScore sc0 read g w with
      | none => rfl
      | some t =>
        simp only []
        split
        · next ht => have := (hf t).2 ⟨hw, ht⟩; rw [hb] at this; cases this.1; omega
        · rfl

/-- Capping at `P ≥ 16` and then at `17` is capping at `16`. -/
theorem cwT_cap16 (P : Nat) (hP : 16 ≤ P) (read : List Char) (g : Genome) (w : Window) :
    min (cwT P read g w) 17 = cwT 16 read g w := by
  unfold cwT
  cases windowScore sc0 read g w with
  | none => simp only []; omega
  | some s =>
    simp only []
    split <;> split <;> omega

/-- The penalty-16 kernel: `kerG` up to `15`; above, `filt16` (necessary for `16`)
and the banded kernel. -/
theorem cwT_ker16 (P : Nat) (hP : 16 ≤ P) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (c st len : Nat) (hc : c < gbs.size) :
    min (cwT P read g ⟨c, st, len⟩) 17 = ker16 R gbs c st len := by
  have hk := cwT_ker P read g gbs R hg hr c st len 15 hc (by omega) (by omega)
  unfold ker16; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
  dsimp only
  generalize kerG R gbs[c]! st len 15 = k at hk
  by_cases h15 : k ≤ 15
  · rw [if_pos h15]; omega
  rw [if_neg h15]
  have hcw : 16 ≤ cwT P read g ⟨c, st, len⟩ := by omega
  have hfitE : ∀ (h16 : cwT P read g ⟨c, st, len⟩ = 16 ∨ st + len ≤ gbs[c]!.size),
      ∃ (hc' : c < g.length), st + len ≤ g[c].seq.length ∧ Encodes gbs[c]! g[c].seq ∧
        cwT P read g ⟨c, st, len⟩ = penQ P read ((g[c].seq.drop st).take len) := by
    intro h16
    obtain ⟨hsz, henc⟩ := hg
    have hc' : c < g.length := by omega
    have he := henc c hc hc'
    rw [getElem!_pos gbs c hc] at h16 ⊢
    unfold cwT windowScore windowSeq
    unfold cwT windowScore windowSeq at h16
    simp only [List.getElem?_eq_getElem hc'] at h16 ⊢
    by_cases hfit : st + len ≤ g[c].seq.length
    · refine ⟨hc', hfit, he, ?_⟩
      rw [if_pos hfit]
      unfold penQ
      simp only []
      generalize getBestAlignment sc0 read (List.take len (List.drop st g[c].seq)) = r
      cases r with
      | none => rfl
      | some x => obtain ⟨path, bs⟩ := x; rfl
    · rw [if_neg hfit] at h16; simp only [] at h16
      rcases h16 with h16 | h16
      · omega
      · rw [he.1] at h16; omega
  split
  · next h4 =>
    obtain ⟨hc', hfit, he, heq⟩ := hfitE (Or.inr h4.1)
    obtain ⟨-, hl, hh⟩ := h4
    rw [hamming_spec _ _ st 4 R.size _ 0 0 rfl (Nat.zero_le _), Nat.zero_add] at hh
    subst hl
    have := pen_le_ham4 hr he P hP st hfit (by unfold preB; rw [Nat.sub_zero] at hh; omega)
    omega
  split
  · next h2 =>
    obtain ⟨hc', hfit, he, heq⟩ := hfitE (Or.inr h2.1)
    have := twoGapB_pen hr he P hP st len hfit h2.2
    omega
  split
  · rw [bandPen_eq 16 read g gbs R hg hr, cwT_cap16 P hP]
  · next hf =>
    have : cwT P read g ⟨c, st, len⟩ ≠ 16 := by
      intro h16
      apply hf
      obtain ⟨hc', hfit, he, heq⟩ := hfitE (Or.inl h16)
      rw [getElem!_pos gbs c hc] at he ⊢
      exact filt16_of hr he P hP st len hfit (by rw [← heq, h16])
    omega

/-- The kernel `kerH` is the capped penalty, capped again at `lim + 1` (`lim ≤ 16`). -/
theorem cwT_kerH (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (c st len lim : Nat) (hc : c < gbs.size)
    (h1 : lim ≤ P) (h2 : lim ≤ 16) :
    min (cwT P read g ⟨c, st, len⟩) (lim + 1) = kerH R gbs c st len lim := by
  unfold kerH
  split
  · exact cwT_ker P read g gbs R hg hr c st len lim hc h1 (by omega)
  · have : lim = 16 := by omega
    subst this
    exact cwT_ker16 P h1 read g gbs R hg hr c st len hc

/-! ## Monotonicity of the bounds -/

theorem sbound_def (x : Nat) : sbound x = seedBoundE sc0 (-(x : Int)) := by
  unfold sbound sbTbl; split
  · next h => simp [getElem!_pos, h]
  · rfl

theorem sbound_eq (x : Nat) : sbound x = x / 4 := by
  rw [sbound_def]; unfold seedBoundE sc0
  simp only [Int.neg_neg, show min (4 : Int) (min 6 (-2 * -2)) = 4 by decide, show (-(-6 : Int)) = 6 by decide,
    show (-(-4 : Int)) = 4 by decide]
  omega

theorem gapBound_eq (x : Nat) : gapBound sc0 (-(x : Int)) = (((x : Int) - 6) / 2).toNat := by
  unfold gapBound sc0; simp only [Int.neg_neg, show (-(-2 : Int)) = 2 by decide]; congr 2

theorem gapBound2_eq (x : Nat) : gapBound2 sc0 (-(x : Int)) = (((x : Int) - 12) / 2).toNat := by
  unfold gapBound2 sc0; simp only [Int.neg_neg, show (-(-2 : Int)) = 2 by decide]; congr 2

theorem sbound_mono (x y : Nat) (h : x ≤ y) : sbound x ≤ sbound y := by
  rw [sbound_eq, sbound_eq]; exact Nat.div_le_div_right h

theorem gapBound_mono (x y : Nat) (h : x ≤ y) : gapBound sc0 (-(x : Int)) ≤ gapBound sc0 (-(y : Int)) := by
  rw [gapBound_eq, gapBound_eq]; exact Int.toNat_le_toNat (by omega)

theorem gapBound2_mono (x y : Nat) (h : x ≤ y) : gapBound2 sc0 (-(x : Int)) ≤ gapBound2 sc0 (-(y : Int)) := by
  rw [gapBound2_eq, gapBound2_eq]; exact Int.toNat_le_toNat (by omega)

theorem shapeOk_mono (d d2 d' d2' : Nat) (a b : Int) (h1 : d ≤ d') (h2 : d2 ≤ d2') (h : shapeOk d d2 a b) :
    shapeOk d' d2' a b := by
  unfold shapeOk at *; omega

theorem shapesT_eq (x : Nat) : shapesT x = shapesAt x := by
  unfold shapesT shapesTbl; split
  · next h => simp [getElem!_pos, h]
  · rfl

theorem shapesKT_eq (x : Nat) : shapesKT x = (shapesAt x).filter (· != (0, 0)) := by
  unfold shapesKT shapesTbl; split
  · next h => simp [getElem!_pos, h]
  · rfl

theorem shapesAt_mem (x y : Nat) (h : x ≤ y) (a b : Int)
    (hs : shapeOk (gapBound sc0 (-(x : Int))) (gapBound2 sc0 (-(x : Int))) a b) : (a, b) ∈ shapesAt y := by
  unfold shapesAt
  rw [List.mem_mergeSort]
  exact mem_shapes _ _ a b (shapeOk_mono _ _ _ _ a b (gapBound_mono x y h) (gapBound2_mono x y h) hs)

/-! ## Adding windows -/

theorem add_pen_le (b : Best) (c st len r : Nat) : (b.add c st len r).pen ≤ b.pen := by
  unfold Best.add; split
  · dsimp only; omega
  · split <;> exact Nat.le_refl _

section adds
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read) (cw : Window → Nat) (hcw1 : ∀ w, cw w ≤ P + 1)

/-- The window `(st, len)` of chromosome `c`, when its penalty is `≤ lim`. -/
def KX (c lim : Nat) (st len : Int) (w : Window) : Prop :=
  0 ≤ st ∧ 0 ≤ len ∧ w = ⟨c, st.toNat, len.toNat⟩ ∧ cwT P read g w ≤ lim

def BX (c : Nat) (st len : Int) (w : Window) : Prop :=
  0 ≤ st ∧ 0 ≤ len ∧ w = ⟨c, st.toNat, len.toNat⟩

include hg hr hcw1

/-- `addK` adds the window when its penalty is `≤ min lim best`; a window between
`best` and `lim` cannot change the result, so it counts as added (`inv_skipP`). -/
theorem addK_inv (c lim : Nat) (hc : c < gbs.size)
    (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (h1 : lim ≤ P) (h2 : lim ≤ 16) (st len : Int)
    (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ KX P read g c lim st len w) (addK R gbs c lim st len b) := by
  unfold addK
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    split
    · next hw =>
      apply inv_skipP P cw hcw1 S _ b h
      rintro w ⟨-, -, rfl, -⟩
      right; right
      have e : (⟨c, st.toNat, len.toNat⟩ : Window) = b.win := by
        unfold Best.win; rw [hw.2.1, hw.2.2.1, hw.2.2.2]
      rw [e]; exact ⟨h.hit (by omega), Or.inr rfl⟩
    dsimp only
    have hm := cwT_kerH P read g gbs R hg hr c st.toNat len.toNat (min lim b.pen) hc (by omega) (by omega)
    by_cases hk : kerH R gbs c st.toNat len.toNat (min lim b.pen) ≤ min lim b.pen
    · rw [if_pos hk]
      have hex : kerH R gbs c st.toNat len.toNat (min lim b.pen) = cwT P read g ⟨c, st.toNat, len.toNat⟩ := by omega
      apply inv_congrP P _ _ _ _ (inv_addP P cw hcw1 S b h c st.toNat len.toNat _ (Or.inl (hex.trans (hcwc _ _).symm)))
      intro w; unfold KX; constructor
      · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl, by omega⟩
      · rintro (hw | ⟨-, -, rfl, -⟩); exact Or.inl hw; exact Or.inr rfl
    · rw [if_neg hk]
      apply inv_skipP P cw hcw1 S _ b h
      rintro w ⟨-, -, rfl, hw⟩; left; rw [hcwc]; omega
  · rw [if_neg hp]
    apply inv_congrP P _ _ _ _ h
    intro w; unfold KX; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨a, b', -⟩); exact hw; exact absurd ⟨a, b'⟩ hp

theorem addB_inv (c : Nat) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (st len : Int) (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ BX c st len w) (addB P R gbs c st len b) := by
  unfold addB
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    apply inv_congrP P _ _ _ _ (inv_addP P cw hcw1 S b h c st.toNat len.toNat _
      (Or.inl ((bandPen_eq P read g gbs R hg hr _).trans (hcwc _ _).symm)))
    intro w; unfold BX; constructor
    · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl⟩
    · rintro (hw | ⟨-, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
  · rw [if_neg hp]
    apply inv_congrP P _ _ _ _ h
    intro w; unfold BX; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨a, b', -⟩); exact hw; exact absurd ⟨a, b'⟩ hp

end adds

theorem addK_pen (R : ByteArray) (gbs : Array ByteArray) (c lim : Nat) (st len : Int) (b : Best) :
    (addK R gbs c lim st len b).pen ≤ b.pen := by
  unfold addK; split
  · split
    · exact Nat.le_refl _
    dsimp only; split
    · exact add_pen_le _ _ _ _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem addB_pen (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (st len : Int) (b : Best) :
    (addB P R gbs c st len b).pen ≤ b.pen := by
  unfold addB; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

/-! ## Stage K with shared profiles is stage K -/

theorem kerGP_eq (R G : ByteArray) (st len lim : Nat) :
    kerGP R G st len lim (fwdProf R G st) (bwdProf R G (st + len)) = kerG R G st len lim := by
  unfold kerGP kerG; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
  simp only [gappedPen2P_eq]

theorem kerHP_eq (R : ByteArray) (gbs : Array ByteArray) (c st len l : Nat) :
    kerHP R gbs c st len l (fwdProf R gbs[c]! st) (bwdProf R gbs[c]! (st + len)) = kerH R gbs c st len l := by
  unfold kerHP kerH ker16P ker16; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
  simp only [kerGP_eq, twoGapBP_eq, filt16P_eq]

theorem addKP_eq (R : ByteArray) (gbs : Array ByteArray) (c lim : Nat) (st len : Int) (pf pb : Nat × Nat × Nat)
    (b : Best) (hf : 0 ≤ st → pf = fwdProf R gbs[c]! st.toNat)
    (hb : 0 ≤ st → 0 ≤ len → pb = bwdProf R gbs[c]! (st.toNat + len.toNat)) :
    addKP R gbs c lim st len pf pb b = addK R gbs c lim st len b := by
  unfold addKP addK
  split
  · next h => split
              · rfl
              · rw [hf h.1, hb h.1 h.2]; simp only [kerHP_eq]
  · rfl

theorem shapeR_ge (shs : List (Int × Int)) :
    ∀ sh ∈ shs, sh.1.natAbs ≤ shapeR shs ∧ sh.2.natAbs ≤ shapeR shs := by
  have key : ∀ (l : List (Int × Int)) (m : Nat),
      m ≤ l.foldl (fun m sh => max m (max sh.1.natAbs sh.2.natAbs)) m ∧
      ∀ sh ∈ l, sh.1.natAbs ≤ l.foldl (fun m sh => max m (max sh.1.natAbs sh.2.natAbs)) m ∧
        sh.2.natAbs ≤ l.foldl (fun m sh => max m (max sh.1.natAbs sh.2.natAbs)) m := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons x l ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (max m (max x.1.natAbs x.2.natAbs))
      simp only [List.foldl_cons]
      refine ⟨by omega, fun sh hsh => ?_⟩
      rcases List.mem_cons.mp hsh with rfl | hsh
      · omega
      · exact h2 sh hsh
  exact (key shs 0).2

theorem foldl_ext_mem {α β : Type} (f g : β → α → β) (l : List α) (h : ∀ b, ∀ a ∈ l, f b a = g b a) :
    ∀ b, l.foldl f b = l.foldl g b := by
  induction l with
  | nil => intro b; rfl
  | cons a l ih =>
    intro b
    simp only [List.foldl_cons]
    rw [h b a List.mem_cons_self]
    exact ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) _

theorem stageKP_eq (R : ByteArray) (gbs : Array ByteArray) (c lim : Nat) (shs : List (Int × Int))
    (ds : List Nat) (b : Best) : stageKP R gbs c lim shs ds b = stageK R gbs c lim shs ds b := by
  unfold stageKP stageK
  simp only []
  have hr := shapeR_ge shs
  generalize shapeR shs = d at hr
  apply foldl_ext_mem
  intro b D _
  apply foldl_ext_mem
  intro b sh hsh
  obtain ⟨h1, h2⟩ := hr sh hsh
  apply addKP_eq
  · intro _
    rw [getElem!_pos _ _ (by simp; omega)]
    simp only [Array.getElem_map, Array.getElem_range]
    unfold dst; congr 2; omega
  · intro hs hl
    rw [getElem!_pos _ _ (by simp; omega)]
    simp only [Array.getElem_map, Array.getElem_range]
    unfold dst wlen at *
    congr 1; omega

theorem stageKP_fun : stageKP (Gt := ByteArray) = stageK := by
  funext R gbs c lim shs ds b; exact stageKP_eq R gbs c lim shs ds b

/-! ## Phase 1 and the stages -/

/-! ## Spoiled blocks and the pruned band kernel -/

/-- `sp` counts only blocks with no exact copy that a band cell of end `e` can reach. -/
def SpOk (read : List Char) (gs : List Char) (B : Nat) (sp : Nat → Bool) (e : Nat) : Prop :=
  ∀ j, sp j = true → 25 * j + 25 ≤ read.length → ∀ p, p ≤ e →
    ((((e - p : Nat) : Int) - ((read.length - 25 * j : Nat) : Int)).natAbs ≤ B) →
    ¬(p + 25 ≤ e ∧ ExactAt read gs (25 * j) (25 * j + 25) p)

theorem blockEq_of (R G : ByteArray) (a p : Nat) :
    ∀ k, k ≤ 25 → (∀ u, 25 - k ≤ u → u < 25 → R.get! (a + u) = G.get! (p + u)) → blockEq R G a p k = true := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro hk h
    unfold blockEq
    have e1 := h (25 - (k + 1)) (Nat.le_refl _) (by omega)
    rw [show a + (25 - (k + 1)) = a + 25 - (k + 1) by omega, show p + (25 - (k + 1)) = p + 25 - (k + 1) by omega] at e1
    simp only [GRead.get_bytes, e1, beq_self_eq_true, Bool.true_and]
    exact ih (by omega) (fun u h1 h2 => h u (by omega) h2)

theorem anyCopy_of (R G : ByteArray) (a : Nat) (lo : Int) :
    ∀ (t s : Nat), s < t → 0 ≤ lo + s → (lo + s).toNat + 25 ≤ G.size → blockEq R G a (lo + s).toNat 25 = true →
      anyCopy R G a lo t = true := by
  intro t
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
    intro s hs h0 h1 h2
    unfold anyCopy
    by_cases hst : s = t
    · subst hst
      simp only [GRead.size_bytes, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨h0, h1⟩, h2⟩
    · simp only [Bool.or_eq_true]
      exact Or.inr (ih s (by omega) h0 h1 h2)

theorem shiftMax_ge (bs : List Int) : ∀ bb ∈ bs, bb.natAbs ≤ shiftMax bs := by
  have key : ∀ (l : List Int) (m : Nat), m ≤ l.foldl (fun m bb => max m bb.natAbs) m ∧
      ∀ bb ∈ l, bb.natAbs ≤ l.foldl (fun m bb => max m bb.natAbs) m := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons x l ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (max m x.natAbs)
      refine ⟨by simp only [List.foldl_cons]; omega, fun bb hb => ?_⟩
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · exact h2 bb hb
  intro bb hb
  exact (key bs 0).2 bb hb

/-- The computed spoiled blocks of diagonal `D` are valid for every end `D + bb`, `|bb| ≤ d`. -/
theorem spoiled_ok (R : ByteArray) (read : List Char) (hr : Encodes R read) (G : ByteArray) (gs : List Char)
    (hG : Encodes G gs) (D d B : Nat) (bb : Int) (hbb : bb.natAbs ≤ d) (h0 : 0 ≤ (D : Int) + bb) :
    SpOk read gs B (fun j => (spoiledArr R G D d B)[j]?.getD false) ((D : Int) + bb).toNat := by
  intro j hj hjl p hp hband ⟨hpe, hex⟩
  dsimp only at hj
  have hn := hr.1
  have hjA : j < R.size / 25 := by
    apply Classical.byContradiction
    intro hc
    have : (spoiledArr R G D d B)[j]? = none := by
      unfold spoiledArr; simp; omega
    simp only [this, Option.getD_none] at hj
    cases hj
  have hA : (spoiledArr R G D d B)[j]? = some (!anyCopy R G (25 * j) ((D : Int) - d - R.size + (25 * j : Nat) - B)
      (2 * (d + B) + 1)) := by
    unfold spoiledArr; simp [hjA]
  rw [hA] at hj
  simp only [Option.getD_some, Bool.not_eq_true'] at hj
  -- the copy at `p` is one of the positions tried
  have hlen : ((read.drop (25 * j)).take (25 * j + 25 - 25 * j)).length = 25 := by simp; omega
  have hglen : p + 25 ≤ gs.length := by
    unfold ExactAt at hex
    rw [hex] at hlen; simp at hlen; omega
  have heq : ∀ u, u < 25 → R.get! (25 * j + u) = G.get! (p + u) := by
    intro u hu
    have h1 : ((read.drop (25 * j)).take (25 * j + 25 - 25 * j))[u]'(by rw [hlen]; exact hu) =
        ((gs.drop p).take (25 * j + 25 - 25 * j))[u]'(by rw [← hex, hlen]; exact hu) := by
      unfold ExactAt at hex; simp only [hex]
    simp only [List.getElem_take, List.getElem_drop] at h1
    apply UInt8.toNat_inj.mp
    rw [hr.2 (25 * j + u) (by omega), hG.2 (p + u) (by omega), h1]
  have hgs : G.size = gs.length := hG.1
  rw [anyCopy_of R G (25 * j) _ (2 * (d + B) + 1) (p - ((D : Int) - d - R.size + (25 * j : Nat) - B)).toNat
    (by omega) (by omega) (by omega) (by
      rw [show (((D : Int) - d - R.size + (25 * j : Nat) - B) + ((p - ((D : Int) - d - R.size + (25 * j : Nat) - B)).toNat : Int)).toNat = p by omega]
      exact blockEq_of R G (25 * j) p 25 (Nat.le_refl _) (fun u _ hu => heq u hu))] at hj
  cases hj

theorem SpOk.mono {read gs : List Char} {B B' : Nat} {sp : Nat → Bool} {e : Nat} (h : SpOk read gs B sp e)
    (hB : B' ≤ B) : SpOk read gs B' sp e :=
  fun j hj hjl p hp hband => h j hj hjl p hp (by omega)

theorem bandOf_mono (x y : Nat) (h : x ≤ y) : bandOf sc0 (-(x : Int)) ≤ bandOf sc0 (-(y : Int)) := by
  unfold bandOf sc0; exact Int.toNat_le_toNat (Int.ediv_le_ediv (by decide) (by omega))

theorem foldl_invP_mem_le {α : Type} (P : Nat) (cw : Window → Nat) (f : Best → α → Best) (X : α → Window → Prop)
    (l : List α) (m : Nat) (hpen : ∀ b a, (f b a).pen ≤ b.pen)
    (hstep : ∀ a ∈ l, ∀ S b, b.pen ≤ m → InvP P cw S b → InvP P cw (fun w => S w ∨ X a w) (f b a)) :
    ∀ S b, b.pen ≤ m → InvP P cw S b → InvP P cw (fun w => S w ∨ ∃ a ∈ l, X a w) (l.foldl f b) := by
  induction l with
  | nil => intro S b _ h; exact inv_congrP P cw _ _ b h (fun w => by simp)
  | cons a l ih =>
    intro S b hm h
    have := ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')) _ _
      (Nat.le_trans (hpen b a) hm) (hstep a List.mem_cons_self S b hm h)
    exact inv_congrP P cw _ _ _ this (fun w => by
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h1 | h2) | h3)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)
      · rintro (h1 | h2 | h3)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3)

/-- The pruned kernel gives the same capped penalty as the plain one. -/
theorem bandPenE_P (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (c st len : Nat) (hc : c < gbs.size) (sp : Nat → Bool)
    (hsp : ∀ (hc' : c < g.length), SpOk read g[c].seq (bandOf sc0 (-(P : Int))) sp (st + len))
    (cnt : Array Nat) (hcnt : ∀ i, i ≤ R.size → cnt[i / 25]! = blocksAbove sp i) :
    bandPenE P R.size len (decide (st + len ≤ gbs[c]!.size))
      (bandEndC (-(P : Int)) (bandOf sc0 (-(P : Int))) cnt R gbs[c]! (st + len)) =
    bandPenE P R.size len (decide (st + len ≤ gbs[c]!.size))
      (bandEnd2 sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs[c]! (st + len)) := by
  rw [bandEndC_eq _ _ cnt sp R gbs[c]! _ hcnt]
  unfold bandPenE
  by_cases hf : decide (st + len ≤ gbs[c]!.size) = true ∧ R.size ≤ len + bandOf sc0 (-(P : Int)) ∧
      len ≤ R.size + bandOf sc0 (-(P : Int))
  · rw [if_pos hf, if_pos hf]
    have hc' : c < g.length := by rw [← hg.1]; exact hc
    have henc : Encodes gbs[c]! g[c].seq := by rw [getElem!_pos gbs c hc]; exact hg.2 c hc hc'
    have he : st + len ≤ g[c].seq.length := by
      have := henc.1; simp only [decide_eq_true_eq] at hf; omega
    have hb := bandOf_ok sc0 valid_sc0 (-(P : Int))
    have h1 := bandEndP_spec (-(P : Int)) _ hb read g[c].seq (st + len) he R gbs[c]! hr henc sp (hsp hc')
    have h2 := bandEnd2_spec sc0 valid_sc0 (-(P : Int)) _ hb read g[c].seq (st + len) he R gbs[c]! hr henc
    have hn := hr.1
    generalize hk : len + bandOf sc0 (-(P : Int)) - R.size = k
    have hvk : Valid read.length (bandOf sc0 (-(P : Int))) (st + len) 0 k := by unfold Valid; omega
    have hkB : k < 2 * bandOf sc0 (-(P : Int)) + 1 := by omega
    revert h1 h2
    cases bandEndP (-(P : Int)) (bandOf sc0 (-(P : Int))) sp R gbs[c]! (st + len) <;>
      cases bandEnd2 sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs[c]! (st + len) <;> intro h1 h2
    · rfl
    · -- pruned dead, plain alive: the slot is below the cap
      rename_i A'
      have hd := (h1 (pOf read.length (bandOf sc0 (-(P : Int))) (st + len) 0 k) (by unfold pOf; omega)).1
      have hr2 := h2.2 k hkB hvk
      dsimp only
      rw [if_neg (fun hh => by have := hr2.2 hh; omega)]
    · rename_i A
      have hd := (h2 (pOf read.length (bandOf sc0 (-(P : Int))) (st + len) 0 k) (by unfold pOf; omega)).1
      have hr1 := h1.2 k hkB hvk
      dsimp only
      rw [if_neg (fun hh => by have := hr1.2 hh; omega)]
    · rename_i A A'
      have r1 := h1.2 k hkB hvk
      have r2 := h2.2 k hkB hvk
      dsimp only
      by_cases hA : -(P : Int) ≤ A[k + 1]!
      · have hv := r1.2 hA
        have hA' : -(P : Int) ≤ A'[k + 1]! := by
          have := r2.1 (by rw [← hv]; exact hA); rw [this, ← hv]; exact hA
        rw [if_pos hA, if_pos hA', r2.2 hA', ← hv]
      · rw [if_neg hA]
        have hv : cv sc0 read g[c].seq (st + len) none 0 (pOf read.length (bandOf sc0 (-(P : Int))) (st + len) 0 k) < -(P : Int) :=
          r1.below (by omega)
        rw [if_neg (fun hh => by have := r2.2 hh; omega)]
  · rw [if_neg hf, if_neg hf]

section chrom
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c Ls : Nat) (ps : Array Pp)
  (cw : Window → Nat) (hcw1 : ∀ w, cw w ≤ P + 1) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩)

/-- Anchor array of seed `j`. -/
def arrOf (j : Nat) : Array Nat := LookG.look ix gbs[c]! R (j * Ls) (R.size - j * Ls) ps[j]!

/-- The same-length window `phase1` adds for anchor `e`. -/
def GX (lim e : Nat) (w : Window) : Prop :=
  KX P read g c lim (((e / 16 : Nat) : Int) - (R.size : Int)) (R.size : Int) w

include hg hr

include hcw1 hcwc in
theorem phase1_spec (hc : c < gbs.size) :
    ∀ (ord J : List Nat) (acc : List (Array Nat)) (b : Best) (S : Window → Prop),
      InvP P cw S b →
      ∃ pre, pre <+: ord ∧
        (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.2 = pre.reverse ++ J ∧
        (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.1 =
          (pre.map (arrOf gbs R ix c Ls ps)).reverse ++ acc ∧
        (sbound (min (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).1.pen P) <
            (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.2.length ∨ pre = ord) ∧
        InvP P cw (fun w => S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
          GX P read g R c (min P 16) e w) (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).1 ∧
        (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).1.pen ≤ b.pen := by
  intro ord
  induction ord with
  | nil =>
    intro J acc b S h
    refine ⟨[], List.prefix_refl _, rfl, rfl, Or.inr rfl, inv_congrP P _ _ _ _ h (fun w => by simp), Nat.le_refl _⟩
  | cons j rest ih =>
    intro J acc b S h
    have hf := foldl_invP P cw
      (fun b e => addK R gbs c (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b)
      (fun e w => GX P read g R c (min P 16) e w)
      (fun e S b h => addK_inv P read g gbs R hg hr cw hcw1 c (min P 16) hc hcwc (Nat.min_le_left _ _)
        (Nat.min_le_right _ _) _ _ S b h)
      (arrOf gbs R ix c Ls ps j).toList S b h
    have hfp := foldl_pen (fun b e => addK R gbs c (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b)
      (fun b e => addK_pen _ _ _ _ _ _ b) (arrOf gbs R ix c Ls ps j).toList b
    rw [Array.foldl_toList] at hf hfp
    unfold phase1
    simp only []
    rw [show LookG.look ix gbs[c]! R (j * Ls) (R.size - j * Ls) ps[j]! = arrOf gbs R ix c Ls ps j from rfl]
    generalize hb1 : (arrOf gbs R ix c Ls ps j).foldl
      (fun b e => addK R gbs c (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b) b = b1
    rw [hb1] at hf hfp
    split
    · next hstop =>
      refine ⟨[j], List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩, rfl, rfl, Or.inl (by simpa using hstop.1),
        inv_congrP P _ _ _ _ hf (fun w => by simp), hfp⟩
    · obtain ⟨pre, hpre, h1, h2, h3, h4, h5⟩ := ih (j :: J) (arrOf gbs R ix c Ls ps j :: acc) b1 _ hf
      refine ⟨j :: pre, List.cons_prefix_cons.2 ⟨rfl, hpre⟩, by rw [h1]; simp, by rw [h2]; simp,
        ?_, inv_congrP P _ _ _ _ h4 (fun w => by simp [or_assoc]), Nat.le_trans h5 hfp⟩
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by rw [h3])

/-- The windows stage K looks at. -/
def StageK (lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (w : Window) : Prop :=
  ∃ D ∈ ds, ∃ sh ∈ shs, KX P read g c lim (dst R.size D sh) (wlen R.size sh) w

include hcw1 hcwc in
theorem stageK_spec (hc : c < gbs.size) (shs : List (Int × Int)) (ds : List Nat) (b : Best)
    (S : Window → Prop) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ StageK P read g R c (min P 16) shs ds w)
      (stageK R gbs c (min P 16) shs ds b) ∧ (stageK R gbs c (min P 16) shs ds b).pen ≤ b.pen := by
  have hsh : ∀ (D : Nat) S b, InvP P cw S b →
      InvP P cw (fun w => S w ∨ ∃ sh ∈ shs, KX P read g c (min P 16) (dst R.size D sh) (wlen R.size sh) w)
        (shs.foldl (fun b sh => addK R gbs c (min P 16) (dst R.size D sh) (wlen R.size sh) b) b) :=
    fun D => foldl_invP P cw _ (fun sh w => KX P read g c (min P 16) (dst R.size D sh) (wlen R.size sh) w)
      (fun sh S b h => addK_inv P read g gbs R hg hr cw hcw1 c (min P 16) hc hcwc (Nat.min_le_left _ _)
        (Nat.min_le_right _ _) _ _ S b h) shs
  have hp1 : ∀ (D : Nat) b, (shs.foldl (fun b sh => addK R gbs c (min P 16) (dst R.size D sh) (wlen R.size sh) b) b).pen
      ≤ b.pen :=
    fun D => foldl_pen _ (fun b sh => addK_pen _ _ _ _ _ _ b) shs
  unfold stageK
  exact ⟨inv_congrP P _ _ _ _ (foldl_invP P cw _ _ (fun D S b h => hsh D S b h) ds S b h)
    (fun w => by unfold StageK; rfl), foldl_pen _ (fun b D => hp1 D b) ds b⟩

theorem bandPenE_eq (c st len : Nat) (hc : c < gbs.size) :
    bandPenE P R.size len (decide (st + len ≤ gbs[c]!.size))
      (bandEnd2 sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs[c]! (st + len)) = bandPen P R gbs ⟨c, st, len⟩ := by
  unfold bandPenE bandPen bandScore; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
  simp only []
  rw [dif_pos hc, getElem!_pos gbs c hc]
  by_cases hf : st + len ≤ gbs[c].size ∧ R.size ≤ len + bandOf sc0 (-(P : Int)) ∧ len ≤ R.size + bandOf sc0 (-(P : Int))
  · rw [if_pos (by simpa using hf), if_pos hf]
    cases bandEnd2 sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs[c] (st + len) <;> rfl
  · rw [if_neg (by simpa using hf), if_neg hf]

/-- The windows the band stage scores. -/
def BW (c : Nat) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (w : Window) : Prop :=
  ∃ D ∈ ds, ∃ bb ∈ bs, 0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
    0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
    w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩

theorem addBS_pen (c D : Nat) (opt : Option (Array Int)) (b : Best) (sh : Int × Int) :
    (addBS P R gbs c D opt b sh).pen ≤ b.pen := by
  unfold addBS; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]; simp only []; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

theorem stageBD_pen (c : Nat) (shs : List (Int × Int)) (D : Nat) (cnt : Array Nat) (b : Best) (bb : Int) :
    (stageBD P R gbs c shs D cnt b bb).pen ≤ b.pen := by
  unfold stageBD; split
  · exact foldl_pen _ (fun b sh => addBS_pen P read g gbs R hg hr c D _ b sh) _ b
  · exact Nat.le_refl _

theorem stageB_pen (c : Nat) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (b : Best) :
    (stageB P R gbs c shs bs ds b).pen ≤ b.pen := by
  unfold stageB
  exact foldl_pen _ (fun b D => foldl_pen _ (fun b bb => stageBD_pen _ read g gbs R hg hr c shs D _ b bb) bs b) ds b

include hcw1 hcwc in
theorem addBS_spec (hc : c < gbs.size) (Pc : Nat) (hPc : Pc ≤ P) (D : Nat) (bb : Int) (sh : Int × Int)
    (hsb : sh.2 = bb) (sp : Nat → Bool)
    (hsp : 0 ≤ (D : Int) + bb → ∀ (hc' : c < g.length),
      SpOk read g[c].seq (bandOf sc0 (-(P : Int))) sp ((D : Int) + bb).toNat)
    (cnt : Array Nat) (hcnt : ∀ i, i ≤ R.size → cnt[i / 25]! = blocksAbove sp i) (S : Window → Prop)
    (b : Best) (hbP : Pc = P ∨ b.pen ≤ Pc) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ (0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (addBS Pc R gbs c D (bandEndAt Pc R gbs c D cnt bb) b sh) := by
  unfold addBS; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
  simp only []
  split
  · next hp =>
    have he : ((D : Int) + bb).toNat = ((D : Int) - R.size - sh.1).toNat + ((R.size : Int) + sh.1 + sh.2).toNat := by
      omega
    have hsp' := fun hc' => (hsp (by omega) hc').mono (bandOf_mono Pc P hPc)
    unfold bandEndAt
    rw [he] at hsp' ⊢
    rw [bandPenE_P Pc read g gbs R hg hr c _ _ hc sp hsp' cnt hcnt, bandPenE_eq Pc read g gbs R hg hr _ _ _ hc,
      bandPen_eq Pc read g gbs R hg hr, cwT_cap P read g Pc hPc]
    have hcw := hcwc ((D : Int) - R.size - sh.1).toNat ((R.size : Int) + sh.1 + sh.2).toNat
    have hle := h.le
    have hcwP := cwT_le P read g ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩
    refine inv_congrP P _ _ _ _ (inv_addP P cw hcw1 S b h c _ _ _ ?_) ?_
    · rw [hcw]
      split
      · exact Or.inl rfl
      · next hgt =>
        rcases hbP with hP | hb
        · subst hP; left; omega
        · right; omega
    · intro w; constructor
      · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl⟩
      · rintro (hw | ⟨-, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
  · next hp =>
    refine inv_congrP P _ _ _ _ h ?_
    intro w; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨h1, h2, -⟩); exact hw; exact absurd ⟨h1, h2⟩ hp

include hcw1 hcwc in
theorem stageBD_spec (hc : c < gbs.size) (Pc : Nat) (hPc : Pc ≤ P) (shs : List (Int × Int)) (D : Nat)
    (sp : Nat → Bool) (bb : Int)
    (hsp : 0 ≤ (D : Int) + bb → ∀ (hc' : c < g.length),
      SpOk read g[c].seq (bandOf sc0 (-(P : Int))) sp ((D : Int) + bb).toNat)
    (cnt : Array Nat) (hcnt : ∀ i, i ≤ R.size → cnt[i / 25]! = blocksAbove sp i) (S : Window → Prop)
    (b : Best) (hbP : Pc = P ∨ b.pen ≤ Pc) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (stageBD Pc R gbs c shs D cnt b bb) := by
  unfold stageBD
  split
  · next hD =>
    have hl := foldl_invP_mem_le P cw _ (fun (sh : Int × Int) w => sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩)
      (shs.filter (·.2 == bb)) (if Pc = P then P + 1 else Pc)
      (fun b sh => addBS_pen Pc read g gbs R hg hr c D _ b sh)
      (fun sh hsh S b hb h => by
        have hs2 : sh.2 = bb := by simpa using (List.mem_filter.1 hsh).2
        exact inv_congrP P _ _ _ _ (addBS_spec P read g gbs R hg hr c cw hcw1 hcwc hc Pc hPc D bb sh hs2 sp hsp cnt hcnt S b
          (by split at hb <;> omega) h)
          (fun w => by simp [hs2])) S b (by have := h.le; split <;> omega) h
    refine inv_congrP P _ _ _ _ hl (fun w => ?_)
    constructor
    · rintro (hw | ⟨sh, hsh, hx⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨hD, sh, (List.mem_filter.1 hsh).1, hx⟩
    · rintro (hw | ⟨-, sh, hsh, hx⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨sh, List.mem_filter.2 ⟨hsh, by simp [hx.1]⟩, hx⟩
  · next hD => exact inv_congrP P _ _ _ _ h (fun w => by simp [hD])

include hcw1 hcwc in
theorem stageB_spec (hc : c < gbs.size) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (b : Best)
    (S : Window → Prop) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ BW R c shs bs ds w) (stageB P R gbs c shs bs ds b) := by
  unfold stageB
  have hD : ∀ (D : Nat) S b, InvP P cw S b →
      InvP P cw (fun w => S w ∨ ∃ bb ∈ bs, (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
        (bs.foldl (fun b bb => stageBD (min b.pen P) R gbs c shs D
          (prefCnt (spoiledArr R gbs[c]! D (shiftMax bs) (bandOf sc0 (-(P : Int))))) b bb) b) :=
    fun D => foldl_invP_mem P cw _ _ bs (fun bb hbb S b h =>
      stageBD_spec P read g gbs R hg hr c cw hcw1 hcwc hc (min b.pen P) (Nat.min_le_right _ _) shs D _ bb
        (fun h0 hc' => spoiled_ok R read hr gbs[c]! g[c].seq
          (by rw [getElem!_pos gbs c hc]; exact hg.2 c hc hc') D (shiftMax bs) _ bb (shiftMax_ge bs bb hbb) h0)
        _ (prefCnt_get _ R.size (by unfold spoiledArr; simp))
        S b (by omega) h)
  exact inv_congrP P _ _ _ _ (foldl_invP P cw _ _ (fun D S b h => hD D S b h) ds S b h)
    (fun w => by unfold BW; rfl)

end chrom

/-! ## One chromosome -/

theorem le_div_seeds (n : Nat) (hm : 0 < n / 25) : 25 ≤ n / (n / 25) := by
  rw [Nat.le_div_iff_mul_le hm]
  have := Nat.div_mul_le_self n 25
  rw [Nat.mul_comm]; exact this

theorem seed_fits (n j : Nat) (hm : 0 < n / 25) (hj : j < n / 25) : j * (n / (n / 25)) + q ≤ n := by
  have hL := le_div_seeds n hm
  have hmL : n / 25 * (n / (n / 25)) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have : j * (n / (n / 25)) + n / (n / 25) ≤ n / 25 * (n / (n / 25)) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hq : q = 25 := rfl
  omega

section chrom2
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c : Nat) (ps : Array Pp) (ord : List Nat)
  (hc : c < gbs.size) (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25)
  (cw : Window → Nat) (hcw1 : ∀ w, cw w ≤ P + 1) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩)
  (hps : ∀ j, j < R.size / 25 → ps[j]! = LookG.prep ix (seedHashAt R (j * (R.size / (R.size / 25)))))
  (hlook : ∀ s base, s + q ≤ R.size →
    LookOkS gbs[c]! R s base 0 (LookG.look ix gbs[c]! R s base (LookG.prep ix (seedHashAt R s))))
  (hnd : ord.Nodup) (hlt : ∀ j ∈ ord, j < R.size / 25) (hlen : ord.length = R.size / 25)

include hg hr hc hm hsb hcw1 hcwc

omit hm hsb in
set_option maxHeartbeats 2000000 in
/-- **Stages K and B of one chromosome**, from any anchor arrays `arr j` of the
looked-up seeds `pre` (sorted, holding every exact seed place) whose same-length
windows are in `S1`, under the stop rule: afterwards every window of chromosome `c`
within penalty `min best P` was added (any seed count `m`, lookup length `l`). -/
theorem chromKB_coverL (m Ls l : Nat) (hm0 : 0 < m) (hsbm : sbound P < m) (hLs : R.size / m = Ls) (hL2 : 2 ≤ Ls)
    (hl0 : 0 < l) (hlL : l ≤ Ls) (arr : Nat → Array Nat)
    (hArr : ∀ j, j < m → (arr j).toList.Pairwise (· < ·) ∧
      ∀ p, MatchAtL gbs[c]! p R (j * Ls) l → (p + (R.size - j * Ls)) * 16 + 0 ∈ (arr j).toList)
    (pre : List Nat) (hpnd : pre.Nodup) (hpm : ∀ j ∈ pre, j < m)
    (S1 : Window → Prop) (b1 : Best) (hinv1 : InvP P cw S1 b1)
    (hS1 : ∀ j ∈ pre, ∀ e ∈ (arr j).toList, ∀ w, GX P read g R c (min P 16) e w → S1 w)
    (hstop : sbound (min b1.pen P) < pre.length ∨ pre.length = m) :
    ∃ S', InvP P cw S' (chromKB R gbs c P (pre.map arr).reverse b1) ∧ (∀ w, S1 w → S' w) ∧
      ∀ w, w.chr = c → cwT P read g w ≤ min (chromKB R gbs c P (pre.map arr).reverse b1).pen P → S' w := by
  have hn := hr.1
  have hmL : m * Ls ≤ R.size := by rw [← hLs]; exact Nat.div_mul_le_self _ _ |> fun h => by rw [Nat.mul_comm]; exact h
  generalize hacc0 : (pre.map arr).reverse = acc
  have hacc : acc = (pre.map arr).reverse := hacc0.symm
  obtain ⟨J, hJ⟩ : ∃ J, J = pre.reverse := ⟨_, rfl⟩
  unfold chromKB
  simp only [stageKP_fun, ite_self, shapesT_eq, shapesKT_eq]
  -- stage K
  generalize hQ1 : min b1.pen P = Q1
  generalize hshK : (shapesAt Q1).filter (· != (0, 0)) = shK
  generalize hdsK : diagsB acc (acc.length - sbound (min (min P 16) Q1)) (2 * gapBound sc0 (-(Q1 : Int))) = dsK
  have hK := stageK_spec P read g gbs R hg hr c cw hcw1 hcwc hc shK dsK b1 _ hinv1
  have h2 : InvP P cw (fun w => S1 w ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageK P read g R c (min P 16) shK dsK w))
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1) ∧
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1).pen ≤ b1.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hK.1 (fun w => by simp [hk]), hK.2⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ hinv1 (fun w => by simp [hk]), Nat.le_refl _⟩
  generalize hb2 : (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1) = b2 at h2
  -- stage B
  generalize hQ2 : min b2.pen P = Q2
  generalize hdsv : diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int))) = ds
  have hB := stageB_spec P read g gbs R hg hr c cw hcw1 hcwc hc (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 _ h2.1
  have hBp := stageB_pen P read g gbs R hg hr c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
  have h3 : InvP P cw (fun w => (S1 w ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageK P read g R c (min P 16) shK dsK w)) ∨
        (min P 16 < Q2 ∧ BW R c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds w))
      (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2) ∧
      (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2).pen
        ≤ b2.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hB (fun w => by simp [hk]), hBp⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ h2.1 (fun w => by simp [hk]), Nat.le_refl _⟩
  refine ⟨_, h3.1, fun w hw => Or.inl (Or.inl hw), ?_⟩
  generalize (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
    else b2) = bf at h3
  intro w hwc hcw
  generalize hx : cwT P read g w = x at hcw
  have hxP : x ≤ P := by omega
  have hxb : x ≤ bf.pen := by omega
  have hb21 := h2.2
  have hbf2 := h3.2
  have hx1 : x ≤ Q1 := by omega
  have hx2 : x ≤ Q2 := by omega
  -- the window scores `−x`
  have hws : windowScore sc0 read g w = some (-(x : Int)) := by
    have := (cwT_iff P read g w (-(cwT P read g w : Int))).2 ⟨by omega, rfl⟩
    rw [hx] at this; exact this.1
  -- the seeds looked up
  have hJn : J.Nodup := by rw [hJ]; exact (List.reverse_perm pre).nodup_iff.2 hpnd
  have hJm : ∀ j ∈ J, j < m := by
    intro j hj; rw [hJ, List.mem_reverse] at hj; exact hpm j hj
  rw [hQ1] at hstop
  have hJl : sbound x < J.length := by
    have := sbound_mono x Q1 hx1
    rcases hstop with h | h
    · rw [hJ, List.length_reverse]; omega
    · rw [hJ, List.length_reverse, h]
      have := sbound_mono Q1 P (by omega); omega
  obtain ⟨j, hj, p, a, bb, hcg, hmatch, hshape, ha1, ha2, hst, hwl⟩ :=
    coverLE g read gbs R hg hr (-(x : Int)) l hl0 (m - 1) (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
      (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
      J hJn (fun j hj => by have := hJm j hj; omega) (by rw [sbound_def] at hJl; omega) w (-(x : Int)) hws (Int.le_refl _)
  rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch ha1 hst
  rw [← hn] at hwl
  rw [hwc] at hmatch
  have hjm := hJm j hj
  have hjL : j * Ls + Ls ≤ R.size := by
    have : j * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  -- the anchor
  have hjpre : j ∈ pre := by rw [hJ, List.mem_reverse] at hj; exact hj
  have harr : arr j ∈ acc := by
    rw [hacc, List.mem_reverse]; exact List.mem_map_of_mem hjpre
  have he : (p + (R.size - j * Ls)) * 16 + 0 ∈ (arr j).toList := by
    exact (hArr j hjm).2 p hmatch
  generalize he' : (p + (R.size - j * Ls)) * 16 + 0 = e at he
  have he16 : e / 16 = p + (R.size - j * Ls) := by rw [← he']; omega
  have hwst : ∀ sh : Int × Int, sh.1 = a → wst R.size e sh = (p : Int) - (j * Ls : Nat) - a := by
    intro sh hsh; unfold wst; rw [he16, hsh]; push_cast; omega
  have hwlen : ∀ sh : Int × Int, sh.1 = a → sh.2 = bb → wlen R.size sh = (R.size : Int) + a + bb := by
    intro sh h1 h2; unfold wlen; rw [h1, h2]
  have hwin : w = ⟨c, ((p : Int) - (j * Ls : Nat) - a).toNat, ((R.size : Int) + a + bb).toNat⟩ := by
    cases w; simp only at hwc hst hwl; rw [hwc, hst, hwl, hn]
  -- seeds without a clean anchor near the window: at most `sbound x` of them
  have hsuppG : ∀ r, 2 * gapBound sc0 (-(x : Int)) ≤ r → acc.length - sbound x ≤ suppA acc (e / 16) r := by
    intro r hrx
    have hsa := hshape.1
    generalize hpred : (fun arr : Array Nat => anyNear arr (e / 16 - r) (e / 16 + r)) = pred
    have hsupp : suppA acc (e / 16) r = (pre.filter (pred ∘ arr)).length := by
      unfold suppA; rw [← hpred, hacc, List.filter_reverse, List.length_reverse, List.filter_map, List.length_map]
    rw [hsupp]
    have hcnt : ∀ (l : List Nat) (f : Nat → Bool),
        (l.filter f).length + (l.filter (fun x => !f x)).length = l.length := by
      intro l f; induction l with
      | nil => rfl
      | cons y l ih => by_cases hy : f y = true <;> simp [hy] <;> omega
    have hc2 := hcnt pre (pred ∘ arr)
    have hJ' : (pre.filter (fun j' => !(pred ∘ arr) j')).length ≤ sbound x := by
      apply Classical.byContradiction; intro hlt'
      have hsub := List.filter_sublist (p := fun j' => !(pred ∘ arr) j') (l := pre)
      obtain ⟨j', hj', p', a', bb', -, hmatch', hshape', ha1', -, hst', -⟩ :=
        coverLE g read gbs R hg hr (-(x : Int)) l hl0 (m - 1) (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
          (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
          _ (hsub.nodup hpnd)
          (fun j hj => by have := hpm j (hsub.subset hj); omega)
          (by rw [sbound_def] at hlt'; omega) w (-(x : Int)) hws (Int.le_refl _)
      rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch' ha1' hst'
      rw [hwc] at hmatch'
      have hj'pre := hsub.subset hj'
      have hj'm := hpm j' hj'pre
      have hj'L : j' * Ls + Ls ≤ R.size := by
        have : j' * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
        omega
      have he2 : (p' + (R.size - j' * Ls)) * 16 + 0 ∈ (arr j').toList := by
        exact (hArr j' hj'm).2 p' hmatch'
      have hsort : (arr j').toList.Pairwise (· < ·) := by
        exact (hArr j' hj'm).1
      have hpj : (pred ∘ arr) j' = true := by
        simp only [Function.comp, ← hpred]
        rw [anyNear_spec _ hsort]
        refine ⟨_, he2, ?_⟩
        have hsa' := hshape'.1
        have e1 : ((p' + (R.size - j' * Ls)) * 16 + 0) / 16 = p' + (R.size - j' * Ls) := by omega
        rw [e1, he16]
        omega
      have := (List.mem_filter.1 hj').2
      rw [hpj] at this; cases this
    have hal : acc.length = pre.length := by rw [hacc]; simp
    omega
  -- the band stage covers the windows above `lim`
  have hband : min P 16 < x → BW R c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds w := by
    intro hlx
    have hdx := gapBound_mono x Q2 hx2
    have hsa := hshape.1
    refine ⟨e / 16, ?_, bb, ?_, ?_, (a, bb), shapesAt_mem x Q2 hx2 a bb hshape, rfl, ?_, ?_, ?_⟩
    · -- the diagonal is one of the stage's: an anchor's, and supported
      rw [← hdsv]
      unfold diagsB diags
      rw [List.mem_filter, mem_dedupAdj, List.mem_mergeSort, List.mem_flatMap]
      refine ⟨⟨_, harr, List.mem_map.2 ⟨e, he, rfl⟩⟩, decide_eq_true ?_⟩
      have := hsuppG (2 * gapBound sc0 (-(Q2 : Int))) (by omega)
      have := sbound_mono x P hxP
      omega
    · unfold shifts
      rw [List.mem_mergeSort, List.mem_map]
      refine ⟨(bb + (gapBound sc0 (-(Q2 : Int)) : Int)).toNat, List.mem_range.2 (by omega), by omega⟩
    · rw [he16]; omega
    · rw [he16]; omega
    · omega
    · rw [hwin, he16]; congr 2; omega
  by_cases h00 : a = 0 ∧ bb = 0
  · -- the same-length window: phase 1, or the band stage
    obtain ⟨rfl, rfl⟩ := h00
    by_cases hxl : x ≤ min P 16
    · left; left
      apply hS1 j hjpre e he
      unfold GX KX
      rw [he16]
      have e1 : ((p + (R.size - j * Ls) : Nat) : Int) - (R.size : Int) = (p : Int) - (j * Ls : Nat) - 0 := by omega
      have e2 : (R.size : Int) = (R.size : Int) + 0 + 0 := by omega
      rw [e1]
      refine ⟨by omega, by omega, ?_, by rw [hx]; omega⟩
      rw [e2]; exact hwin
    · right; exact ⟨by omega, hband (by omega)⟩
  · -- a gapped shape: stage K, or the band stage
    have hab : 1 ≤ a.natAbs + bb.natAbs := by omega
    have hgb : 0 < gapBound sc0 (-(Q1 : Int)) := by
      have := gapBound_mono x Q1 hx1; have := hshape.1; omega
    by_cases hxl : x ≤ min P 16
    · left; right
      refine ⟨hgb, e / 16, ?_, (a, bb), ?_, ?_⟩
      · rw [← hdsK]
        unfold diagsB diags
        rw [List.mem_filter, mem_dedupAdj, List.mem_mergeSort, List.mem_flatMap]
        refine ⟨⟨_, harr, List.mem_map.2 ⟨e, he, rfl⟩⟩, decide_eq_true ?_⟩
        have := hsuppG (2 * gapBound sc0 (-(Q1 : Int))) (by have := gapBound_mono x Q1 hx1; omega)
        have := sbound_mono x (min (min P 16) Q1) (by omega)
        omega
      · rw [← hshK, List.mem_filter]
        refine ⟨shapesAt_mem x Q1 hx1 a bb hshape, ?_⟩
        simp only [bne_iff_ne, ne_eq, Prod.mk.injEq]; omega
      · have hd : dst R.size (e / 16) (a, bb) = (p : Int) - (j * Ls : Nat) - a := by
          unfold dst; rw [he16]; push_cast; omega
        rw [hd, hwlen (a, bb) rfl rfl]
        exact ⟨by omega, by omega, hwin, by rw [hx]; omega⟩
    · right; exact ⟨by omega, hband (by omega)⟩

set_option maxHeartbeats 2000000 in
/-- **Stages K and B of one chromosome**, from any anchor arrays `arr j` of the
looked-up seeds `pre` (sorted, holding every exact seed place) whose same-length
windows are in `S1`, under the stop rule: afterwards every window of chromosome `c`
within penalty `min best P` was added. -/
theorem chromKB_cover (arr : Nat → Array Nat)
    (hArr : ∀ j, j < R.size / 25 → (arr j).toList.Pairwise (· < ·) ∧
      ∀ p, MatchAt gbs[c]! p R (j * (R.size / (R.size / 25))) →
        (p + (R.size - j * (R.size / (R.size / 25)))) * 16 + 0 ∈ (arr j).toList)
    (pre : List Nat) (hpnd : pre.Nodup) (hpm : ∀ j ∈ pre, j < R.size / 25)
    (S1 : Window → Prop) (b1 : Best) (hinv1 : InvP P cw S1 b1)
    (hS1 : ∀ j ∈ pre, ∀ e ∈ (arr j).toList, ∀ w, GX P read g R c (min P 16) e w → S1 w)
    (hstop : sbound (min b1.pen P) < pre.length ∨ pre.length = R.size / 25) :
    ∃ S', InvP P cw S' (chromKB R gbs c P (pre.map arr).reverse b1) ∧ (∀ w, S1 w → S' w) ∧
      ∀ w, w.chr = c → cwT P read g w ≤ min (chromKB R gbs c P (pre.map arr).reverse b1).pen P → S' w :=
  chromKB_coverL P read g gbs R hg hr c hc cw hcw1 hcwc (R.size / 25) (R.size / (R.size / 25)) q hm hsb rfl
    (by have := le_div_seeds R.size hm; unfold q at this; omega)
    (by decide) (le_div_seeds _ hm) arr (fun j hj => ⟨(hArr j hj).1, fun p hp => (hArr j hj).2 p hp⟩)
    pre hpnd hpm S1 b1 hinv1 hS1 hstop

include hps hlook hnd hlt hlen in
/-- **One chromosome.**  After `chromG`, every window of chromosome `c` within
penalty `min best P` was added. -/
theorem chromG_cover (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    ∃ S', InvP P cw S' (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b) ∧
      (∀ w, S w → S' w) ∧
      ∀ w, w.chr = c → cwT P read g w ≤ min (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b).pen P →
        S' w := by
  obtain ⟨pre, hpre, hJ, hacc, hstop, hinv1, hpen1⟩ :=
    phase1_spec P read g gbs R hg hr ix c (R.size / (R.size / 25)) ps cw hcw1 hcwc hc ord [] [] b S h
  unfold chromG
  simp only []
  generalize phase1 ix R gbs c P (min P 16) (R.size / (R.size / 25)) ps ord [] [] b = r1 at *
  obtain ⟨b1, acc, J⟩ := r1
  simp only [List.append_nil] at hJ hacc hstop hinv1 hpen1 ⊢
  subst hacc
  have hpnd : pre.Nodup := hpre.sublist.nodup hnd
  obtain ⟨S', h1, h2, h3⟩ := chromKB_cover P read g gbs R hg hr c hc hm hsb cw hcw1 hcwc
    (arrOf gbs R ix c (R.size / (R.size / 25)) ps)
    (fun j hj => by
      unfold arrOf
      rw [hps j hj]
      have hfit := seed_fits R.size j hm hj
      exact ⟨(hlook _ _ hfit).1, fun p hp => ((hlook _ _ hfit).2 _).2 ⟨p, hp, rfl⟩⟩)
    pre hpnd (fun j hj => hlt j (hpre.sublist.subset hj)) _ b1 hinv1
    (fun j hj e he w hw => Or.inr ⟨j, hj, e, he, hw⟩)
    (by
      rcases hstop with h | h
      · left; rw [hJ, List.length_reverse] at h; exact h
      · right; rw [h, hlen])
  exact ⟨S', h1, fun w hw => h2 w (Or.inl hw), h3⟩

end chrom2

end MapSpec.Fast
