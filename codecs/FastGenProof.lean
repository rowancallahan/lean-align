import FastGenAlgo
import FastGenCover

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

/-! ## Monotonicity of the bounds -/

theorem sbound_eq (x : Nat) : sbound x = max ((x : Int) / 4).toNat (((x : Int) - 6) / 2).toNat := by
  unfold sbound seedBound sc0
  simp only [Int.neg_neg, show min (4 : Int) (-(-6 + -2)) = 4 by decide, show min (4 : Int) 2 = 2 by decide,
    show (-(-2 : Int)) = 2 by decide, show (-(-4 : Int)) = 4 by decide]
  congr 2

theorem gapBound_eq (x : Nat) : gapBound sc0 (-(x : Int)) = (((x : Int) - 6) / 2).toNat := by
  unfold gapBound sc0; simp only [Int.neg_neg, show (-(-2 : Int)) = 2 by decide]; congr 2

theorem gapBound2_eq (x : Nat) : gapBound2 sc0 (-(x : Int)) = (((x : Int) - 12) / 2).toNat := by
  unfold gapBound2 sc0; simp only [Int.neg_neg, show (-(-2 : Int)) = 2 by decide]; congr 2

theorem sbound_mono (x y : Nat) (h : x ≤ y) : sbound x ≤ sbound y := by
  rw [sbound_eq, sbound_eq]
  have a : ((x : Int) / 4).toNat ≤ ((y : Int) / 4).toNat := Int.toNat_le_toNat (by omega)
  have b : (((x : Int) - 6) / 2).toNat ≤ (((y : Int) - 6) / 2).toNat := Int.toNat_le_toNat (by omega)
  omega

theorem gapBound_mono (x y : Nat) (h : x ≤ y) : gapBound sc0 (-(x : Int)) ≤ gapBound sc0 (-(y : Int)) := by
  rw [gapBound_eq, gapBound_eq]; exact Int.toNat_le_toNat (by omega)

theorem gapBound2_mono (x y : Nat) (h : x ≤ y) : gapBound2 sc0 (-(x : Int)) ≤ gapBound2 sc0 (-(y : Int)) := by
  rw [gapBound2_eq, gapBound2_eq]; exact Int.toNat_le_toNat (by omega)

theorem shapeOk_mono (d d2 d' d2' : Nat) (a b : Int) (h1 : d ≤ d') (h2 : d2 ≤ d2') (h : shapeOk d d2 a b) :
    shapeOk d' d2' a b := by
  unfold shapeOk at *; omega

theorem shapesAt_mem (x y : Nat) (h : x ≤ y) (a b : Int)
    (hs : shapeOk (gapBound sc0 (-(x : Int))) (gapBound2 sc0 (-(x : Int))) a b) : (a, b) ∈ shapesAt y :=
  mem_shapes _ _ a b (shapeOk_mono _ _ _ _ a b (gapBound_mono x y h) (gapBound2_mono x y h) hs)

/-! ## Adding windows -/

theorem add_pen_le (b : Best) (c st len r : Nat) : (b.add c st len r).pen ≤ b.pen := by
  unfold Best.add; split
  · dsimp only; omega
  · split <;> exact Nat.le_refl _

section adds
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)

/-- The window `addK` would add. -/
def KX (c lim : Nat) (st len : Int) (w : Window) : Prop :=
  0 ≤ st ∧ 0 ≤ len ∧ kerG R gbs[c]! st.toNat len.toNat lim ≤ lim ∧ w = ⟨c, st.toNat, len.toNat⟩

def BX (c : Nat) (st len : Int) (w : Window) : Prop :=
  0 ≤ st ∧ 0 ≤ len ∧ w = ⟨c, st.toNat, len.toNat⟩

include hg hr

theorem addK_inv (c lim : Nat) (hc : c < gbs.size) (h1 : lim ≤ P) (h2 : lim ≤ 15) (st len : Int)
    (S : Window → Prop) (b : Best) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ KX gbs R c lim st len w) (addK R gbs[c]! c lim st len b) := by
  unfold addK
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    dsimp only
    by_cases hk : kerG R gbs[c]! st.toNat len.toNat lim ≤ lim
    · rw [if_pos hk]
      have hm := cwT_ker P read g gbs R hg hr c st.toNat len.toNat lim hc h1 h2
      have hex : kerG R gbs[c]! st.toNat len.toNat lim = cwT P read g ⟨c, st.toNat, len.toNat⟩ := by omega
      apply inv_congrP P _ _ _ _ (inv_addP P (cwT P read g) (cwT_le P read g) S b h c st.toNat len.toNat _ (Or.inl hex))
      intro w; unfold KX; constructor
      · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, hk, rfl⟩
      · rintro (hw | ⟨-, -, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
    · rw [if_neg hk]
      apply inv_congrP P _ _ _ _ h
      intro w; unfold KX; constructor
      · intro hw; exact Or.inl hw
      · rintro (hw | ⟨-, -, hk', -⟩); exact hw; exact absurd hk' hk
  · rw [if_neg hp]
    apply inv_congrP P _ _ _ _ h
    intro w; unfold KX; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨a, b', -⟩); exact hw; exact absurd ⟨a, b'⟩ hp

theorem addB_inv (c : Nat) (st len : Int) (S : Window → Prop) (b : Best) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ BX c st len w) (addB P R gbs c st len b) := by
  unfold addB
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    apply inv_congrP P _ _ _ _ (inv_addP P (cwT P read g) (cwT_le P read g) S b h c st.toNat len.toNat _
      (Or.inl (bandPen_eq P read g gbs R hg hr _)))
    intro w; unfold BX; constructor
    · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl⟩
    · rintro (hw | ⟨-, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
  · rw [if_neg hp]
    apply inv_congrP P _ _ _ _ h
    intro w; unfold BX; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨a, b', -⟩); exact hw; exact absurd ⟨a, b'⟩ hp

end adds

theorem addK_pen (R G : ByteArray) (c lim : Nat) (st len : Int) (b : Best) : (addK R G c lim st len b).pen ≤ b.pen := by
  unfold addK; split
  · dsimp only; split
    · exact add_pen_le _ _ _ _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem addB_pen (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (st len : Int) (b : Best) :
    (addB P R gbs c st len b).pen ≤ b.pen := by
  unfold addB; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

/-! ## Phase 1 and the stages -/

section chrom
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c Ls : Nat) (ps : Array Pp)

/-- Anchor array of seed `j`. -/
def arrOf (j : Nat) : Array Nat := LookG.look ix gbs[c]! R (j * Ls) (R.size - j * Ls) ps[j]!

/-- The same-length window `phase1` adds for anchor `e`. -/
def GX (lim e : Nat) (w : Window) : Prop :=
  KX gbs R c lim (((e / 16 : Nat) : Int) - (R.size : Int)) (R.size : Int) w

include hg hr

theorem phase1_spec (hc : c < gbs.size) :
    ∀ (ord J : List Nat) (acc : List (Array Nat)) (b : Best) (S : Window → Prop),
      InvP P (cwT P read g) S b →
      ∃ pre, pre <+: ord ∧
        (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).2.2 = pre.reverse ++ J ∧
        (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).2.1 =
          (pre.map (arrOf gbs R ix c Ls ps)).reverse ++ acc ∧
        (sbound (min (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).1.pen P) <
            (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).2.2.length ∨ pre = ord) ∧
        InvP P (cwT P read g) (fun w => S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
          GX gbs R c (min P 15) e w) (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).1 ∧
        (phase1 ix R gbs[c]! c P (min P 15) Ls ps ord J acc b).1.pen ≤ b.pen := by
  intro ord
  induction ord with
  | nil =>
    intro J acc b S h
    refine ⟨[], List.prefix_refl _, rfl, rfl, Or.inr rfl, inv_congrP P _ _ _ _ h (fun w => by simp), Nat.le_refl _⟩
  | cons j rest ih =>
    intro J acc b S h
    have hf := foldl_invP P (cwT P read g)
      (fun b e => addK R gbs[c]! c (min P 15) ((e / 16 : Nat) - (R.size : Int)) R.size b)
      (fun e w => GX gbs R c (min P 15) e w)
      (fun e S b h => addK_inv P read g gbs R hg hr c (min P 15) hc (Nat.min_le_left _ _)
        (Nat.min_le_right _ _) _ _ S b h)
      (arrOf gbs R ix c Ls ps j).toList S b h
    have hfp := foldl_pen (fun b e => addK R gbs[c]! c (min P 15) ((e / 16 : Nat) - (R.size : Int)) R.size b)
      (fun b e => addK_pen _ _ _ _ _ _ b) (arrOf gbs R ix c Ls ps j).toList b
    rw [Array.foldl_toList] at hf hfp
    unfold phase1
    simp only []
    rw [show LookG.look ix gbs[c]! R (j * Ls) (R.size - j * Ls) ps[j]! = arrOf gbs R ix c Ls ps j from rfl]
    generalize hb1 : (arrOf gbs R ix c Ls ps j).foldl
      (fun b e => addK R gbs[c]! c (min P 15) ((e / 16 : Nat) - (R.size : Int)) R.size b) b = b1
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

/-- The windows a stage looks at. -/
def StageX (X : Int → Int → Window → Prop) (shs : List (Int × Int)) (acc : List (Array Nat)) (w : Window) : Prop :=
  ∃ arr ∈ acc, ∃ e ∈ arr.toList, ∃ sh ∈ shs, X (wst R.size e sh) (wlen R.size sh) w

theorem stageK_spec (hc : c < gbs.size) (shs : List (Int × Int)) (acc : List (Array Nat)) (b : Best)
    (S : Window → Prop) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ StageX R (KX gbs R c (min P 15)) shs acc w)
      (stageK R gbs[c]! c (min P 15) shs acc b) ∧ (stageK R gbs[c]! c (min P 15) shs acc b).pen ≤ b.pen := by
  have hsh : ∀ (e : Nat) S b, InvP P (cwT P read g) S b →
      InvP P (cwT P read g) (fun w => S w ∨ ∃ sh ∈ shs, KX gbs R c (min P 15) (wst R.size e sh) (wlen R.size sh) w)
        (shs.foldl (fun b sh => addK R gbs[c]! c (min P 15) (wst R.size e sh) (wlen R.size sh) b) b) :=
    fun e => foldl_invP P (cwT P read g) _ (fun sh w => KX gbs R c (min P 15) (wst R.size e sh) (wlen R.size sh) w)
      (fun sh S b h => addK_inv P read g gbs R hg hr c (min P 15) hc (Nat.min_le_left _ _)
        (Nat.min_le_right _ _) _ _ S b h) shs
  have harr : ∀ (arr : Array Nat) S b, InvP P (cwT P read g) S b →
      InvP P (cwT P read g) (fun w => S w ∨ ∃ e ∈ arr.toList, ∃ sh ∈ shs,
          KX gbs R c (min P 15) (wst R.size e sh) (wlen R.size sh) w)
        (arr.foldl (fun b e => shs.foldl (fun b sh =>
          addK R gbs[c]! c (min P 15) (wst R.size e sh) (wlen R.size sh) b) b) b) := by
    intro arr S b h
    rw [← Array.foldl_toList]
    exact foldl_invP P (cwT P read g) _ _ (fun e S b h => hsh e S b h) arr.toList S b h
  have hp1 : ∀ (e : Nat) b, (shs.foldl (fun b sh => addK R gbs[c]! c (min P 15) (wst R.size e sh) (wlen R.size sh) b) b).pen ≤ b.pen :=
    fun e => foldl_pen _ (fun b sh => addK_pen _ _ _ _ _ _ b) shs
  have hp2 : ∀ (arr : Array Nat) b, (arr.foldl (fun b e => shs.foldl (fun b sh =>
      addK R gbs[c]! c (min P 15) (wst R.size e sh) (wlen R.size sh) b) b) b).pen ≤ b.pen := by
    intro arr b; rw [← Array.foldl_toList]; exact foldl_pen _ (fun b e => hp1 e b) arr.toList b
  unfold stageK
  exact ⟨inv_congrP P _ _ _ _ (foldl_invP P (cwT P read g) _ _ (fun arr S b h => harr arr S b h) acc S b h)
    (fun w => by unfold StageX; rfl), foldl_pen _ (fun b arr => hp2 arr b) acc b⟩

theorem bandPenE_eq (c st len : Nat) (hc : c < gbs.size) :
    bandPenE P R.size len (decide (st + len ≤ gbs[c]!.size))
      (bandEnd2 sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs[c]! (st + len)) = bandPen P R gbs ⟨c, st, len⟩ := by
  unfold bandPenE bandPen bandScore
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
  unfold addBS; simp only []; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

theorem stageBD_pen (c : Nat) (shs : List (Int × Int)) (D : Nat) (b : Best) (bb : Int) :
    (stageBD P R gbs c shs D b bb).pen ≤ b.pen := by
  unfold stageBD; split
  · exact foldl_pen _ (fun b sh => addBS_pen P read g gbs R hg hr c D _ b sh) _ b
  · exact Nat.le_refl _

theorem stageB_pen (c : Nat) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (b : Best) :
    (stageB P R gbs c shs bs ds b).pen ≤ b.pen := by
  unfold stageB
  exact foldl_pen _ (fun b D => foldl_pen _ (fun b bb => stageBD_pen P read g gbs R hg hr c shs D b bb) bs b) ds b

theorem addBS_spec (hc : c < gbs.size) (D : Nat) (bb : Int) (sh : Int × Int) (hsb : sh.2 = bb) (S : Window → Prop)
    (b : Best) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ (0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (addBS P R gbs c D (bandEndAt P R gbs c D bb) b sh) := by
  unfold addBS
  simp only []
  split
  · next hp =>
    have he : ((D : Int) + bb).toNat = ((D : Int) - R.size - sh.1).toNat + ((R.size : Int) + sh.1 + sh.2).toNat := by
      omega
    unfold bandEndAt
    rw [he, bandPenE_eq P read g gbs R hg hr _ _ _ hc, bandPen_eq P read g gbs R hg hr]
    refine inv_congrP P _ _ _ _ (inv_addP P (cwT P read g) (cwT_le P read g) S b h c _ _ _ (Or.inl rfl)) ?_
    intro w; constructor
    · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl⟩
    · rintro (hw | ⟨-, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
  · next hp =>
    refine inv_congrP P _ _ _ _ h ?_
    intro w; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨h1, h2, -⟩); exact hw; exact absurd ⟨h1, h2⟩ hp

theorem stageBD_spec (hc : c < gbs.size) (shs : List (Int × Int)) (D : Nat) (bb : Int) (S : Window → Prop)
    (b : Best) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (stageBD P R gbs c shs D b bb) := by
  unfold stageBD
  split
  · next hD =>
    have hl := foldl_invP_mem P (cwT P read g) _ (fun (sh : Int × Int) w => sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩)
      (shs.filter (·.2 == bb))
      (fun sh hsh S b h => by
        have hs2 : sh.2 = bb := by simpa using (List.mem_filter.1 hsh).2
        exact inv_congrP P _ _ _ _ (addBS_spec P read g gbs R hg hr c hc D bb sh hs2 S b h)
          (fun w => by simp [hs2])) S b h
    refine inv_congrP P _ _ _ _ hl (fun w => ?_)
    constructor
    · rintro (hw | ⟨sh, hsh, hx⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨hD, sh, (List.mem_filter.1 hsh).1, hx⟩
    · rintro (hw | ⟨-, sh, hsh, hx⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨sh, List.mem_filter.2 ⟨hsh, by simp [hx.1]⟩, hx⟩
  · next hD => exact inv_congrP P _ _ _ _ h (fun w => by simp [hD])

theorem stageB_spec (hc : c < gbs.size) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (b : Best)
    (S : Window → Prop) (h : InvP P (cwT P read g) S b) :
    InvP P (cwT P read g) (fun w => S w ∨ BW R c shs bs ds w) (stageB P R gbs c shs bs ds b) := by
  unfold stageB
  have hD : ∀ (D : Nat) S b, InvP P (cwT P read g) S b →
      InvP P (cwT P read g) (fun w => S w ∨ ∃ bb ∈ bs, (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
        (bs.foldl (stageBD P R gbs c shs D) b) :=
    fun D => foldl_invP P (cwT P read g) _ _ (fun bb S b h => stageBD_spec P read g gbs R hg hr c hc shs D bb S b h) bs
  exact inv_congrP P _ _ _ _ (foldl_invP P (cwT P read g) _ _ (fun D S b h => hD D S b h) ds S b h)
    (fun w => by unfold BW; rfl)

end chrom

/-! ## One chromosome -/

theorem le_div_seeds (n : Nat) (hm : 0 < n / 25) : 25 ≤ n / (n / 25) := by
  rw [Nat.le_div_iff_mul_le hm]
  have := Nat.div_mul_le_self n 25
  rw [Nat.mul_comm]; exact this

section chrom2
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c : Nat) (ps : Array Pp) (ord : List Nat)
  (hc : c < gbs.size) (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25)
  (hps : ∀ j, j < R.size / 25 → ps[j]! = LookG.prep ix (seedHashAt R (j * (R.size / (R.size / 25)))))
  (hlook : ∀ s base, s + q ≤ R.size →
    LookOkS gbs[c]! R s base 0 (LookG.look ix gbs[c]! R s base (LookG.prep ix (seedHashAt R s))))
  (hnd : ord.Nodup) (hlt : ∀ j ∈ ord, j < R.size / 25) (hlen : ord.length = R.size / 25)

include hg hr hc hm hsb hps hlook hnd hlt hlen

set_option maxHeartbeats 2000000 in
/-- **One chromosome.**  After `chromG`, every window of chromosome `c` within
penalty `min best P` was added. -/
theorem chromG_cover (S : Window → Prop) (b : Best) (h : InvP P (cwT P read g) S b) :
    ∃ S', InvP P (cwT P read g) S' (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b) ∧
      (∀ w, S w → S' w) ∧
      ∀ w, w.chr = c → cwT P read g w ≤ min (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b).pen P →
        S' w := by
  generalize hmv : R.size / 25 = m at *
  generalize hLs : R.size / m = Ls at *
  have hL25 : 25 ≤ Ls := by rw [← hLs, ← hmv]; exact le_div_seeds _ (by omega)
  have hq : q = 25 := rfl
  have hn := hr.1
  have hmL : m * Ls ≤ R.size := by rw [← hLs]; exact Nat.div_mul_le_self _ _ |> fun h => by rw [Nat.mul_comm]; exact h
  obtain ⟨pre, hpre, hJ, hacc, hstop, hinv1, hpen1⟩ := phase1_spec P read g gbs R hg hr ix c Ls ps hc ord [] [] b S h
  unfold chromG
  simp only []
  generalize hr1 : phase1 ix R gbs[c]! c P (min P 15) Ls ps ord [] [] b = r1 at *
  obtain ⟨b1, acc, J⟩ := r1
  simp only [List.append_nil] at hJ hacc hstop hinv1 hpen1 ⊢
  -- stage K
  generalize hQ1 : min b1.pen P = Q1
  generalize hshK : (shapesAt Q1).filter (· != (0, 0)) = shK
  have hK := stageK_spec P read g gbs R hg hr c hc shK acc b1 _ hinv1
  have h2 : InvP P (cwT P read g) (fun w => (S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
        GX gbs R c (min P 15) e w) ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageX R (KX gbs R c (min P 15)) shK acc w))
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs[c]! c (min P 15) shK acc b1 else b1) ∧
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs[c]! c (min P 15) shK acc b1 else b1).pen ≤ b1.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hK.1 (fun w => by simp [hk]), hK.2⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ hinv1 (fun w => by simp [hk]), Nat.le_refl _⟩
  generalize hb2 : (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs[c]! c (min P 15) shK acc b1 else b1) = b2 at h2
  -- stage B
  generalize hQ2 : min b2.pen P = Q2
  generalize hdsv : diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int))) = ds
  have hB := stageB_spec P read g gbs R hg hr c hc (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 _ h2.1
  have hBp := stageB_pen P read g gbs R hg hr c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
  have h3 : InvP P (cwT P read g) (fun w => ((S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
        GX gbs R c (min P 15) e w) ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageX R (KX gbs R c (min P 15)) shK acc w)) ∨
        (min P 15 < Q2 ∧ BW R c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds w))
      (if min P 15 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2) ∧
      (if min P 15 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2).pen
        ≤ b2.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hB (fun w => by simp [hk]), hBp⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ h2.1 (fun w => by simp [hk]), Nat.le_refl _⟩
  refine ⟨_, h3.1, fun w hw => Or.inl (Or.inl (Or.inl hw)), ?_⟩
  generalize (if min P 15 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
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
  have hpnd : pre.Nodup := hpre.sublist.nodup hnd
  have hJn : J.Nodup := by rw [hJ]; exact (List.reverse_perm pre).nodup_iff.2 hpnd
  have hJm : ∀ j ∈ J, j < m := by
    intro j hj; rw [hJ, List.mem_reverse] at hj; exact hlt j (hpre.sublist.subset hj)
  rw [hQ1] at hstop
  have hJl : sbound x < J.length := by
    have := sbound_mono x Q1 hx1
    rcases hstop with h | h
    · omega
    · rw [hJ, List.length_reverse, h, hlen]
      have := sbound_mono Q1 P (by omega); omega
  obtain ⟨j, hj, p, a, bb, hcg, hmatch, hshape, ha1, ha2, hst, hwl⟩ :=
    cover g read gbs R hg hr (-(x : Int)) (m - 1) (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
      J hJn (fun j hj => by have := hJm j hj; omega) (by unfold sbound at hJl; omega) w (-(x : Int)) hws (Int.le_refl _)
  rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch ha1 hst
  rw [← hn] at hwl
  rw [hwc] at hmatch
  have hjm := hJm j hj
  have hjL : j * Ls + Ls ≤ R.size := by
    have : j * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  -- the anchor
  have hjpre : j ∈ pre := by rw [hJ, List.mem_reverse] at hj; exact hj
  have harr : arrOf gbs R ix c Ls ps j ∈ acc := by
    rw [hacc, List.mem_reverse]; exact List.mem_map_of_mem hjpre
  have he : (p + (R.size - j * Ls)) * 16 + 0 ∈ (arrOf gbs R ix c Ls ps j).toList := by
    unfold arrOf
    rw [hps j hjm]
    exact ((hlook (j * Ls) _ (by omega)).2 _).2 ⟨p, hmatch, rfl⟩
  generalize he' : (p + (R.size - j * Ls)) * 16 + 0 = e at he
  have he16 : e / 16 = p + (R.size - j * Ls) := by rw [← he']; omega
  have hwst : ∀ sh : Int × Int, sh.1 = a → wst R.size e sh = (p : Int) - (j * Ls : Nat) - a := by
    intro sh hsh; unfold wst; rw [he16, hsh]; push_cast; omega
  have hwlen : ∀ sh : Int × Int, sh.1 = a → sh.2 = bb → wlen R.size sh = (R.size : Int) + a + bb := by
    intro sh h1 h2; unfold wlen; rw [h1, h2]
  have hwin : w = ⟨c, ((p : Int) - (j * Ls : Nat) - a).toNat, ((R.size : Int) + a + bb).toNat⟩ := by
    cases w; simp only at hwc hst hwl; rw [hwc, hst, hwl, hn]
  -- the kernel value of the window
  have hker : min x (min P 15 + 1) =
      kerG R gbs[c]! ((p : Int) - (j * Ls : Nat) - a).toNat ((R.size : Int) + a + bb).toNat (min P 15) := by
    rw [← cwT_ker P read g gbs R hg hr c _ _ (min P 15) hc (Nat.min_le_left _ _) (Nat.min_le_right _ _), ← hx, hwin]
  -- the band stage covers the windows above `lim`
  have hband : min P 15 < x → BW R c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds w := by
    intro hlx
    have hdx := gapBound_mono x Q2 hx2
    have hsa := hshape.1
    refine ⟨e / 16, ?_, bb, ?_, ?_, (a, bb), shapesAt_mem x Q2 hx2 a bb hshape, rfl, ?_, ?_, ?_⟩
    · -- the diagonal is one of the stage's: an anchor's, and supported
      rw [← hdsv]
      unfold diagsB
      rw [List.mem_filter, List.mem_eraseDups, List.mem_flatMap]
      refine ⟨⟨_, harr, List.mem_map.2 ⟨e, he, rfl⟩⟩, decide_eq_true ?_⟩
      -- seeds without an anchor near the window: at most `sbound x` of them
      generalize hr2 : 2 * gapBound sc0 (-(Q2 : Int)) = r
      generalize hpred : (fun arr : Array Nat => arr.any fun e' =>
        decide (e / 16 ≤ e' / 16 + r) && decide (e' / 16 ≤ e / 16 + r)) = pred
      have hsupp : suppA acc (e / 16) r = (pre.filter (pred ∘ arrOf gbs R ix c Ls ps)).length := by
        unfold suppA; rw [← hpred, hacc, List.filter_reverse, List.length_reverse, List.filter_map, List.length_map]
      rw [hsupp]
      have hcnt : ∀ (l : List Nat) (f : Nat → Bool),
          (l.filter f).length + (l.filter (fun x => !f x)).length = l.length := by
        intro l f; induction l with
        | nil => rfl
        | cons y l ih => by_cases hy : f y = true <;> simp [hy] <;> omega
      have hc2 := hcnt pre (pred ∘ arrOf gbs R ix c Ls ps)
      have hJ' : (pre.filter (fun j' => !(pred ∘ arrOf gbs R ix c Ls ps) j')).length ≤ sbound x := by
        apply Classical.byContradiction; intro hlt'
        have hsub := List.filter_sublist (p := fun j' => !(pred ∘ arrOf gbs R ix c Ls ps) j') (l := pre)
        obtain ⟨j', hj', p', a', bb', -, hmatch', hshape', ha1', -, hst', -⟩ :=
          cover g read gbs R hg hr (-(x : Int)) (m - 1) (by rw [← hn, show m - 1 + 1 = m by omega, hLs]; omega)
            _ (hsub.nodup hpnd)
            (fun j hj => by have := hlt j (hpre.sublist.subset (hsub.subset hj)); omega)
            (by unfold sbound at hlt'; omega) w (-(x : Int)) hws (Int.le_refl _)
        rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch' ha1' hst'
        rw [hwc] at hmatch'
        have hj'pre := hsub.subset hj'
        have hj'm := hlt j' (hpre.sublist.subset hj'pre)
        have hj'L : j' * Ls + Ls ≤ R.size := by
          have : j' * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        have he2 : (p' + (R.size - j' * Ls)) * 16 + 0 ∈ (arrOf gbs R ix c Ls ps j').toList := by
          unfold arrOf
          rw [hps j' hj'm]
          exact ((hlook (j' * Ls) _ (by omega)).2 _).2 ⟨p', hmatch', rfl⟩
        have hpj : (pred ∘ arrOf gbs R ix c Ls ps) j' = true := by
          simp only [Function.comp, ← hpred]
          rw [← Array.any_toList, List.any_eq_true]
          refine ⟨_, he2, ?_⟩
          have hsa' := hshape'.1
          have hd' := gapBound_mono x Q2 hx2
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          have e1 : ((p' + (R.size - j' * Ls)) * 16 + 0) / 16 = p' + (R.size - j' * Ls) := by omega
          rw [e1, he16]
          omega
        have := (List.mem_filter.1 hj').2
        rw [hpj] at this; cases this
      have := sbound_mono x P hxP
      have hal : acc.length = pre.length := by rw [hacc]; simp
      omega
    · unfold shifts
      rw [List.mem_map]
      refine ⟨(bb + (gapBound sc0 (-(Q2 : Int)) : Int)).toNat, List.mem_range.2 (by omega), by omega⟩
    · rw [he16]; omega
    · rw [he16]; omega
    · omega
    · rw [hwin, he16]; congr 2; omega
  by_cases h00 : a = 0 ∧ bb = 0
  · -- the same-length window: phase 1, or the band stage
    obtain ⟨rfl, rfl⟩ := h00
    by_cases hxl : x ≤ min P 15
    · left; left; right
      refine ⟨j, hjpre, e, he, ?_⟩
      unfold GX KX
      rw [he16]
      have e1 : ((p + (R.size - j * Ls) : Nat) : Int) - (R.size : Int) = (p : Int) - (j * Ls : Nat) - 0 := by omega
      have e2 : (R.size : Int) = (R.size : Int) + 0 + 0 := by omega
      rw [e1]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [e2, ← hker]; omega
      · rw [e2]; exact hwin
    · right; exact ⟨by omega, hband (by omega)⟩
  · -- a gapped shape: stage K, or the band stage
    have hab : 1 ≤ a.natAbs + bb.natAbs := by omega
    have hgb : 0 < gapBound sc0 (-(Q1 : Int)) := by
      have := gapBound_mono x Q1 hx1; have := hshape.1; omega
    by_cases hxl : x ≤ min P 15
    · left; right
      refine ⟨hgb, _, harr, e, he, (a, bb), ?_, ?_⟩
      · rw [← hshK, List.mem_filter]
        refine ⟨shapesAt_mem x Q1 hx1 a bb hshape, ?_⟩
        simp only [bne_iff_ne, ne_eq, Prod.mk.injEq]; omega
      · rw [hwst (a, bb) rfl, hwlen (a, bb) rfl rfl]
        refine ⟨by omega, by omega, ?_, hwin⟩
        rw [← hker]; omega
    · right; exact ⟨by omega, hband (by omega)⟩

end chrom2

end MapSpec.Fast
