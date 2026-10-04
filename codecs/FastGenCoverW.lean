import FastGenProof

/-!
`chromG_coverW`: `chromG_cover` (codecs/FastGenProof.lean) for any penalty
function `cw` that agrees with the read's own penalty `cwT P read g` on the
windows of the chromosome being searched (and is `≤ P + 1` everywhere).  This
lets one shared `Best` span chromosomes searched with different reads (the two
strands, codecs/PairGen.lean).  Same proof as there, with `cw` for `cwT P read g`
(generated from FastGenProof; to be replaced when that file states the general form).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

section adds
variable (cw : Window → Nat) (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read) (hle : ∀ w, cw w ≤ P + 1)

/-- The window `(st, len)` of chromosome `c`, when its penalty is `≤ lim`. -/
def KXW (c lim : Nat) (st len : Int) (w : Window) : Prop :=
  0 ≤ st ∧ 0 ≤ len ∧ w = ⟨c, st.toNat, len.toNat⟩ ∧ cw w ≤ lim

include hg hr hle

/-- `addK` adds the window when its penalty is `≤ min lim best`; a window between
`best` and `lim` cannot change the result, so it counts as added (`inv_skipP`). -/
theorem addK_invW (c lim : Nat) (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (h1 : lim ≤ P) (h2 : lim ≤ 16) (st len : Int)
    (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ KXW cw c lim st len w) (addK R gbs c lim st len b) := by
  unfold addK
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    dsimp only
    have hm := cwT_kerH P read g gbs R hg hr c st.toNat len.toNat (min lim b.pen) hc (by omega) (by omega)
    by_cases hk : kerH R gbs c st.toNat len.toNat (min lim b.pen) ≤ min lim b.pen
    · rw [if_pos hk]
      have hex : kerH R gbs c st.toNat len.toNat (min lim b.pen) = cw ⟨c, st.toNat, len.toNat⟩ := by rw [hcwc]; omega
      apply inv_congrP P _ _ _ _ (inv_addP P cw hle S b h c st.toNat len.toNat _ (Or.inl hex))
      intro w; unfold KXW; constructor
      · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl, by omega⟩
      · rintro (hw | ⟨-, -, rfl, -⟩); exact Or.inl hw; exact Or.inr rfl
    · rw [if_neg hk]
      apply inv_skipP P cw hle S _ b h
      rintro w ⟨-, -, rfl, hw⟩; left; rw [hcwc] at hw ⊢; omega
  · rw [if_neg hp]
    apply inv_congrP P _ _ _ _ h
    intro w; unfold KXW; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨a, b', -⟩); exact hw; exact absurd ⟨a, b'⟩ hp

theorem addB_invW (c : Nat) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (st len : Int) (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ BX c st len w) (addB P R gbs c st len b) := by
  unfold addB
  by_cases hp : 0 ≤ st ∧ 0 ≤ len
  · rw [if_pos hp]
    apply inv_congrP P _ _ _ _ (inv_addP P cw hle S b h c st.toNat len.toNat _
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

/-! ## Phase 1 and the stages -/

section chrom
variable (cw : Window → Nat) (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read) (hle : ∀ w, cw w ≤ P + 1)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c Ls : Nat) (ps : Array Pp)

/-- The same-length window `phase1` adds for anchor `e`. -/
def GXW (lim e : Nat) (w : Window) : Prop :=
  KXW cw c lim (((e / 16 : Nat) : Int) - (R.size : Int)) (R.size : Int) w

include hg hr hle

theorem phase1_specW (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) :
    ∀ (ord J : List Nat) (acc : List (Array Nat)) (b : Best) (S : Window → Prop),
      InvP P cw S b →
      ∃ pre, pre <+: ord ∧
        (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.2 = pre.reverse ++ J ∧
        (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.1 =
          (pre.map (arrOf gbs R ix c Ls ps)).reverse ++ acc ∧
        (sbound (min (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).1.pen P) <
            (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).2.2.length ∨ pre = ord) ∧
        InvP P cw (fun w => S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
          GXW cw R c (min P 16) e w) (phase1 ix R gbs c P (min P 16) Ls ps ord J acc b).1 ∧
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
      (fun e w => GXW cw R c (min P 16) e w)
      (fun e S b h => addK_invW cw P read g gbs R hg hr hle c (min P 16) hc hcwc (Nat.min_le_left _ _)
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
def StageKW (lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (w : Window) : Prop :=
  ∃ D ∈ ds, ∃ sh ∈ shs, KXW cw c lim (dst R.size D sh) (wlen R.size sh) w

theorem stageK_specW (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (shs : List (Int × Int)) (ds : List Nat) (b : Best)
    (S : Window → Prop) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ StageKW cw R c (min P 16) shs ds w)
      (stageK R gbs c (min P 16) shs ds b) ∧ (stageK R gbs c (min P 16) shs ds b).pen ≤ b.pen := by
  have hsh : ∀ (D : Nat) S b, InvP P cw S b →
      InvP P cw (fun w => S w ∨ ∃ sh ∈ shs, KXW cw c (min P 16) (dst R.size D sh) (wlen R.size sh) w)
        (shs.foldl (fun b sh => addK R gbs c (min P 16) (dst R.size D sh) (wlen R.size sh) b) b) :=
    fun D => foldl_invP P cw _ (fun sh w => KXW cw c (min P 16) (dst R.size D sh) (wlen R.size sh) w)
      (fun sh S b h => addK_invW cw P read g gbs R hg hr hle c (min P 16) hc hcwc (Nat.min_le_left _ _)
        (Nat.min_le_right _ _) _ _ S b h) shs
  have hp1 : ∀ (D : Nat) b, (shs.foldl (fun b sh => addK R gbs c (min P 16) (dst R.size D sh) (wlen R.size sh) b) b).pen
      ≤ b.pen :=
    fun D => foldl_pen _ (fun b sh => addK_pen _ _ _ _ _ _ b) shs
  unfold stageK
  exact ⟨inv_congrP P _ _ _ _ (foldl_invP P cw _ _ (fun D S b h => hsh D S b h) ds S b h)
    (fun w => by unfold StageKW; rfl), foldl_pen _ (fun b D => hp1 D b) ds b⟩

theorem addBS_specW (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (D : Nat) (bb : Int) (sh : Int × Int) (hsb : sh.2 = bb) (S : Window → Prop)
    (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ (0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (addBS P R gbs c D (bandEndAt P R gbs c D bb) b sh) := by
  unfold addBS
  simp only []
  split
  · next hp =>
    have he : ((D : Int) + bb).toNat = ((D : Int) - R.size - sh.1).toNat + ((R.size : Int) + sh.1 + sh.2).toNat := by
      omega
    unfold bandEndAt
    rw [he, bandPenE_eq P read g gbs R hg hr _ _ _ hc, bandPen_eq P read g gbs R hg hr, ← hcwc]
    refine inv_congrP P _ _ _ _ (inv_addP P cw hle S b h c _ _ _ (Or.inl rfl)) ?_
    intro w; constructor
    · rintro (hw | rfl); exact Or.inl hw; exact Or.inr ⟨hp.1, hp.2, rfl⟩
    · rintro (hw | ⟨-, -, rfl⟩); exact Or.inl hw; exact Or.inr rfl
  · next hp =>
    refine inv_congrP P _ _ _ _ h ?_
    intro w; constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | ⟨h1, h2, -⟩); exact hw; exact absurd ⟨h1, h2⟩ hp

theorem stageBD_specW (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (shs : List (Int × Int)) (D : Nat) (bb : Int) (S : Window → Prop)
    (b : Best) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
      (stageBD P R gbs c shs D b bb) := by
  unfold stageBD
  split
  · next hD =>
    have hl := foldl_invP_mem P cw _ (fun (sh : Int × Int) w => sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩)
      (shs.filter (·.2 == bb))
      (fun sh hsh S b h => by
        have hs2 : sh.2 = bb := by simpa using (List.mem_filter.1 hsh).2
        exact inv_congrP P _ _ _ _ (addBS_specW cw P read g gbs R hg hr hle c hc hcwc D bb sh hs2 S b h)
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

theorem stageB_specW (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat) (b : Best)
    (S : Window → Prop) (h : InvP P cw S b) :
    InvP P cw (fun w => S w ∨ BW R c shs bs ds w) (stageB P R gbs c shs bs ds b) := by
  unfold stageB
  have hD : ∀ (D : Nat) S b, InvP P cw S b →
      InvP P cw (fun w => S w ∨ ∃ bb ∈ bs, (0 ≤ (D : Int) + bb ∧ ∃ sh ∈ shs, sh.2 = bb ∧
        0 ≤ (D : Int) - R.size - sh.1 ∧ 0 ≤ (R.size : Int) + sh.1 + sh.2 ∧
        w = ⟨c, ((D : Int) - R.size - sh.1).toNat, ((R.size : Int) + sh.1 + sh.2).toNat⟩))
        (bs.foldl (stageBD P R gbs c shs D) b) :=
    fun D => foldl_invP P cw _ _ (fun bb S b h => stageBD_specW cw P read g gbs R hg hr hle c hc hcwc shs D bb S b h) bs
  exact inv_congrP P _ _ _ _ (foldl_invP P cw _ _ (fun D S b h => hD D S b h) ds S b h)
    (fun w => by unfold BW; rfl)

end chrom

/-! ## One chromosome -/

section chrom2
variable (cw : Window → Nat) (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read) (hle : ∀ w, cw w ≤ P + 1)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (c : Nat) (ps : Array Pp) (ord : List Nat)
  (hc : c < gbs.size) (hcwc : ∀ st len, cw ⟨c, st, len⟩ = cwT P read g ⟨c, st, len⟩) (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25)
  (hps : ∀ j, j < R.size / 25 → ps[j]! = LookG.prep ix (seedHashAt R (j * (R.size / (R.size / 25)))))
  (hlook : ∀ s base, s + q ≤ R.size →
    LookOkS gbs[c]! R s base 0 (LookG.look ix gbs[c]! R s base (LookG.prep ix (seedHashAt R s))))
  (hnd : ord.Nodup) (hlt : ∀ j ∈ ord, j < R.size / 25) (hlen : ord.length = R.size / 25)

include hg hr hle hc hcwc hm hsb hps hlook hnd hlt hlen

set_option maxHeartbeats 2000000 in
/-- **One chromosome.**  After `chromG`, every window of chromosome `c` within
penalty `min best P` was added. -/
theorem chromG_coverW (S : Window → Prop) (b : Best) (h : InvP P cw S b) :
    ∃ S', InvP P cw S' (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b) ∧
      (∀ w, S w → S' w) ∧
      ∀ w, w.chr = c → cw w ≤ min (chromG ix R gbs c P (R.size / (R.size / 25)) ps ord b).pen P →
        S' w := by
  generalize hmv : R.size / 25 = m at *
  generalize hLs : R.size / m = Ls at *
  have hL25 : 25 ≤ Ls := by rw [← hLs, ← hmv]; exact le_div_seeds _ (by omega)
  have hq : q = 25 := rfl
  have hn := hr.1
  have hmL : m * Ls ≤ R.size := by rw [← hLs]; exact Nat.div_mul_le_self _ _ |> fun h => by rw [Nat.mul_comm]; exact h
  obtain ⟨pre, hpre, hJ, hacc, hstop, hinv1, hpen1⟩ := phase1_specW cw P read g gbs R hg hr hle ix c Ls ps hc hcwc ord [] [] b S h
  unfold chromG
  simp only []
  generalize hr1 : phase1 ix R gbs c P (min P 16) Ls ps ord [] [] b = r1 at *
  obtain ⟨b1, acc, J⟩ := r1
  simp only [List.append_nil] at hJ hacc hstop hinv1 hpen1 ⊢
  -- stage K
  generalize hQ1 : min b1.pen P = Q1
  generalize hshK : (shapesAt Q1).filter (· != (0, 0)) = shK
  generalize hdsK : diagsB acc (acc.length - sbound (min (min P 16) Q1)) (2 * gapBound sc0 (-(Q1 : Int))) = dsK
  have hK := stageK_specW cw P read g gbs R hg hr hle c hc hcwc shK dsK b1 _ hinv1
  have h2 : InvP P cw (fun w => (S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
        GXW cw R c (min P 16) e w) ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageKW cw R c (min P 16) shK dsK w))
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1) ∧
      (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1).pen ≤ b1.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hK.1 (fun w => by simp [hk]), hK.2⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ hinv1 (fun w => by simp [hk]), Nat.le_refl _⟩
  generalize hb2 : (if 0 < gapBound sc0 (-(Q1 : Int)) then stageK R gbs c (min P 16) shK dsK b1 else b1) = b2 at h2
  -- stage B
  generalize hQ2 : min b2.pen P = Q2
  generalize hdsv : diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int))) = ds
  have hB := stageB_specW cw P read g gbs R hg hr hle c hc hcwc (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 _ h2.1
  have hBp := stageB_pen P read g gbs R hg hr c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
  have h3 : InvP P cw (fun w => ((S w ∨ ∃ j ∈ pre, ∃ e ∈ (arrOf gbs R ix c Ls ps j).toList,
        GXW cw R c (min P 16) e w) ∨ (0 < gapBound sc0 (-(Q1 : Int)) ∧ StageKW cw R c (min P 16) shK dsK w)) ∨
        (min P 16 < Q2 ∧ BW R c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds w))
      (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2) ∧
      (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2 else b2).pen
        ≤ b2.pen := by
    split
    · next hk => exact ⟨inv_congrP P _ _ _ _ hB (fun w => by simp [hk]), hBp⟩
    · next hk => exact ⟨inv_congrP P _ _ _ _ h2.1 (fun w => by simp [hk]), Nat.le_refl _⟩
  refine ⟨_, h3.1, fun w hw => Or.inl (Or.inl (Or.inl hw)), ?_⟩
  generalize (if min P 16 < Q2 then stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) ds b2
    else b2) = bf at h3
  intro w hwc hcw
  generalize hx : cw w = x at hcw
  have hx' : cwT P read g w = x := by
    rw [← hx]; obtain ⟨c', s', l'⟩ := w; simp only at hwc; subst hwc; exact (hcwc _ _).symm
  have hxP : x ≤ P := by omega
  have hxb : x ≤ bf.pen := by omega
  have hb21 := h2.2
  have hbf2 := h3.2
  have hx1 : x ≤ Q1 := by omega
  have hx2 : x ≤ Q2 := by omega
  -- the window scores `−x`
  have hws : windowScore sc0 read g w = some (-(x : Int)) := by
    have := (cwT_iff P read g w (-(cwT P read g w : Int))).2 ⟨by omega, rfl⟩
    rw [hx'] at this; exact this.1
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
  -- seeds without a clean anchor near the window: at most `sbound x` of them
  have hsuppG : ∀ r, 2 * gapBound sc0 (-(x : Int)) ≤ r → acc.length - sbound x ≤ suppA acc (e / 16) r := by
    intro r hrx
    have hsa := hshape.1
    generalize hpred : (fun arr : Array Nat => anyNear arr (e / 16 - r) (e / 16 + r)) = pred
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
      have hsort : (arrOf gbs R ix c Ls ps j').toList.Pairwise (· < ·) := by
        unfold arrOf
        rw [hps j' hj'm]
        exact (hlook (j' * Ls) _ (by omega)).1
      have hpj : (pred ∘ arrOf gbs R ix c Ls ps) j' = true := by
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
      rw [List.mem_map]
      refine ⟨(bb + (gapBound sc0 (-(Q2 : Int)) : Int)).toNat, List.mem_range.2 (by omega), by omega⟩
    · rw [he16]; omega
    · rw [he16]; omega
    · omega
    · rw [hwin, he16]; congr 2; omega
  by_cases h00 : a = 0 ∧ bb = 0
  · -- the same-length window: phase 1, or the band stage
    obtain ⟨rfl, rfl⟩ := h00
    by_cases hxl : x ≤ min P 16
    · left; left; right
      refine ⟨j, hjpre, e, he, ?_⟩
      unfold GXW KXW
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

end chrom2

end MapSpec.Fast

#print axioms MapSpec.Fast.chromG_coverW
