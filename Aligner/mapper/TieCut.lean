import FastGenPair
import FastGenK250
import WgPacked

/-!
# Tie cut: after a tie at penalty `p`, the gapped stage runs at cap `p − 1`

A mate's whole-genome search (`mapChromsGB`) is phase 1 (seed lookups, same-length windows; best
`b1`) followed by the gapped stages K/B over every chromosome and strand.  When `b1` is already a tie
(`amb`) at `p`, a window scoring `p` changes nothing (`Best.add` keeps the tie), so only windows
below `p` matter: the gapped stages run at cap `p − 1` from a fresh best (`tieCut`), and the result is
that best when it is below `p`, else `b1`.  A tie at `0` needs no gapped stage at all.

`mapChromsGBT_inv`: the same invariant as `mapChromsGB_inv`, so every theorem built on it holds for the
cut search.  The cut needs no new search proof: the existing cover theorem (`kbFold`) runs at cap `p − 1`,
and phase 1's lookups (made for cap `P`) satisfy its stop rule there (`sbound` is monotone).
-/

namespace MapSpec.Fast

open MapSpec

/-- The gapped stages `gap Q b` (cap `Q`, start best `b`) after phase 1's best `b1`, cut at a tie. -/
@[inline] def tieCut (P : Nat) (gap : Nat → Best → Best) (b1 : Best) : Best :=
  if b1.amb && decide (b1.pen ≤ P) then
    if b1.pen = 0 then b1 else
    let b := gap (b1.pen - 1) (initP (b1.pen - 1))
    if b.pen < b1.pen then b else b1
  else gap P b1

/-! ## Phase 1 with the tie cut's stop rule

After a tie at `p`, the gapped stages only look for windows below `p` (cap `p − 1`), and their cover
theorem needs only `sbound (p − 1) + 1` seeds looked up per strand: phase 1 stops on `effP` (the best's
penalty, minus one when it is a tie). -/

/-- The penalty the search still has to beat: one less than a tie's. -/
@[inline] def effP (b : Best) : Nat := if b.amb && decide (0 < b.pen) then b.pen - 1 else b.pen

/-- `GS.live` on `effP`. -/
@[inline] def GS.liveT (P : Nat) (s : GS) (b : Best) : Bool :=
  !s.ord.isEmpty && !decide (sbound (min (effP b) P) < s.J.length)

/-- `ilG` stopping on `GS.liveT`. -/
@[specialize] def ilGT {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.liveT P b
    if s1.liveT P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.adv ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGT ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.adv ix G R2 gbs2 offs n n P Ls ps2 b
      ilGT ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `ilGF` (kernels as parameters) stopping on `GS.liveT`. -/
@[specialize] def ilGFT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.liveT P b
    if s1.liveT P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advF kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGFT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advF kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGFT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `ilGFG` (any chromosome representation) stopping on `GS.liveT`. -/
@[specialize] def ilGFGT {Gt : Type} [GRead Gt] [Inhabited Gt] [GPk Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.liveT P b
    if s1.liveT P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advFG kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGFGT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advFG kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGFGT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `ilGFGT` with the strands' lookup counts carried (`ilGFGNT_eq`). -/
@[specialize] def ilGFGNT {Gt : Type} [GRead Gt] [Inhabited Gt] [GPk Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Nat → Nat → Best → GS × GS × Best
  | 0, s1, s2, _, _, b => (s1, s2, b)
  | f + 1, s1, s2, k1, k2, b =>
    let sb := sbound (min (effP b) P)
    let l2 := !s2.ord.isEmpty && !decide (sb < k2)
    if (!s1.ord.isEmpty && !decide (sb < k1)) && (!l2 || decide (k1 ≤ k2)) then
      let r := s1.advFG kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGFGNT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 (k1 + 1) k2 r.2
    else if l2 then
      let r := s2.advFG kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGFGNT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 k1 (k2 + 1) r.2
    else (s1, s2, b)

theorem ilGFGNT_eq {Gt : Type} [GRead Gt] [Inhabited Gt] [GPk Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) : ∀ (f : Nat) (s1 s2 : GS) (b : Best),
    ilGFGNT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 s1.J.length s2.J.length b =
      ilGFGT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b
  | 0, _, _, _ => rfl
  | f + 1, s1, s2, b => by
    unfold ilGFGNT ilGFGT GS.liveT
    simp only []
    split
    · next h =>
      have h1 : s1.ord.isEmpty = false := by
        cases he : s1.ord.isEmpty <;> simp_all
      rw [← GS.advFG_J kf1 ix G R1 gbs2 offs n 0 P Ls ps1 s1 b h1]
      exact ilGFGNT_eq kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f _ _ _
    · split
      · next h =>
        have h2 : s2.ord.isEmpty = false := by
          cases he : s2.ord.isEmpty <;> simp_all
        rw [← GS.advFG_J kf2 ix G R2 gbs2 offs n n P Ls ps2 s2 b h2]
        exact ilGFGNT_eq kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f _ _ _
      · rfl

/-- `ilGFGNT` from the strands' own counts. -/
@[inline] def ilGFGWT {Gt : Type} [GRead Gt] [Inhabited Gt] [GPk Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) (f : Nat) (s1 s2 : GS) (b : Best) :
    GS × GS × Best :=
  ilGFGNT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 s1.J.length s2.J.length b

/-- Compiled code runs `ilGFGWT`. -/
@[csimp] theorem ilGFGT_eqN : @ilGFGT = @ilGFGWT := by
  funext
  simp only [ilGFGWT, ilGFGNT_eq]

theorem ilGFT_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGFT (kerH R1 gbs2) (kerH R2 gbs2) ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b =
      ilGT ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih =>
    intro s1 s2 b
    simp only [ilGFT, ilGT, advF_eq, ih]

theorem ilGFGT_bytes {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGFGT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b =
      ilGFT kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilGFGT, ilGFT, advFG_bytes, ih]

theorem ilGFGT_same {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] [GPk G1] [GPk G2]
    {xs : Array G1} {ys : Array G2} (h : SameA xs ys) {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (kf1 kf2 : Ker) (ix : L) (G : ByteArray) (R1 R2 : ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGFGT kf1 kf2 ix G R1 R2 xs offs n P Ls ps1 ps2 f s1 s2 b =
      ilGFGT kf1 kf2 ix G R1 R2 ys offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilGFGT, advFG_same h, ih]

theorem ilGT_congrG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p)
    (R1 R2 : ByteArray) (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat)
    (ps1 ps2 : Array Pp) : ∀ f s1 s2 b,
      ilGT ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b = ilGT ix G' R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilGT, GS.adv, hG, ih]

/-- `mapChromsGB` with the tie cut. -/
@[specialize] def mapChromsGBT {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (P : Nat) (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array Gt) (R : ByteArray) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let Rr := revCompB2 R
  let m := R.size / 25
  let Ls := R.size / m
  let ps := prepG ix R m Ls
  let pr := prepG ix Rr m Ls
  let x := ilGT ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  tieCut P (fun Q b =>
    let b := (List.range n).foldl (fun b c => chromKBS R gbs2 c Q x.1.acc[c]! x.1.J b) b
    (List.range n).foldl (fun b c => chromKBS Rr gbs2 (n + c) Q x.2.1.acc[c]! x.2.1.J b) b) x.2.2

/-! ## Caps -/

theorem cwT_capT (P Q : Nat) (read : List Char) (g : Genome) (w : Window) (hQ : Q ≤ P)
    (h : cwT P read g w ≤ Q ∨ cwT Q read g w ≤ Q) : cwT P read g w = cwT Q read g w := by
  rw [cwT_cap P read g Q hQ w] at h ⊢
  split at h <;> split <;> omega

theorem cwB_capT (P Q : Nat) (read : List Char) (g : Genome) (w : Window) (hQ : Q ≤ P)
    (h : cwB P read g w ≤ Q ∨ cwB Q read g w ≤ Q) : cwB P read g w = cwB Q read g w := by
  by_cases hc : w.chr < g.length
  · simp only [cwB, hc, if_true] at h ⊢; exact cwT_capT P Q _ g w hQ h
  · simp only [cwB, hc, if_false] at h ⊢; exact cwT_capT P Q _ g _ hQ h

theorem gsOk_cap (P Q : Nat) (g : Genome) (gbs : Array ByteArray) {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (ix : L) (G : ByteArray) (offs : Array Nat) (Rs : ByteArray) (reads : List Char) (t Ls : Nat) (ps : Array Pp)
    (S : Window → Prop) (ord0 : List Nat) (s : GS) (hQ : Q ≤ P)
    (h : GSok P g gbs ix G offs Rs reads t Ls ps S ord0 s)
    (hS : ∀ c, c < gbs.size → ∀ st len, S ⟨t + c, st, len⟩ → cwT P reads (g ++ g) ⟨t + c, st, len⟩ ≤ Q → False) :
    GSok Q g gbs ix G offs Rs reads t Ls ps (fun _ => False) ord0 s := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun c hc j hj e he w hw => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have e' := cwT_capT P Q reads (g ++ g) w hQ (Or.inr (by omega))
  have hS' := h.2.2.2 c hc j hj e he w ⟨h1, h2, h3, by omega⟩
  rw [h3] at hS' e' h4
  exact hS c hc _ _ hS' (by omega)

section bothT
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (R1 R2 : ByteArray) (reads1 reads2 : List Char) (h1 : Encodes R1 reads1) (h2 : Encodes R2 reads2)
  (hcw1 : ∀ c, c < gbs.size → ∀ st len, cwB P read g ⟨0 + c, st, len⟩ = cwT P reads1 (g ++ g) ⟨0 + c, st, len⟩)
  (hcw2 : ∀ c, c < gbs.size → ∀ st len,
    cwB P read g ⟨gbs.size + c, st, len⟩ = cwT P reads2 (g ++ g) ⟨gbs.size + c, st, len⟩)
  (Ls : Nat) (ps1 ps2 : Array Pp) (ord1 ord2 : List Nat)

include hg h1 h2 hcw1 hcw2

theorem ilGT_ok : ∀ (f : Nat) (s1 s2 : GS) (b : Best) (S : Window → Prop),
    GSok P g gbs ix G offs R1 reads1 0 Ls ps1 S ord1 s1 →
    GSok P g gbs ix G offs R2 reads2 gbs.size Ls ps2 S ord2 s2 →
    InvP P (cwB P read g) S b → s1.ord.length + s2.ord.length < f →
    ∃ S', InvP P (cwB P read g) S' (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 ∧
      (∀ w, S w → S' w) ∧ (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2.pen ≤ b.pen ∧
      GSok P g gbs ix G offs R1 reads1 0 Ls ps1 S' ord1 (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).1 ∧
      GSok P g gbs ix G offs R2 reads2 gbs.size Ls ps2 S' ord2
        (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.1 ∧
      (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).1.liveT P
        (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 = false ∧
      (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.1.liveT P
        (ilGT ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 = false := by
  intro f
  induction f with
  | zero => intro s1 s2 b S _ _ _ hf; omega
  | succ f ih =>
    intro s1 s2 b S o1 o2 hi hf
    unfold ilGT
    simp only []
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      have hne : s1.ord ≠ [] := by
        intro he; unfold GS.liveT at hc; simp [he] at hc
      obtain ⟨j, rest, hjr⟩ : ∃ j rest, s1.ord = j :: rest := by
        cases h : s1.ord with
        | nil => exact absurd h hne
        | cons j rest => exact ⟨j, rest, rfl⟩
      obtain ⟨S1, i1, e1, p1, k1, r1, -⟩ := advG_ok P read g gbs hg ix G offs R1 reads1 h1 0 hcw1 Ls ps1
        (Or.inl rfl) ord1 s1 j rest hjr S b o1 hi
      obtain ⟨S2, i2, e2, p2, k2, k3, l1, l2⟩ := ih _ s2 _ S1 k1 (o2.mono P g gbs ix G offs R2 reads2 gbs.size Ls ps2 e1) i1
        (by rw [r1]; rw [hjr] at hf; simp at hf; omega)
      exact ⟨S2, i2, fun w hw => e2 w (e1 w hw), Nat.le_trans p2 p1, k2, k3, l1, l2⟩
    · next hc1 =>
      split
      · next hc =>
        have hne : s2.ord ≠ [] := by
          intro he; unfold GS.liveT at hc; simp [he] at hc
        obtain ⟨j, rest, hjr⟩ : ∃ j rest, s2.ord = j :: rest := by
          cases h : s2.ord with
          | nil => exact absurd h hne
          | cons j rest => exact ⟨j, rest, rfl⟩
        obtain ⟨S1, i1, e1, p1, k1, r1, -⟩ := advG_ok P read g gbs hg ix G offs R2 reads2 h2 gbs.size hcw2 Ls ps2
          (Or.inr rfl) ord2 s2 j rest hjr S b o2 hi
        obtain ⟨S2, i2, e2, p2, k2, k3, l1, l2⟩ := ih s1 _ _ S1 (o1.mono P g gbs ix G offs R1 reads1 0 Ls ps1 e1) k1 i1
          (by rw [r1]; rw [hjr] at hf; simp at hf; omega)
        exact ⟨S2, i2, fun w hw => e2 w (e1 w hw), Nat.le_trans p2 p1, k2, k3, l1, l2⟩
      · next hc2 =>
        simp only [Bool.not_eq_true] at hc2
        refine ⟨S, hi, fun w hw => hw, Nat.le_refl _, o1, o2, ?_, hc2⟩
        simp only [hc2, Bool.not_false, Bool.true_or, Bool.and_true, Bool.not_eq_true] at hc1
        exact hc1

end bothT

/-! ## The invariant -/

section top
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

include hg hr hcat hlk

set_option maxHeartbeats 1000000 in
/-- **The gapped stages of both strands at cap `Q`**, from phase-1 states meeting `GSok` at `Q` and its
stop rule: the invariant at `Q` over a set holding every window within `Q`. -/
theorem gapBoth_inv (Q : Nat) (hm : 0 < R.size / 25) (hsb : sbound Q < R.size / 25)
    (ps pr : Array Pp) (hps : ps = prepG ix R (R.size / 25) (R.size / (R.size / 25)))
    (hpr : pr = prepG ix (revCompB R) (R.size / 25) (R.size / (R.size / 25)))
    (ord1 ord2 : List Nat)
    (nd1 : ord1.Nodup) (lt1 : ∀ j ∈ ord1, j < R.size / 25) (len1 : ord1.length = R.size / 25)
    (nd2 : ord2.Nodup) (lt2 : ∀ j ∈ ord2, j < R.size / 25) (len2 : ord2.length = R.size / 25)
    (s1 s2 : GS) (S : Window → Prop) (b : Best)
    (o1 : GSok Q g gbs ix G offs R read 0 (R.size / (R.size / 25)) ps S ord1 s1)
    (o2 : GSok Q g gbs ix G offs (revCompB R) (revComp read) gbs.size (R.size / (R.size / 25)) pr S ord2 s2)
    (i1 : InvP Q (cwB Q read g) S b)
    (st1 : sbound (min b.pen Q) < s1.J.length ∨ s1.ord = [])
    (st2 : sbound (min b.pen Q) < s2.J.length ∨ s2.ord = []) :
    ∃ S', InvP Q (cwB Q read g) S'
        ((List.range gbs.size).foldl (fun b c => chromKBS (revCompB R) (gbs ++ gbs) (gbs.size + c) Q s2.acc[c]! s2.J b)
          ((List.range gbs.size).foldl (fun b c => chromKBS R (gbs ++ gbs) c Q s1.acc[c]! s1.J b) b)) ∧
      ∀ w, cwB Q read g w ≤ Q → S' w := by
  have hn : gbs.size = g.length := hg.1
  have hrr := revCompB_encodes R read hr
  have hsz := revCompB_size R
  have hcw1 : ∀ c, c < gbs.size → ∀ st len,
      cwB Q read g ⟨0 + c, st, len⟩ = cwT Q read (g ++ g) ⟨0 + c, st, len⟩ := by
    intro c hc st len
    rw [Nat.zero_add, cwT_app_left Q read g _ (by simp only; omega)]
    unfold cwB; rw [if_pos (by simp only; omega)]
  have hcw2 : ∀ c, c < gbs.size → ∀ st len,
      cwB Q read g ⟨gbs.size + c, st, len⟩ = cwT Q (revComp read) (g ++ g) ⟨gbs.size + c, st, len⟩ := by
    intro c hc st len
    rw [hn, cwT_app_right]
    unfold cwB; rw [if_neg (by simp only; omega)]
    simp
  generalize hLs : R.size / (R.size / 25) = Ls at o1 o2 hps hpr
  obtain ⟨S2, i2, s2', p2, c2⟩ := kbFold Q read g gbs hg ix G offs hcat R read hr 0 (Or.inl rfl) hcw1 hm hsb
    ps Ls hLs.symm (fun j hj => by rw [hps]; exact prepG_get ix R _ _ j hj) (hlk R) ord1 nd1 lt1 len1 s1
    (List.range gbs.size) S b (fun c hc => List.mem_range.mp hc) o1 i1 st1
  simp only [Nat.zero_add] at i2 p2 c2
  generalize (List.range gbs.size).foldl (fun b c => chromKBS R (gbs ++ gbs) c Q s1.acc[c]! s1.J b) b = b1 at i2 p2 c2
  obtain ⟨S3, i3, s3, -, c3⟩ := kbFold Q read g gbs hg ix G offs hcat (revCompB R) (revComp read) hrr gbs.size
    (Or.inr rfl) hcw2 (by rw [hsz]; exact hm) (by rw [hsz]; exact hsb) pr Ls (by rw [hsz, hLs])
    (fun j hj => by rw [hpr]; rw [hsz] at hj; exact prepG_get ix _ _ _ j hj) (hlk _) ord2 nd2
    (by rw [hsz]; exact lt2) (by rw [hsz]; exact len2) s2
    (List.range gbs.size) S2 b1 (fun c hc => List.mem_range.mp hc) (o2.mono Q g gbs ix G offs _ _ _ Ls pr s2') i2
    (by
      rcases st2 with h | h
      · left; have := sbound_mono (min b1.pen Q) (min b.pen Q) (by omega); omega
      · right; exact h)
  refine ⟨S3, i3, fun w hw => ?_⟩
  have hw2 := cwB_chr_lt Q read g w hw
  by_cases hwc : w.chr < gbs.size
  · exact s3 w (c2 w.chr (List.mem_range.mpr hwc) w rfl hw)
  · exact c3 (w.chr - gbs.size) (List.mem_range.mpr (by omega)) w (by omega) hw

set_option maxHeartbeats 1000000 in
/-- **Both strands, tie cut.**  `mapChromsGBT` ends with the invariant over a set containing every
virtual hit (the statement of `mapChromsGB_inv`). -/
theorem mapChromsGBT_inv (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25) :
    ∃ S, InvP P (cwB P read g) S (mapChromsGBT P ix G offs gbs R) ∧ ∀ w, cwB P read g w ≤ P → S w := by
  have hn : gbs.size = g.length := hg.1
  have hrr := revCompB_encodes R read hr
  have hcw1 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨0 + c, st, len⟩ = cwT P read (g ++ g) ⟨0 + c, st, len⟩ := by
    intro c hc st len
    rw [Nat.zero_add, cwT_app_left P read g _ (by simp only; omega)]
    unfold cwB; rw [if_pos (by simp only; omega)]
  have hcw2 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨gbs.size + c, st, len⟩ = cwT P (revComp read) (g ++ g) ⟨gbs.size + c, st, len⟩ := by
    intro c hc st len
    rw [hn, cwT_app_right]
    unfold cwB; rw [if_neg (by simp only; omega)]
    simp
  unfold mapChromsGBT
  simp only [revCompB2_eq]
  generalize hLs : R.size / (R.size / 25) = Ls
  generalize hps : prepG ix R (R.size / 25) Ls = ps
  generalize hpr : prepG ix (revCompB R) (R.size / 25) Ls = pr
  obtain ⟨nd1, lt1, len1⟩ := ordG_spec (ps.map (LookG.size ix)) (R.size / 25)
  obtain ⟨nd2, lt2, len2⟩ := ordG_spec (pr.map (LookG.size ix)) (R.size / 25)
  generalize ordG (ps.map (LookG.size ix)) (R.size / 25) = ord1 at nd1 lt1 len1
  generalize ordG (pr.map (LookG.size ix)) (R.size / 25) = ord2 at nd2 lt2 len2
  obtain ⟨S1, i1, -, -, o1, o2, l1, l2⟩ := ilGT_ok P read g gbs hg ix G offs R (revCompB R) read (revComp read)
    hr hrr hcw1 hcw2 Ls ps pr ord1 ord2 (2 * (R.size / 25) + 1) _ _ (initP P) (fun _ => False)
    (gsInit_ok P g gbs ix G offs R read 0 Ls ps ord1) (gsInit_ok P g gbs ix G offs (revCompB R) (revComp read) gbs.size Ls pr ord2)
    (inv_initP P (cwB P read g)) (by simp only []; omega)
  generalize ilGT ix G R (revCompB R) (gbs ++ gbs) offs gbs.size P Ls ps pr (2 * (R.size / 25) + 1) _ _ (initP P) = x
    at i1 o1 o2 l1 l2
  have stopE : ∀ (s : GS) (b : Best), s.liveT P b = false → sbound (min (effP b) P) < s.J.length ∨ s.ord = [] := by
    intro s b h
    unfold GS.liveT at h
    cases ho : s.ord with
    | nil => right; rfl
    | cons j rest =>
      left; rw [ho] at h; simpa using h
  -- no tie within `P`: `effP` stops as `GS.live` does
  have stop : ∀ (s : GS), s.liveT P x.2.2 = false → ¬ (x.2.2.amb = true ∧ x.2.2.pen ≤ P) →
      sbound (min x.2.2.pen P) < s.J.length ∨ s.ord = [] := by
    intro s h hn
    have e : min (effP x.2.2) P = min x.2.2.pen P := by
      unfold effP; split
      · next ha => simp only [Bool.and_eq_true, decide_eq_true_eq] at ha; have := not_and.mp hn ha.1; omega
      · rfl
    rw [← e]; exact stopE s _ h
  have gap := fun Q (hQ : sbound Q < R.size / 25) =>
    gapBoth_inv read g gbs R hg hr ix G offs hcat hlk Q hm hQ ps pr (by rw [← hps, hLs]) (by rw [← hpr, hLs])
      ord1 ord2 nd1 lt1 len1 nd2 lt2 len2 x.1 x.2.1
  rw [← hLs] at o1 o2
  -- the windows within `P`
  let H : Window → Prop := fun w => cwB P read g w ≤ P
  unfold tieCut
  split
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha, hp⟩ := hc
    have hamb : ∃ w, S1 w ∧ w ≠ x.2.2.win ∧ cwB P read g w = x.2.2.pen := (i1.amb hp).mp ha
    have hb1 : InvP P (cwB P read g) H x.2.2 → ∃ S, InvP P (cwB P read g) S x.2.2 ∧ ∀ w, cwB P read g w ≤ P → S w :=
      fun h => ⟨H, h, fun w hw => hw⟩
    -- `b1` itself over every window within `P`, once no window is below its penalty
    have keep : (∀ w, cwB P read g w ≤ P → x.2.2.pen ≤ cwB P read g w) → InvP P (cwB P read g) H x.2.2 := by
      intro hmin
      refine ⟨i1.le, fun w hw => hmin w hw, i1.hit, fun _ => ⟨fun _ => ?_, fun _ => ha⟩⟩
      obtain ⟨w, hw, h1, h2⟩ := hamb
      exact ⟨w, by show cwB P read g w ≤ P; omega, h1, h2⟩
    split
    · next h0 => exact hb1 (keep fun w _ => by omega)
    · next h0 =>
      generalize hQ : x.2.2.pen - 1 = Q
      have hQP : Q ≤ P := by omega
      have hsQ : sbound Q < R.size / 25 := Nat.lt_of_le_of_lt (sbound_mono Q P hQP) hsb
      -- phase 1 left no window below `p`: phase 1's own windows score at least `p`
      have no1 : ∀ w, S1 w → cwB P read g w ≤ Q → False := fun w hw h => by
        have := i1.min w hw; omega
      have o1' := gsOk_cap P Q g gbs ix G offs R read 0 _ ps S1 ord1 x.1 hQP o1
        (fun c hc st len hw h => no1 _ hw (by rw [hcw1 c hc st len]; exact h))
      have o2' := gsOk_cap P Q g gbs ix G offs (revCompB R) (revComp read) gbs.size _ pr S1 ord2 x.2.1 hQP o2
        (fun c hc st len hw h => no1 _ hw (by rw [hcw2 c hc st len]; exact h))
      have hst : ∀ s : GS, (sbound (min (effP x.2.2) P) < s.J.length ∨ s.ord = []) →
          sbound (min (initP Q).pen Q) < s.J.length ∨ s.ord = [] := by
        intro s h
        have e : min (effP x.2.2) P = Q := by
          unfold effP; rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨ha, by omega⟩)]; omega
        rw [e] at h
        rcases h with h | h
        · left
          have : min (initP Q).pen Q = Q := by simp [initP]
          rw [this]; exact h
        · right; exact h
      obtain ⟨S', i', c'⟩ := gap Q hsQ (fun _ => False) (initP Q) o1' o2' (inv_initP Q (cwB Q read g))
        (hst _ (stopE _ _ l1)) (hst _ (stopE _ _ l2))
      simp only []
      generalize ((List.range gbs.size).foldl (fun b c => chromKBS (revCompB R) (gbs ++ gbs) (gbs.size + c) Q x.2.1.acc[c]! x.2.1.J b)
          ((List.range gbs.size).foldl (fun b c => chromKBS R (gbs ++ gbs) c Q x.1.acc[c]! x.1.J b) (initP Q))) = b at i' c'
      -- every window within `Q` is in `S'`; at cap `P` it scores the same
      have low : ∀ w, cwB P read g w ≤ Q → S' w ∧ cwB Q read g w = cwB P read g w := fun w h =>
        have e := (cwB_capT P Q read g w hQP (Or.inl h)).symm
        ⟨c' w (by omega), e⟩
      split
      · next hlt =>
        refine ⟨H, ⟨by omega, fun w hw => ?_, fun _ => ?_, fun _ => ?_⟩, fun w hw => hw⟩
        · by_cases h : cwB P read g w ≤ Q
          · obtain ⟨hs, e⟩ := low w h; have := i'.min w hs; omega
          · omega
        · have := i'.hit (by omega)
          rw [cwB_capT P Q read g b.win hQP (Or.inr (by omega))]; exact this
        · rw [i'.amb (by omega)]
          constructor
          · rintro ⟨w, hw, h1, h2⟩
            have := cwB_capT P Q read g w hQP (Or.inr (by omega))
            exact ⟨w, by show cwB P read g w ≤ P; omega, h1, by omega⟩
          · rintro ⟨w, hw, h1, h2⟩
            obtain ⟨hs, e⟩ := low w (by omega)
            exact ⟨w, hs, h1, by omega⟩
      · next hge =>
        refine hb1 (keep fun w _ => ?_)
        apply Classical.byContradiction; intro hlt
        obtain ⟨hs, e⟩ := low w (by omega)
        have := i'.min w hs; omega
  · next hc =>
    have hn : ¬ (x.2.2.amb = true ∧ x.2.2.pen ≤ P) := fun h => hc (by simp [h.1, h.2])
    exact gap P hsb S1 x.2.2 o1 o2 i1 (stop _ l1 hn) (stop _ l2 hn)

end top

/-! ## The fast searches with the tie cut

Each is its original (`mapChromsGBF`, `mapChromsGBFG`, `mapChromsGBFGP`, `mapChromsGBFGPO`) with the gapped
stages passed to `tieCut`; the equalities are the originals' proofs, under the binder of `tieCut`'s `gap`. -/

/-- `mapChromsGBF` (kernels as parameters, byte chromosomes) with the tie cut. -/
@[specialize] def mapChromsGBFT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (R Rr : ByteArray) (ps pr : Array Pp) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let x := ilGFT kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  tieCut P (fun Q b =>
    let b := (List.range n).foldl (fun b c => chromKBF kf1 R gbs2 c Q x.1.acc[c]! x.1.J b) b
    (List.range n).foldl (fun b c => chromKBF kf2 Rr gbs2 (n + c) Q x.2.1.acc[c]! x.2.1.J b) b) x.2.2

/-- `mapChromsGBFG` (any chromosome representation) with the tie cut. -/
@[specialize] def mapChromsGBFGT {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    [GPk Gt] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array Gt) (R Rr : ByteArray) (ps pr : Array Pp) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let x := ilGFGT kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  tieCut P (fun Q b =>
    let b := (List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c Q x.1.acc[c]! x.1.J b) b
    (List.range n).foldl (fun b c => chromKBFG kf2 Rr gbs2 (n + c) Q x.2.1.acc[c]! x.2.1.J b) b) x.2.2

/-- `mapChromsGBFGT` with both strands' packed reads and seed orders given (`mapChromsGBFGT_eqPO`); the
compiled search of `mateKPPO`. -/
@[specialize] def mapChromsGBFGPOT {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    [GPk Gt] (kf1 kf2 : Ker) (K1 K2 : RP) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array Gt) (R Rr : ByteArray) (ps pr : Array Pp) (o1 o2 : List Nat) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let x := ilGFGT kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨o1, [], Array.replicate n []⟩ ⟨o2, [], Array.replicate n []⟩ (initP P)
  tieCut P (fun Q b =>
    let b := foldUpN (fun b c => chromKBFGK K1 kf1 R gbs2 c Q x.1.acc[c]! x.1.J b) n 0 b
    foldUpN (fun b c => chromKBFGK K2 kf2 Rr gbs2 (n + c) Q x.2.1.acc[c]! x.2.1.J b) n 0 b) x.2.2

theorem mapChromsGBFGT_eqPO {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    [GPk Gt] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array Gt) (R Rr : ByteArray) (ps pr : Array Pp) :
    mapChromsGBFGT kf1 kf2 P ix G offs gbs R Rr ps pr =
      mapChromsGBFGPOT kf1 kf2 (packRP R) (packRP Rr) P ix G offs gbs R Rr ps pr
        (ordG (ps.map (LookG.size ix)) (R.size / 25)) (ordG (pr.map (LookG.size ix)) (R.size / 25)) := by
  unfold mapChromsGBFGT mapChromsGBFGPOT
  simp only [chromKBFG_eqK, foldUpN_eq, List.range_eq_range']

/-- `mapChromsGBKG` with the tie cut: the packed chromosomes `pvs`, word kernels. -/
@[specialize] def mapChromsGBKGT {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    [GPk Gt] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array Gt) (pvs : Array PGen) (R : ByteArray) : Best :=
  let gbs2 := gbs ++ gbs
  let pvs2 := pvs ++ pvs
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  mapChromsGBFGT (kerHKG R K1 gbs2 pvs2) (kerHKG Rr K2 gbs2 pvs2) P ix G offs gbs R Rr
    (prepGK ix R K1 m Ls) (prepGK ix Rr K2 m Ls)

/-- `mapChromsGBK` (byte chromosomes, word kernels) with the tie cut. -/
@[specialize] def mapChromsGBKT {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Best :=
  let gbs2 := gbs ++ gbs
  let pvs2 := pvs ++ pvs
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  mapChromsGBFT (kerHK R K1 gbs2 pvs2) (kerHK Rr K2 gbs2 pvs2) P ix G offs gbs R Rr
    (prepGK ix R K1 m Ls) (prepGK ix Rr K2 m Ls)

theorem mapChromsGBFT_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    mapChromsGBFT (kerH R (gbs ++ gbs)) (kerH (revCompB R) (gbs ++ gbs)) P ix G offs gbs R (revCompB R)
      (prepG ix R (R.size / 25) (R.size / (R.size / 25)))
      (prepG ix (revCompB R) (R.size / 25) (R.size / (R.size / 25))) =
      mapChromsGBT P ix G offs gbs R := by
  unfold mapChromsGBFT mapChromsGBT
  simp only [ilGFT_eq, chromKBF_eq, revCompB2_eq]

theorem mapChromsGBFGT_bytes {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (R Rr : ByteArray) (ps pr : Array Pp) :
    mapChromsGBFGT kf1 kf2 P ix G offs gbs R Rr ps pr = mapChromsGBFT kf1 kf2 P ix G offs gbs R Rr ps pr := by
  simp only [mapChromsGBFGT, mapChromsGBFT, ilGFGT_bytes, chromKBFG_eq]
  rfl

theorem mapChromsGBKGT_unpack {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapChromsGBKGT P ix G offs pgs pgs R = mapChromsGBKT P ix G offs (pgs.map Mz.unpack) pgs R := by
  have hs := sameA_unpack pgs
  have h2 := sameA_append hs sameG_default
  unfold mapChromsGBKGT mapChromsGBKT mapChromsGBFGT
  have ek : ∀ R K, kerHKG R K (pgs ++ pgs) (pgs ++ pgs) = kerHK R K (pgs.map Mz.unpack ++ pgs.map Mz.unpack) (pgs ++ pgs) := by
    intro R K; funext c st len l; rw [kerHKG_same h2, kerHKG_bytes]
  simp only [ek, hs.1, ilGFGT_same h2, chromKBFG_same h2]
  rw [← mapChromsGBFGT_bytes]
  rfl

theorem mapChromsGBKT_eq_rep {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAllK (pvs ++ pvs) (gbs ++ gbs))
    (R : ByteArray) : mapChromsGBKT P ix G offs gbs pvs R = mapChromsGBT P ix G offs gbs R := by
  unfold mapChromsGBKT
  simp only [revCompK_eq, prepGK_eq]
  rw [← mapChromsGBFT_eq]
  congr 1
  · funext c st len l; exact kerHK_eq R _ _ hrep c st len l
  · funext c st len l; exact kerHK_eq (revCompB R) _ _ hrep c st len l

end MapSpec.Fast
