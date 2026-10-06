import FastGenPair
import PairConcatPacked
import MzWord

/-!
# Codec `pairFastGBP`: the general pair mapper over a packed genome

`pairFastGB` (codecs/FastGenPair.lean: any read length, `T = −P`, one index over
the concatenated genome, strands interleaved) with the chromosomes `PGen` views of
one packed genome (`cutAll`) and the minimizer index bundled with that packed
genome (`PkMz`), so no byte genome exists at run time.

* The genome-reading code is generic over `GRead`; `*_same` below: two genome
  arrays with the same bytes (`SameA`) give the same results, for every generic
  def on the path (kernels, band scorer, stages K and B, `mapChromsGB`).
* `PkMz` looks seeds up in its own packed genome (`mzLookSP`), ignoring the byte
  genome argument; `mzLookSP_eq`: it is `mzLookS` on the unpacked genome.

    cutOk G offs ns → Mz.check2P ix G → GenomeBytes ((cutAll G offs ns).map Mz.unpack) g → …
      pairFastGBP P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 = pairSpec sc0 (−P) lo hi g m1 m2
                                                                       (pairFastGBP_mz_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Same bytes, same results -/

/-- Same number of chromosomes, each with the same bytes (also past the end). -/
def SameA {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] (xs : Array G1) (ys : Array G2) : Prop :=
  xs.size = ys.size ∧ ∀ c : Nat, SameG xs[c]! ys[c]!

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] {x : G1} {y : G2} (h : SameG x y)
include h

theorem matchQ_same (R : ByteArray) (s p : Nat) : ∀ k, matchQ R x s p k = matchQ R y s p k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [matchQ, h.2, ih]

theorem nearS_same (R : ByteArray) (s : Nat) : ∀ w lo, nearS R x s lo w = nearS R y s lo w := by
  intro w
  induction w with
  | zero => intro lo; rfl
  | succ w ih => intro lo; simp only [nearS, h.1, matchQ_same h, ih]

theorem seedNear_same (R : ByteArray) (Ls r D j : Nat) : seedNear R x Ls r D j = seedNear R y Ls r D j := by
  simp only [seedNear, nearS_same h, matchQ_same h, h.1]

theorem unlook_same (R : ByteArray) (Ls r D sb : Nat) :
    ∀ us f, unlook R x Ls r D sb us f = unlook R y Ls r D sb us f := by
  intro us
  induction us with
  | nil => intro f; rfl
  | cons j us ih => intro f; simp only [unlook, seedNear_same h, ih]

theorem matchLn_same (R : ByteArray) (s p l : Nat) : ∀ k, matchLn R x s p l k = matchLn R y s p l k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [matchLn, h.2, ih]

theorem nearL_same (R : ByteArray) (s l : Nat) : ∀ w lo, nearL R x s l lo w = nearL R y s l lo w := by
  intro w
  induction w with
  | zero => intro lo; rfl
  | succ w ih => intro lo; simp only [nearL, h.1, matchLn_same h, ih]

theorem fineOk_same (R : ByteArray) (l Ls r D sb : Nat) :
    ∀ k j f, fineOk R x l Ls r D sb j f k = fineOk R y l Ls r D sb j f k := by
  intro k
  induction k with
  | zero => intro j f; rfl
  | succ k ih => intro j f; simp only [fineOk, pieceNear, nearL_same h, matchLn_same h, h.1, ih]

theorem kfilt_same (R : ByteArray) (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) :
    kfilt R x acc us Ls lim b D = kfilt R y acc us Ls lim b D := by
  simp only [kfilt, unlook_same h, fineOk_same h]

theorem stageKS_same (body1 body2 : Nat → Best → Best) (hb : ∀ D b, body1 D b = body2 D b) (R : ByteArray)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (ds : List Nat) (b : Best) :
    stageKS body1 R x acc us Ls lim ds b = stageKS body2 R y acc us Ls lim ds b := by
  simp only [stageKS, kfilt_same h, hb]

theorem gappedPen2_same (r : ByteArray) (st len lim : Nat) : gappedPen2 r x st len lim = gappedPen2 r y st len lim := by
  simp only [gappedPen2, fwdMis_same' h, bwdMis_same' h]

theorem kerG_same (R : ByteArray) (st len lim : Nat) : kerG R x st len lim = kerG R y st len lim := by
  simp only [kerG, hamming_same' h, gappedPen2_same h, h.1]

theorem kerGP_same (R : ByteArray) (st len lim : Nat) (pf pb : Nat × Nat × Nat) :
    kerGP R x st len lim pf pb = kerGP R y st len lim pf pb := by
  simp only [kerGP, hamming_same' h, h.1, gappedPen2P]

theorem filt16_same (R : ByteArray) (st len : Nat) : filt16 R x st len = filt16 R y st len := by
  simp only [filt16, hamming_same' h, fwdMis_same' h, bwdMis_same' h]

theorem twoGapAt_same (R : ByteArray) (st len x1 x2 A B : Nat) :
    twoGapAt R x st len x1 x2 A B = twoGapAt R y st len x1 x2 A B := by
  simp only [twoGapAt, hamming_same' h]

theorem twoGapB_same (R : ByteArray) (st len : Nat) : twoGapB R x st len = twoGapB R y st len := by
  simp only [twoGapB, twoGapAt_same h, fwdMis_same' h, bwdMis_same' h]

theorem twoGapBP_same (R : ByteArray) (st len A B : Nat) : twoGapBP R x st len A B = twoGapBP R y st len A B := by
  simp only [twoGapBP, twoGapAt_same h]

theorem filt16P_same (R : ByteArray) (st len A B f3 e3 : Nat) :
    filt16P R x st len A B f3 e3 = filt16P R y st len A B f3 e3 := by
  simp only [filt16P, hamming_same' h]

theorem fwdProf_same (R : ByteArray) (st : Nat) : fwdProf R x st = fwdProf R y st := by
  simp only [fwdProf, fwdMis_same' h]

theorem bwdProf_same (R : ByteArray) (E : Nat) : bwdProf R x E = bwdProf R y E := by
  simp only [bwdProf, bwdMis_same' h]

theorem cellVals_same (sc : Scoring) (rb : ByteArray) (i p : Nat) (lastRow atEnd : Bool) (dN xX yY : Int) :
    cellVals sc rb x i p lastRow atEnd dN xX yY = cellVals sc rb y i p lastRow atEnd dN xX yY := by
  simp only [cellVals, h.2]

theorem bandLoop_same (sc : Scoring) (T To : Int) (rb : ByteArray) (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ d k p N X Y alive, hi + 1 - k = d →
      bandLoop sc T To rb x e i lastRow hi k p N X Y alive = bandLoop sc T To rb y e i lastRow hi k p N X Y alive := by
  intro d
  induction d with
  | zero => intro k p N X Y alive hd; unfold bandLoop; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro k p N X Y alive hd
    unfold bandLoop
    have ih' := fun p N X Y alive => ih (k + 1) p N X Y alive (by omega)
    simp only [cellVals_same h, ih']

theorem bandLoop_same' (sc : Scoring) (T To : Int) (rb : ByteArray) (e i : Nat) (lastRow : Bool) (hi k p : Nat)
    (N X Y : Array Int) (alive : Bool) :
    bandLoop sc T To rb x e i lastRow hi k p N X Y alive = bandLoop sc T To rb y e i lastRow hi k p N X Y alive :=
  bandLoop_same h sc T To rb e i lastRow hi _ k p N X Y alive rfl

theorem bandRows2_same (sc : Scoring) (T : Int) (B : Nat) (rb : ByteArray) (e : Nat) :
    ∀ i N X Y, bandRows2 sc T B rb x e i N X Y = bandRows2 sc T B rb y e i N X Y := by
  intro i
  induction i with
  | zero => intro N X Y; rw [bandRows2, bandRows2, bandLoop_same' h]
  | succ i ih => intro N X Y; rw [bandRows2, bandRows2, bandLoop_same' h]; simp only [ih]

theorem bandEnd2_same (sc : Scoring) (T : Int) (B : Nat) (rb : ByteArray) (e : Nat) :
    bandEnd2 sc T B rb x e = bandEnd2 sc T B rb y e := by
  simp only [bandEnd2, bandRows2_same h]

theorem bandRowsP_same (T : Int) (B : Nat) (sp : Nat → Bool) (rb : ByteArray) (e : Nat) :
    ∀ i N X Y, bandRowsP T B sp rb x e i N X Y = bandRowsP T B sp rb y e i N X Y := by
  intro i
  induction i with
  | zero => intro N X Y; rw [bandRowsP, bandRowsP, bandLoop_same' h]
  | succ i ih => intro N X Y; rw [bandRowsP, bandRowsP, bandLoop_same' h]; simp only [ih]

theorem bandEndP_same (T : Int) (B : Nat) (sp : Nat → Bool) (rb : ByteArray) (e : Nat) :
    bandEndP T B sp rb x e = bandEndP T B sp rb y e := by
  simp only [bandEndP, bandRowsP_same h]

theorem bandRowsC_same (T : Int) (B : Nat) (cnt : Array Nat) (rb : ByteArray) (e : Nat) :
    ∀ i N X Y, bandRowsC T B cnt rb x e i N X Y = bandRowsC T B cnt rb y e i N X Y := by
  intro i
  induction i with
  | zero => intro N X Y; rw [bandRowsC, bandRowsC]; simp only [bandLoop_same' h]
  | succ i ih => intro N X Y; rw [bandRowsC, bandRowsC]; simp only [bandLoop_same' h, ih]

theorem bandEndC_same (T : Int) (B : Nat) (cnt : Array Nat) (rb : ByteArray) (e : Nat) :
    bandEndC T B cnt rb x e = bandEndC T B cnt rb y e := by
  simp only [bandEndC, bandRowsC_same h]

theorem bandLoopB_same (M : Nat) (uN uG : Int) (rb : ByteArray) (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ d k p N X Y alive, hi + 1 - k = d →
      bandLoopB M uN uG rb x e i lastRow hi k p N X Y alive = bandLoopB M uN uG rb y e i lastRow hi k p N X Y alive := by
  intro d
  induction d with
  | zero => intro k p N X Y alive hd; unfold bandLoopB; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro k p N X Y alive hd
    unfold bandLoopB
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [cellB, h.2]
    exact ih (k + 1) _ _ _ _ _ (by omega)

theorem bandRowsCB_same (T : Int) (B : Nat) (cnt : Array Nat) (M : Nat) (rb : ByteArray) (e : Nat) :
    ∀ i N X Y, bandRowsCB T B cnt M rb x e i N X Y = bandRowsCB T B cnt M rb y e i N X Y := by
  intro i
  induction i with
  | zero => intro N X Y; rw [bandRowsCB, bandRowsCB]; simp only [bandLoopB_same h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl]
  | succ i ih =>
    intro N X Y; rw [bandRowsCB, bandRowsCB]
    simp only [bandLoopB_same h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl, ih]

theorem bandEndCB_same (T : Int) (B : Nat) (cnt : Array Nat) (M : Nat) (rb : ByteArray) (e : Nat) :
    bandEndCB T B cnt M rb x e = bandEndCB T B cnt M rb y e := by
  simp only [bandEndCB, bandRowsCB_same h]

theorem blockEq_same (R : ByteArray) (a p : Nat) : ∀ k, blockEq R x a p k = blockEq R y a p k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [blockEq, h.2, ih]

theorem anyCopy_same (R : ByteArray) (a : Nat) (lo : Int) : ∀ t, anyCopy R x a lo t = anyCopy R y a lo t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp only [anyCopy, h.1, blockEq_same h, ih]

theorem spoiledArr_same (R : ByteArray) (D d B : Nat) : spoiledArr R x D d B = spoiledArr R y D d B := by
  simp only [spoiledArr, anyCopy_same h]

end

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1} {ys : Array G2}
  (h : SameA xs ys)
include h

theorem bandScore_same (sc : Scoring) (T : Int) (B : Nat) (rb : ByteArray) (w : Window) :
    bandScore sc T B rb xs w = bandScore sc T B rb ys w := by
  unfold bandScore
  by_cases hc : w.chr < xs.size
  · have hc' : w.chr < ys.size := h.1 ▸ hc
    rw [dif_pos hc, dif_pos hc', ← getElem!_pos xs w.chr hc, ← getElem!_pos ys w.chr hc',
      (h.2 w.chr).1, bandEnd2_same (h.2 w.chr)]
  · rw [dif_neg hc, dif_neg (h.1 ▸ hc)]

theorem bandPen_same (P : Nat) (R : ByteArray) (w : Window) : bandPen P R xs w = bandPen P R ys w := by
  simp only [bandPen, bandScore_same h]

theorem ker16_same (R : ByteArray) (c st len : Nat) : ker16 R xs c st len = ker16 R ys c st len := by
  simp only [ker16, kerG_same (h.2 c), (h.2 c).1, hamming_same' (h.2 c), twoGapB_same (h.2 c), filt16_same (h.2 c),
    bandPen_same h]

theorem kerH_same (R : ByteArray) (c st len l : Nat) : kerH R xs c st len l = kerH R ys c st len l := by
  simp only [kerH, kerG_same (h.2 c), ker16_same h]

theorem addK_same (R : ByteArray) (c lim : Nat) (st len : Int) (b : Best) :
    addK R xs c lim st len b = addK R ys c lim st len b := by
  simp only [addK, kerH_same h]

theorem stageK_same (R : ByteArray) (c lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (b : Best) :
    stageK R xs c lim shs ds b = stageK R ys c lim shs ds b := by
  simp only [stageK, addK_same h]

theorem ker16P_same (R : ByteArray) (c st len : Nat) (pf pb : Nat × Nat × Nat) :
    ker16P R xs c st len pf pb = ker16P R ys c st len pf pb := by
  simp only [ker16P, kerGP_same (h.2 c), (h.2 c).1, hamming_same' (h.2 c), twoGapBP_same (h.2 c),
    filt16P_same (h.2 c), bandPen_same h]

theorem kerHP_same (R : ByteArray) (c st len l : Nat) (pf pb : Nat × Nat × Nat) :
    kerHP R xs c st len l pf pb = kerHP R ys c st len l pf pb := by
  simp only [kerHP, kerGP_same (h.2 c), ker16P_same h]

theorem addKP_same (R : ByteArray) (c lim : Nat) (st len : Int) (pf pb : Nat × Nat × Nat) (b : Best) :
    addKP R xs c lim st len pf pb b = addKP R ys c lim st len pf pb b := by
  simp only [addKP, kerHP_same h]

theorem stageKP_same (R : ByteArray) (c lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (b : Best) :
    stageKP R xs c lim shs ds b = stageKP R ys c lim shs ds b := by
  simp only [stageKP, addKP_same h, fwdProf_same (h.2 c), bwdProf_same (h.2 c)]

theorem bandEndAt_same (P : Nat) (R : ByteArray) (c D : Nat) (cnt : Array Nat) (bb : Int) :
    bandEndAt P R xs c D cnt bb = bandEndAt P R ys c D cnt bb := by
  simp only [bandEndAt, bandEndC_same (h.2 c), bandEndCB_same (h.2 c)]

theorem stageB_same (P : Nat) (R : ByteArray) (c : Nat) (shs : List (Int × Int)) (bs : List Int) (ds : List Nat)
    (b : Best) : stageB P R xs c shs bs ds b = stageB P R ys c shs bs ds b := by
  have e : ∀ Pc, stageBD Pc R xs c shs = stageBD Pc R ys c shs := by
    intro Pc
    funext D cnt b bb
    have e2 : addBS Pc R xs c D = addBS Pc R ys c D := by
      funext opt b sh; simp only [addBS, (h.2 c).1]
    simp only [stageBD, bandEndAt_same h, e2]
  simp only [stageB, e, spoiledArr_same (h.2 c)]

theorem chromKB_same (R : ByteArray) (c P : Nat) (acc : List (Array Nat)) (b1 : Best) :
    chromKB R xs c P acc b1 = chromKB R ys c P acc b1 := by
  unfold chromKB
  by_cases h16 : 16 ≤ min (min P 16) (min b1.pen P) <;>
    simp only [h16, if_true, if_false, decide_true, decide_false, stageKP_same h, stageK_same h, stageB_same h]

theorem chromKBS_same (R : ByteArray) (c P : Nat) (acc : List (Array Nat)) (J : List Nat) (b1 : Best) :
    chromKBS R xs c P acc J b1 = chromKBS R ys c P acc J b1 := by
  unfold chromKBS
  by_cases h16 : 16 ≤ min (min P 16) (min b1.pen P) <;>
    simp only [h16, if_true, if_false, decide_true, decide_false,
      stageKS_same (h.2 c) _ _ (fun D b => stageKP_same h _ _ _ _ _ b),
      stageKS_same (h.2 c) _ _ (fun D b => stageK_same h _ _ _ _ _ b),
      stageKS_same (h.2 c) _ _ (fun D b => stageB_same h _ _ _ _ _ _ b)]

end

/-! ## The pair mapper's search -/

theorem sameA_append {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1} {ys : Array G2}
    (h : SameA xs ys) (hd : SameG (default : G1) (default : G2)) : SameA (xs ++ xs) (ys ++ ys) := by
  have hs := h.1
  refine ⟨by simp [h.1], fun c => ?_⟩
  by_cases h1 : c < xs.size
  · rw [getElem!_pos (xs ++ xs) c (by simp; omega), getElem!_pos (ys ++ ys) c (by simp; omega),
      Array.getElem_append_left h1, Array.getElem_append_left (h.1 ▸ h1), ← getElem!_pos xs c h1,
      ← getElem!_pos ys c (h.1 ▸ h1)]
    exact h.2 c
  · by_cases h2 : c < 2 * xs.size
    · rw [getElem!_pos (xs ++ xs) c (by simp; omega), getElem!_pos (ys ++ ys) c (by simp; omega),
        Array.getElem_append_right (by omega), Array.getElem_append_right (by omega)]
      have := h.2 (c - xs.size)
      rw [getElem!_pos xs _ (by omega), getElem!_pos ys _ (by omega)] at this
      simpa [h.1] using this
    · rw [getElem!_neg (xs ++ xs) c (by simp; omega), getElem!_neg (ys ++ ys) c (by simp; omega)]
      exact hd

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1} {ys : Array G2}
  (h : SameA xs ys) {L Pp : Type} [LookG L Pp] [Inhabited Pp] {ix : L} {G G' : ByteArray}
  (hl : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p)
include h hl

theorem gsAdv_same (R : ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) :
    s.adv ix G R xs offs n t P Ls ps b = s.adv ix G' R ys offs n t P Ls ps b := by
  have e : ∀ bs a, advC R xs offs t P bs a = advC R ys offs t P bs a := by
    intro bs a; funext r c; simp only [advC, (h.2 _).1, addK_same h]
  obtain ⟨ord, J, acc⟩ := s
  cases ord with
  | nil => rfl
  | cons j rest => simp only [GS.adv, hl, e]

theorem ilG_same (R1 R2 : ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilG ix G R1 R2 xs offs n P Ls ps1 ps2 f s1 s2 b = ilG ix G' R1 R2 ys offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilG, gsAdv_same h hl, ih]

end

theorem mapChromsGB_same {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1}
    {ys : Array G2} (h : SameA xs ys) (hd : SameG (default : G1) (default : G2)) {L Pp : Type} [LookG L Pp]
    [Inhabited Pp] (P : Nat) (ix : L) {G G' : ByteArray}
    (hl : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (offs : Array Nat) (R : ByteArray) :
    mapChromsGB P ix G offs xs R = mapChromsGB P ix G' offs ys R := by
  have h2 := sameA_append h hd
  simp only [mapChromsGB, h.1, ilG_same h2 hl, chromKBS_same h2]

/-! ## Minimizer index bundled with its packed genome -/

/-- `mzLookS` reading a packed genome. -/
def mzLookSP (ix : Mz.MzIdx) (G : PGen) (R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupPW ix G R s p base 0 else lookupSeedAP ix G R s base 0

/-- A minimizer index and the packed genome it indexes. -/
abbrev PkMz := Mz.MzIdx × PGen

/-- Lookups read the bundled packed genome (the byte genome argument is ignored). -/
instance : LookG PkMz MzP := ⟨fun ix => mzPrep ix.1, fun ix => mzSize ix.1, fun ix _ R s base p => mzLookSP ix.1 ix.2 R s base p⟩

theorem mzLookSP_eq {P : PGen} {G : ByteArray} (h : Rep P G) (ix : Mz.MzIdx) (R : ByteArray) (s base : Nat) (p : MzP) :
    mzLookSP ix P R s base p = mzLookS ix G R s base p := by
  simp only [mzLookSP, lookupPW_eq, mzLookS, lookupPP, lookupP, lookupSeedAP, lookupSeedA, lookupCodeAP, lookupCodeA,
    fun ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =>
      scanAP_eq h ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit _ t acc rfl,
    fun ix R side d0 s base bit i acc => scanEdgeAP_eq h ix R side d0 s base bit _ i acc rfl,
    fun ix R s base bit i acc => scanInsideAP_eq h ix R s base bit _ i acc rfl]

/-! ## Algorithm -/

/-- `mapFastGB` on the packed chromosomes `pgs`, lookups in the bundled genome. -/
def mapFastGBP (P : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    Option (Placement × Int) :=
  if fastT P R then decodeP pgs.size P (mapChromsGB P ix ByteArray.empty offs pgs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB (pgs.map Mz.unpack)) (decodeBytes R)

/-- A pair from its mates' answers, mate 2 mapped only when mate 1 has an answer
(the pair needs both): `pairLazy_match`. -/
@[inline] def pairLazy (lo hi : Nat) (m1 : Option (Placement × Int)) (m2 : Unit → Option (Placement × Int)) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match m1 with
  | none => none
  | some a =>
    match m2 () with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

theorem pairLazy_match (lo hi : Nat) (m1 m2 : Option (Placement × Int)) :
    pairLazy lo hi m1 (fun _ => m2) = (match m1, m2 with
      | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
      | _, _ => none) := by
  cases m1 <;> cases m2 <;> rfl

def pairFastGBP (P lo hi : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  pairLazy lo hi (mapFastGBP P ix offs pgs R1) (fun _ => mapFastGBP P ix offs pgs R2)

/-! ## Theorem -/

theorem sameA_unpack (pgs : Array PGen) : SameA pgs (pgs.map Mz.unpack) := by
  refine ⟨by simp, fun c => ?_⟩
  by_cases hc : c < pgs.size
  · rw [show (pgs.map Mz.unpack)[c]! = Mz.unpack pgs[c]! by simp [hc]]
    exact (Mz.rep_unpack _).same
  · rw [getElem!_neg pgs c (by omega), getElem!_neg _ c (by simp; omega)]
    exact ⟨rfl, fun i => by simp only [GRead.get_bytes]; rw [get!_out _ i (Nat.zero_le _)]; rfl⟩

theorem sameG_default : SameG (default : PGen) (default : ByteArray) :=
  ⟨rfl, fun i => by simp only [GRead.get_bytes]; rw [get!_out _ i (Nat.zero_le _)]; rfl⟩

theorem mapFastGBP_eq (P : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapFastGBP P ix offs pgs R = mapFastGB P ix (Mz.unpack ix.2) offs (pgs.map Mz.unpack) R := by
  unfold mapFastGBP mapFastGB
  rw [mapChromsGB_same (sameA_unpack pgs) sameG_default P ix (G := ByteArray.empty) (G' := Mz.unpack ix.2)
    (fun _ _ _ _ => rfl)]
  simp

/-- **Packed genome + one minimizer index, general path, proper pairs at `T = −P`.** -/
theorem pairFastGBP_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairFastGBP P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  have e : pairFastGBP P lo hi (ix, G) offs (cutAll G offs ns) R1 R2 =
      pairFastGB P lo hi ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R1 R2 := by
    unfold pairFastGBP pairFastGB; rw [pairLazy_match, mapFastGBP_eq, mapFastGBP_eq]; rfl
  rw [e]
  refine pairFastGB_eq_pairSpec P lo hi g m1 m2 _ R1 R2 _ _ offs hg h1 h2 (catOk_cut G offs ns hcut) ?_
  intro R' s base hs
  show LookOkS (Mz.unpack G) R' s base 0 (mzLookSP ix G R' s base (mzPrep ix (seedHashAt R' s)))
  rw [mzLookSP_eq (Mz.rep_unpack G)]
  exact mzLookS_ok ix _ R' s base (by rw [← Mz.check2_eq, ← Mz.check2P_eq (Mz.rep_unpack G)]; exact hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastGBP_eq
#print axioms MapSpec.Fast.pairFastGBP_mz_eq_pairSpec
