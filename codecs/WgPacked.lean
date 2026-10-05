import FastGenPairPacked
import FastGenK250
import PairDispatch
import MzCheckPar
import MzPacked
import MzView

/-!
# Codec `pairDispatchKP`: whole genome held once, 2-bit, word kernels, length dispatch

For the whole genome (bench/WholeGenome.lean): no byte genome at run time.  The
genome is one `PGen` (`G`), chromosomes are views of it (`cutAll`), the minimizer
index is bundled with it (`PkMz`) and checked on it (`Mz.check3P`, parallel).

* `Mz.check3P ix G P = Mz.check2P ix G`                                   (check3P_eq)
* `pairDispatchP`: `pairDispatch` (each mate at `T = −16` from 150 letters,
  `−12` from 100) on the packed genome (`mapFastGBP`)                     (pairDispatchP_mz_eq)
* the word kernels (`kerHK`, codecs/FastGenK250.lean) with the chromosomes'
  bytes read from the `PGen` views as well (`…G` copies, generic over `GRead`):
  `pairFastGBKP` (one `T`) and `pairDispatchKP` (length dispatch)         (pairFastGBKP_mz_eq_pairSpec,
                                                                            pairDispatchKP_mz_eq)
Hypotheses, all runtime-checked: `cutOk G offs ns`, `Mz.check2P ix G`; the genome
is what the views spell (`GenomeBytes ((cutAll G offs ns).map Mz.unpack) g`).
-/

namespace MapSpec.Mz

/-- `checkSoundP` on `P` tasks. -/
def checkSoundParP (ix : MzIdx) (G : Fast.PGen) (P : Nat) : Bool :=
  let N := 2 ^ ix.B
  let P := max P 1
  let ch := (N + P - 1) / P
  let tasks := (List.range P).map fun j =>
    Task.spawn (prio := .dedicated) fun _ => checkSoundP ix G (min ((j + 1) * ch) N - j * ch) (j * ch)
  tasks.all (·.get)

/-- `check2P` with the per-entry pass on `P` tasks, run beside the sequential passes. -/
def check3P (ix : MzIdx) (G : Fast.PGen) (P : Nat) : Bool :=
  let seq := Task.spawn (prio := .dedicated) fun _ =>
    (let s := rollToP G (q - 1); compRP ix G ix.offs 0 (G.n + 1 - q) 0 s.1 s.2) &&
      checkRunsP ix G ix.nr 0 && checkCoverP ix G 0 G.n 0
  checkParams ix && checkSoundParP ix G P && seq.get

theorem check3P_eq (ix : MzIdx) (G : Fast.PGen) (P : Nat) : check3P ix G P = check2P ix G := by
  have h := rep_unpack G
  have e : checkSoundParP ix G P = checkSoundPar ix (unpack G) P := by
    simp only [checkSoundParP, checkSoundPar, soundChunk, checkSoundP_eq h]
  rw [check2P_eq h, check2_eq, ← check3_eq ix (unpack G) P]
  simp only [check3P, check3, e, rollToP_eq h, compRP_eq h, checkRunsP_eq h, checkCoverP_eq h, h.1]
  show _ = (checkParams ix && checkSoundPar ix (unpack G) P && _ && _ && _)
  simp only [Bool.and_assoc]
  rfl

end MapSpec.Mz

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- A mapper whose index ignores `G` gives the same answers for any `G`. -/
theorem mapFastGB_congrG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (P : Nat) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) : mapFastGB P ix G offs gbs R = mapFastGB P ix G' offs gbs R := by
  simp only [mapFastGB, mapChromsGB, ilG_congrG ix G G' hG]

/-! ## Length dispatch on the packed genome -/

/-- `pairDispatch` on the packed chromosomes `pgs` (lookups in the bundled genome). -/
def pairDispatchP (lo hi : Nat) (ix : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGBP (penOf R1) ix offs pgs R1, mapFastGBP (penOf R2) ix offs pgs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem lookOk_pk (ix : Mz.MzIdx) (G : PGen) (hchk : Mz.check2P ix G = true) :
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS (Mz.unpack G) R' s base 0
        (LookG.look ((ix, G) : PkMz) (Mz.unpack G) R' s base (LookG.prep ((ix, G) : PkMz) (seedHashAt R' s))) := by
  intro R' s base _
  show LookOkS (Mz.unpack G) R' s base 0 (mzLookSP ix G R' s base (mzPrep ix (seedHashAt R' s)))
  rw [mzLookSP_eq (Mz.rep_unpack G)]
  exact mzLookS_ok ix _ R' s base (by rw [← Mz.check2_eq, ← Mz.check2P_eq (Mz.rep_unpack G)]; exact hchk)

/-- **Packed genome, length dispatch** (`T = −16` / `−12` per mate). -/
theorem pairDispatchP_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairDispatchP lo hi (ix, G) offs (cutAll G offs ns) R1 R2 =
      pairSpecT (-(penOf R1 : Int)) (-(penOf R2 : Int)) lo hi g m1 m2 := by
  have e : pairDispatchP lo hi (ix, G) offs (cutAll G offs ns) R1 R2 =
      pairDispatch lo hi ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R1 R2 := by
    unfold pairDispatchP pairDispatch; rw [mapFastGBP_eq, mapFastGBP_eq]; rfl
  rw [e]
  exact pairDispatch_eq_pairSpecT lo hi g m1 m2 _ R1 R2 _ _ offs hg h1 h2 (catOk_cut G offs ns hcut)
    (lookOk_pk ix G hchk)

/-! ## Word kernels with the chromosome bytes read through `GRead` (copies) -/

section
variable {Gt : Type} [GRead Gt]

def gappedPen3G (r : ByteArray) (g : Gt) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdMis r g st (n - skip) 0 1
  let E1 := bwdMis r g st len skip n 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdMis r g st (n - skip) 0 2
  let E2 := bwdMis r g st len skip n 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdMis r g st (n - skip) 0 3
  let E3 := bwdMis r g st len skip n 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

def kerG3G (R : ByteArray) (G : Gt) (st len lim : Nat) : Nat :=
  if st + len ≤ GRead.size G then
    if len = R.size then
      let h := hamming R G st (lim / 4) 0 R.size 0
      if 4 * h ≤ lim then 4 * h else lim + 1
    else gappedPen3G R G st len lim
  else lim + 1

@[inline] def fwdLG (R : ByteArray) (G : Gt) (K : RP) (P : PGen) (st stop k : Nat) : Nat :=
  let f := fwdMis R G st (min stop pre) 0 k
  if f < min stop pre then f
  else if K.ok && decide (stop ≤ R.size) && winOk P st stop then fwdA K.w P.w (P.o + st) stop k
  else fwdMis R G st stop 0 k

@[inline] def bwdLG (R : ByteArray) (G : Gt) (K : RP) (P : PGen) (st len lo k : Nat) : Nat :=
  let n := R.size
  let b := bwdMis R G st len (max lo (n - pre)) n k
  if max lo (n - pre) < b then b
  else if K.ok && decide (n ≤ st + len) && decide (lo < n) && winOk P (st + len - n + lo) (n - lo) then
    bwdA K.w P.w (P.o + (st + len - n)) lo n k
  else bwdMis R G st len lo n k

@[inline] def gappedLG (R : ByteArray) (G : Gt) (K : RP) (P : PGen) (st len lim : Nat) : Nat :=
  let n := R.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdLG R G K P st (n - skip) 1
  let E1 := bwdLG R G K P st len skip 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdLG R G K P st (n - skip) 2
  let E2 := bwdLG R G K P st len skip 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdLG R G K P st (n - skip) 3
  let E3 := bwdLG R G K P st len skip 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

def kerGKG (R : ByteArray) (K : RP) (G : Gt) (P : PGen) (st len lim : Nat) : Nat :=
  if len = R.size then
    if lim / 4 < hamming R G st (lim / 4) 0 (min R.size pre) 0 then lim + 1
    else if wordOk R K P st len then
      let h := hamA K.w P.w (P.o + st) (lim / 4) R.size
      if 4 * h ≤ lim then 4 * h else lim + 1
    else kerG3G R G st len lim
  else if st + len ≤ P.n then gappedLG R G K P st len lim
  else lim + 1

@[inline] def twoGapCG (R : ByteArray) (G : Gt) (st len : Nat) : Bool :=
  let n := R.size
  let A := fwdMis R G st n 0 1
  let B := bwdMis R G st len 0 n 1
  (len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0)

variable [Inhabited Gt]

@[inline] def twoGap16G (R : ByteArray) (gbs : Array Gt) (c st len : Nat) : Nat :=
  let G := gbs[c]!
  if !twoGapCG R G st len then 17
  else if twoGapB R G st len then 16
  else bandPen 16 R gbs ⟨c, st, len⟩

def ker16KG (R : ByteArray) (K : RP) (gbs : Array Gt) (pvs : Array PGen) (c st len : Nat) : Nat :=
  if gbs.size ≤ c then ker16 R gbs c st len
  else if st + len ≤ GRead.size gbs[c]! then
    let r := kerGKG R K gbs[c]! pvs[c]! st len 16
    if r ≤ 16 then r
    else if len = R.size ∨ len = R.size + 2 ∨ len + 2 = R.size then twoGap16G R gbs c st len
    else 17
  else 17

@[inline] def kerHKG (R : ByteArray) (K : RP) (gbs : Array Gt) (pvs : Array PGen) (c st len l : Nat) : Nat :=
  if l ≤ 15 then kerGKG R K gbs[c]! pvs[c]! st len l else ker16KG R K gbs pvs c st len

/-! ### The search with the kernel as a parameter, chromosomes through `GRead` -/

def chromKBFG (kf : Ker) (R : ByteArray) (gbs : Array Gt) (c P : Nat) (acc : List (Array Nat)) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageKF kf R.size c lim (shapesKT Q1)
        (diagsB acc (acc.length - sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int))))
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

@[inline] def advCFG (kf : Ker) (n : Nat) (gbs2 : Array Gt) (offs : Array Nat) (t P bs : Nat) (a : Array Nat)
    (r : Array (List (Array Nat)) × Best) (c : Nat) : Array (List (Array Nat)) × Best :=
  let sl := sliceG a bs offs[c]! (GRead.size gbs2[t + c]!)
  (r.1.set! c (sl :: r.1[c]!),
    sl.foldl (fun b e => addKF kf (t + c) (min P 16) ((e / 16 : Nat) - (n : Int)) n b) r.2)

@[inline] def GS.advFG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf : Ker) (ix : L) (G R : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) : GS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := (List.range n).foldl (advCFG kf R.size gbs2 offs t P (R.size - j * Ls)
      (LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!)) (s.acc, b)
    (⟨rest, j :: s.J, r.1⟩, r.2)

@[specialize] def ilGFG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.live P b
    if s1.live P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advFG kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGFG kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advFG kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGFG kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

@[specialize] def mapChromsGBFG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array Gt) (R Rr : ByteArray) (ps pr : Array Pp) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let x := ilGFG kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  let b := (List.range n).foldl (fun b c => chromKBFG kf1 R gbs2 c P x.1.acc[c]! b) x.2.2
  (List.range n).foldl (fun b c => chromKBFG kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! b) b

/-- `mapChromsGBK` with the chromosomes `gbs` of any representation. -/
@[specialize] def mapChromsGBKG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array Gt) (pvs : Array PGen) (R : ByteArray) : Best :=
  let gbs2 := gbs ++ gbs
  let pvs2 := pvs ++ pvs
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  mapChromsGBFG (kerHKG R K1 gbs2 pvs2) (kerHKG Rr K2 gbs2 pvs2) P ix G offs gbs R Rr
    (prepGK ix R K1 m Ls) (prepGK ix Rr K2 m Ls)

end

/-- One read, word kernels, packed chromosomes `pgs` only (they are also the kernels' words). -/
def mapFastGBKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (Placement × Int) :=
  if fastT P R then decodeP pgs.size P (mapChromsGBKG P ix G offs pgs pgs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB (pgs.map Mz.unpack)) (decodeBytes R)

/-- Proper pairs at `T = −P`, word kernels, packed genome. -/
def pairFastGBKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGBKP P ix G offs pgs R1, mapFastGBKP P ix G offs pgs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-- Length dispatch, word kernels, packed genome. -/
def pairDispatchKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGBKP (penOf R1) ix G offs pgs R1, mapFastGBKP (penOf R2) ix G offs pgs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-! ## Proofs: same bytes, same kernels -/

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] {x : G1} {y : G2} (h : SameG x y)
include h

theorem gappedPen3G_same (r : ByteArray) (st len lim : Nat) :
    gappedPen3G r x st len lim = gappedPen3G r y st len lim := by
  simp only [gappedPen3G, fwdMis_same' h, bwdMis_same' h]

theorem kerG3G_same (R : ByteArray) (st len lim : Nat) : kerG3G R x st len lim = kerG3G R y st len lim := by
  simp only [kerG3G, hamming_same' h, gappedPen3G_same h, h.1]

theorem fwdLG_same (R : ByteArray) (K : RP) (P : PGen) (st stop k : Nat) :
    fwdLG R x K P st stop k = fwdLG R y K P st stop k := by
  simp only [fwdLG, fwdMis_same' h]

theorem bwdLG_same (R : ByteArray) (K : RP) (P : PGen) (st len lo k : Nat) :
    bwdLG R x K P st len lo k = bwdLG R y K P st len lo k := by
  simp only [bwdLG, bwdMis_same' h]

theorem gappedLG_same (R : ByteArray) (K : RP) (P : PGen) (st len lim : Nat) :
    gappedLG R x K P st len lim = gappedLG R y K P st len lim := by
  simp only [gappedLG, fwdLG_same h, bwdLG_same h]

theorem kerGKG_same (R : ByteArray) (K : RP) (P : PGen) (st len lim : Nat) :
    kerGKG R K x P st len lim = kerGKG R K y P st len lim := by
  simp only [kerGKG, hamming_same' h, kerG3G_same h, gappedLG_same h]

theorem twoGapCG_same (R : ByteArray) (st len : Nat) : twoGapCG R x st len = twoGapCG R y st len := by
  simp only [twoGapCG, fwdMis_same' h, bwdMis_same' h, hamming_same' h]

end

/-- At `ByteArray` the copies are the originals. -/
theorem kerGKG_bytes (R : ByteArray) (K : RP) (G : ByteArray) (P : PGen) (st len lim : Nat) :
    kerGKG R K G P st len lim = kerGK R K G P st len lim := rfl

theorem twoGapCG_bytes (R G : ByteArray) (st len : Nat) : twoGapCG R G st len = twoGapC R G st len := rfl

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1} {ys : Array G2}
  (h : SameA xs ys)
include h

theorem twoGap16G_same (R : ByteArray) (c st len : Nat) :
    twoGap16G R xs c st len = twoGap16G R ys c st len := by
  simp only [twoGap16G, twoGapCG_same (h.2 c), twoGapB_same (h.2 c), bandPen_same h]

theorem ker16KG_same (R : ByteArray) (K : RP) (pvs : Array PGen) (c st len : Nat) :
    ker16KG R K xs pvs c st len = ker16KG R K ys pvs c st len := by
  simp only [ker16KG, h.1, ker16_same h, (h.2 c).1, kerGKG_same (h.2 c), twoGap16G_same h]

theorem kerHKG_same (R : ByteArray) (K : RP) (pvs : Array PGen) (c st len l : Nat) :
    kerHKG R K xs pvs c st len l = kerHKG R K ys pvs c st len l := by
  simp only [kerHKG, kerGKG_same (h.2 c), ker16KG_same h]

end

theorem kerHKG_bytes (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len l : Nat) :
    kerHKG R K gbs pvs c st len l = kerHK R K gbs pvs c st len l := rfl

/-! ## Proofs: the search -/

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] [Inhabited G1] [Inhabited G2] {xs : Array G1} {ys : Array G2}
  (h : SameA xs ys) {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf kf1 kf2 : Ker) (ix : L) (G : ByteArray)
include h

theorem chromKBFG_same (R : ByteArray) (c P : Nat) (acc : List (Array Nat)) (b1 : Best) :
    chromKBFG kf R xs c P acc b1 = chromKBFG kf R ys c P acc b1 := by
  simp only [chromKBFG, stageB_same h]

theorem advFG_same (R : ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) :
    s.advFG kf ix G R xs offs n t P Ls ps b = s.advFG kf ix G R ys offs n t P Ls ps b := by
  have e : ∀ bs a, advCFG kf R.size xs offs t P bs a = advCFG kf R.size ys offs t P bs a := by
    intro bs a; funext r c; simp only [advCFG, (h.2 _).1]
  obtain ⟨ord, J, acc⟩ := s
  cases ord with
  | nil => rfl
  | cons j rest => simp only [GS.advFG, e]

theorem ilGFG_same (R1 R2 : ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGFG kf1 kf2 ix G R1 R2 xs offs n P Ls ps1 ps2 f s1 s2 b =
      ilGFG kf1 kf2 ix G R1 R2 ys offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilGFG, advFG_same h, ih]

end

/-- At `ByteArray` the generic search is `mapChromsGBF`. -/
theorem advFG_bytes {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf : Ker) (ix : L) (G R : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) :
    s.advFG kf ix G R gbs2 offs n t P Ls ps b = s.advF kf ix G R gbs2 offs n t P Ls ps b := rfl

theorem ilGFG_bytes {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGFG kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b =
      ilGF kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilGFG, ilGF, advFG_bytes, ih]

theorem mapChromsGBFG_bytes {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (R Rr : ByteArray) (ps pr : Array Pp) :
    mapChromsGBFG kf1 kf2 P ix G offs gbs R Rr ps pr = mapChromsGBF kf1 kf2 P ix G offs gbs R Rr ps pr := by
  simp only [mapChromsGBFG, mapChromsGBF, ilGFG_bytes]
  rfl

/-- Packed chromosomes = their unpacked bytes, for the whole word-kernel search. -/
theorem mapChromsGBKG_unpack {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapChromsGBKG P ix G offs pgs pgs R = mapChromsGBK P ix G offs (pgs.map Mz.unpack) pgs R := by
  have hs := sameA_unpack pgs
  have h2 := sameA_append hs sameG_default
  unfold mapChromsGBKG mapChromsGBK mapChromsGBFG
  have ek : ∀ R K, kerHKG R K (pgs ++ pgs) (pgs ++ pgs) = kerHK R K (pgs.map Mz.unpack ++ pgs.map Mz.unpack) (pgs ++ pgs) := by
    intro R K; funext c st len l; rw [kerHKG_same h2, kerHKG_bytes]
  simp only [ek, hs.1, ilGFG_same h2, chromKBFG_same h2]
  rw [← mapChromsGBFG_bytes]
  rfl

/-- `RepAllK` for the packed chromosomes against their own unpacking. -/
theorem repAllK_unpack (pgs : Array PGen) : RepAllK (pgs ++ pgs) (pgs.map Mz.unpack ++ pgs.map Mz.unpack) := by
  intro c
  by_cases h1 : c < pgs.size
  · rw [getElem!_pos (pgs ++ pgs) c (by simp; omega), getElem!_pos (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c
      (by simp; omega), Array.getElem_append_left (by omega), Array.getElem_append_left (by simp; omega)]
    simp only [Array.getElem_map]
    exact Mz.rep_unpack _
  by_cases h2 : c < 2 * pgs.size
  · rw [getElem!_pos (pgs ++ pgs) c (by simp; omega), getElem!_pos (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c
      (by simp; omega), Array.getElem_append_right (by omega), Array.getElem_append_right (by simp; omega)]
    simp only [Array.getElem_map, Array.size_map]
    exact Mz.rep_unpack _
  · rw [getElem!_neg (pgs ++ pgs) c (by simp; omega),
      getElem!_neg (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c (by simp; omega)]
    exact rep_default

/-- `mapChromsGBK_eq` with `RepAllK` in place of the runtime check. -/
theorem mapChromsGBK_eq_rep {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAllK (pvs ++ pvs) (gbs ++ gbs))
    (R : ByteArray) : mapChromsGBK P ix G offs gbs pvs R = mapChromsGB P ix G offs gbs R := by
  unfold mapChromsGBK
  simp only [revCompK_eq, prepGK_eq]
  rw [← mapChromsGBF_eq]
  congr 1
  · funext c st len l; exact kerHK_eq R _ _ hrep c st len l
  · funext c st len l; exact kerHK_eq (revCompB R) _ _ hrep c st len l

theorem mapFastGBKP_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapFastGBKP P ix G offs pgs R = mapFastGB P ix G offs (pgs.map Mz.unpack) R := by
  unfold mapFastGBKP mapFastGB
  rw [mapChromsGBKG_unpack, mapChromsGBK_eq_rep P ix G offs _ pgs (repAllK_unpack pgs)]
  simp

/-! ## Top theorems -/

/-- **Packed genome, word kernels, one `T = −P`.** -/
theorem pairFastGBKP_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairFastGBKP P lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  have e : pairFastGBKP P lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairFastGB P lo hi ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R1 R2 := by
    unfold pairFastGBKP pairFastGB
    rw [mapFastGBKP_eq, mapFastGBKP_eq,
      mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl),
      mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)]
    rfl
  rw [e]
  exact pairFastGB_eq_pairSpec P lo hi g m1 m2 _ R1 R2 _ _ offs hg h1 h2 (catOk_cut G offs ns hcut)
    (lookOk_pk ix G hchk)

/-- **Packed genome, word kernels, length dispatch** (`T = −16` / `−12` per mate). -/
theorem pairDispatchKP_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairDispatchKP lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairSpecT (-(penOf R1 : Int)) (-(penOf R2 : Int)) lo hi g m1 m2 := by
  have e : pairDispatchKP lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairDispatch lo hi ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R1 R2 := by
    unfold pairDispatchKP pairDispatch
    rw [mapFastGBKP_eq, mapFastGBKP_eq,
      mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl),
      mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)]
    rfl
  rw [e]
  exact pairDispatch_eq_pairSpecT lo hi g m1 m2 _ R1 R2 _ _ offs hg h1 h2 (catOk_cut G offs ns hcut)
    (lookOk_pk ix G hchk)

end MapSpec.Fast

#print axioms MapSpec.Mz.check3P_eq
#print axioms MapSpec.Fast.pairDispatchP_mz_eq
#print axioms MapSpec.Fast.mapFastGBKP_eq
#print axioms MapSpec.Fast.pairFastGBKP_mz_eq_pairSpec
#print axioms MapSpec.Fast.pairDispatchKP_mz_eq
