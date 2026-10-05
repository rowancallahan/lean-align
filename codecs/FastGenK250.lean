import FastGenPair
import FastGenProof
import MapperK250Words

/-!
# Codec `pairFastGBK`: `pairFastGB` with the word kernels

`pairFastGB` (codecs/FastGenPair.lean) with its window kernel `kerH` replaced by
`kerHK`: the word kernel `kerGK` (pool/mapper/MapperK250.lean) up to `15`, and at `16`
`ker16K`, which decides the one-gap penalty-16 windows in closed form (first/last
three mismatches) instead of the banded kernel; the banded kernel is left only for
two-gap candidates.  The genome is read through the packed copy `pvs` (`Rep`).

The search code is copied with the kernel as a parameter (`…F`); with `kerH` it is
`pairFastGB` itself.

    kerHK R (packRP R) gbs pvs c st len l = kerH R gbs c st len l          (kerHK_eq)
    pairFastGBK … = pairFastGB …                                           (pairFastGBK_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Kernels -/

/-- `complB` as a table (no branches). -/
@[irreducible] def complTab : ByteArray := ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 84, 66, 71, 68, 69, 70, 67, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 65, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]⟩

/-- Reverse complement, one pass. -/
def revCompLoop (R : ByteArray) : (i : Nat) → ByteArray → ByteArray
  | 0, acc => acc
  | i + 1, acc => revCompLoop R i (acc.push (complTab.get! (R.get! i).toNat))

@[inline] def revCompK (R : ByteArray) : ByteArray := revCompLoop R R.size (ByteArray.emptyWithCapacity R.size)

/-- The two-gap candidates (necessary for an exact two-gap walk). -/
@[inline] def twoGapC (R G : ByteArray) (st len : Nat) : Bool :=
  let n := R.size
  let A := fwdMis R G st n 0 1
  let B := bwdMis R G st len 0 n 1
  (len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0)

/-- Two-gap windows (penalty `> 15`, not four mismatches): the necessary test first. -/
@[inline] def twoGap16 (R : ByteArray) (gbs : Array ByteArray) (c st len : Nat) : Nat :=
  let G := gbs[c]!
  if !twoGapC R G st len then 17
  else if twoGapB R G st len then 16
  else bandPen 16 R gbs ⟨c, st, len⟩

/-- `ker16`: the word kernel capped at `17` (exact one-gap formula), then the two-gap
tests for lengths `n`, `n ± 2`. -/
def ker16K (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len : Nat) : Nat :=
  if st + len ≤ gbs[c]!.size then
    let r := kerGK R K gbs[c]! pvs[c]! st len 16
    if r ≤ 16 then r
    else if len = R.size ∨ len = R.size + 2 ∨ len + 2 = R.size then twoGap16 R gbs c st len
    else 17
  else 17

/-- `kerH` with the word kernels. -/
@[inline] def kerHK (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len l : Nat) : Nat :=
  if l ≤ 15 then kerGK R K gbs[c]! pvs[c]! st len l else ker16K R K gbs pvs c st len

/-! ## The search with the kernel as a parameter (copied from `pairFastGB`) -/

/-- A window kernel: chromosome, start, length, cap `l` ↦ penalty capped at `l + 1`. -/
abbrev Ker := Nat → Nat → Nat → Nat → Nat

@[inline] def addKF (kf : Ker) (c lim : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then
    let l := min lim b.pen
    let r := kf c st.toNat len.toNat l
    if r ≤ l then b.add c st.toNat len.toNat r else b
  else b

def stageKF (kf : Ker) (n c lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (b : Best) : Best :=
  ds.foldl (fun b D => shs.foldl (fun b sh => addKF kf c lim (dst n D sh) (wlen n sh) b) b) b

def chromKBF (kf : Ker) (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat)) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageKF kf R.size c lim ((shapesAt Q1).filter (· != (0, 0)))
        (diagsB acc (acc.length - sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageB P R gbs c (shapesAt Q2) (shifts (gapBound sc0 (-(Q2 : Int))))
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

@[inline] def advCF (kf : Ker) (n : Nat) (gbs2 : Array ByteArray) (offs : Array Nat) (t P bs : Nat) (a : Array Nat)
    (r : Array (List (Array Nat)) × Best) (c : Nat) : Array (List (Array Nat)) × Best :=
  let sl := sliceG a bs offs[c]! gbs2[t + c]!.size
  (r.1.set! c (sl :: r.1[c]!),
    sl.foldl (fun b e => addKF kf (t + c) (min P 16) ((e / 16 : Nat) - (n : Int)) n b) r.2)

@[inline] def GS.advF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf : Ker) (ix : L) (G R : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) : GS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := (List.range n).foldl (advCF kf R.size gbs2 offs t P (R.size - j * Ls)
      (LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!)) (s.acc, b)
    (⟨rest, j :: s.J, r.1⟩, r.2)

@[specialize] def ilGF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.live P b
    if s1.live P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advF kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGF kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advF kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGF kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `mapChromsGB` with the kernels `kf1` (read) and `kf2` (reverse complement). -/
@[specialize] def mapChromsGBF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (R Rr : ByteArray) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let ps := prepG ix R m Ls
  let pr := prepG ix Rr m Ls
  let x := ilGF kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  let b := (List.range n).foldl (fun b c => chromKBF kf1 R gbs2 c P x.1.acc[c]! b) x.2.2
  (List.range n).foldl (fun b c => chromKBF kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! b) b

/-! ## With the word kernels -/

/-- Both strands with the word kernels; `pvs` spells `gbs` (packed). -/
@[specialize] def mapChromsGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Best :=
  let gbs2 := gbs ++ gbs
  let pvs2 := pvs ++ pvs
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  mapChromsGBF (kerHK R K1 gbs2 pvs2) (kerHK Rr K2 gbs2 pvs2) P ix G offs gbs R Rr

def mapFastGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Option (Placement × Int) :=
  if fastT P R then decodeP gbs.size P (mapChromsGBK P ix G offs gbs pvs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB gbs) (decodeBytes R)

/-- A proper pair at `T = −P`, word kernels. -/
def pairFastGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGBK P ix G offs gbs pvs R1, mapFastGBK P ix G offs gbs pvs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-! ## Proofs: kernels -/

theorem revCompK_eq (R : ByteArray) : revCompK R = revCompB R := by
  sorry

/-- The packed chromosomes spell the byte chromosomes. -/
def RepAll (pvs : Array PGen) (gbs : Array ByteArray) : Prop := ∀ c : Nat, Rep pvs[c]! gbs[c]!

/-- **Penalty 16.** -/
theorem ker16K_eq (R : ByteArray) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAll pvs gbs)
    (c st len : Nat) : ker16K R (packRP R) gbs pvs c st len = ker16 R gbs c st len := by
  sorry

theorem kerHK_eq (R : ByteArray) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAll pvs gbs)
    (c st len l : Nat) : kerHK R (packRP R) gbs pvs c st len l = kerH R gbs c st len l := by
  unfold kerHK kerH
  split
  · exact kerGK_kerG R gbs[c]! pvs[c]! (hrep c) st len l (by omega)
  · exact ker16K_eq R gbs pvs hrep c st len

/-! ## Proofs: the search -/

/-- The runtime check of the packed chromosomes. -/
def checkPGs (pvs : Array PGen) (gbs : Array ByteArray) : Bool :=
  pvs.size == gbs.size && (List.range gbs.size).all fun c => checkPG pvs[c]! gbs[c]!

theorem checkPGs_ok (pvs : Array PGen) (gbs : Array ByteArray) (h : checkPGs pvs gbs = true) :
    RepAll (pvs ++ pvs) (gbs ++ gbs) := by
  sorry

theorem mapChromsGBF_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    mapChromsGBF (kerH R (gbs ++ gbs)) (kerH (revCompB R) (gbs ++ gbs)) P ix G offs gbs R (revCompB R) =
      mapChromsGB P ix G offs gbs R := by
  sorry

theorem mapChromsGBK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hpg : checkPGs pvs gbs = true) (R : ByteArray) :
    mapChromsGBK P ix G offs gbs pvs R = mapChromsGB P ix G offs gbs R := by
  have hrep := checkPGs_ok pvs gbs hpg
  unfold mapChromsGBK
  simp only [revCompK_eq]
  rw [← mapChromsGBF_eq]
  congr 1
  · funext c st len l; exact kerHK_eq R _ _ hrep c st len l
  · funext c st len l; exact kerHK_eq (revCompB R) _ _ hrep c st len l

theorem pairFastGBK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hpg : checkPGs pvs gbs = true) (R1 R2 : ByteArray) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairFastGB P lo hi ix G offs gbs R1 R2 := by
  have h : ∀ R, mapFastGBK P ix G offs gbs pvs R = mapFastGB P ix G offs gbs R := fun R => by
    unfold mapFastGBK mapFastGB; rw [mapChromsGBK_eq P ix G offs gbs pvs hpg]
  unfold pairFastGBK pairFastGB
  rw [h R1, h R2]
  cases mapFastGB P ix G offs gbs R1 <;> cases mapFastGB P ix G offs gbs R2 <;> rfl

/-! ## Top theorems -/

/-- **Proper pairs, word kernels, hashed index over the concatenation.** -/
theorem pairFastGBK_hashed_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  rw [pairFastGBK_eq P lo hi ix G offs gbs pvs hpg]
  exact pairFastGB_hashed_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

/-- **Proper pairs, word kernels, minimizer index over the concatenation.** -/
theorem pairFastGBK_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  rw [pairFastGBK_eq P lo hi ix G offs gbs pvs hpg]
  exact pairFastGB_mz_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.kerHK_eq
#print axioms MapSpec.Fast.pairFastGBK_eq
#print axioms MapSpec.Fast.pairFastGBK_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGBK_mz_eq_pairSpec
