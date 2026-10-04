import PairInterleave
import FastMapperMz
import MapperPGen
import MzPacked

/-!
# Codec `pairFastIP`: the interleaved pair mapper over a 2-bit genome

`pairFastI` (codecs/PairInterleave.lean) with every chromosome a `PGen`
(pool/mapper/MapperPGen.lean: 2 bits per letter, block flags, exact non-ACGT
runs) instead of a byte array.  The code below copies the genome-reading part of
the mapper with `G.get!`/`G.size` replaced by `PGen.get`/`PGen.n`; the seed
lookup reads the genome through `lp` (for the minimizer index `mzLookP`).

    RepAll pgs gbs → pairFastIP lk lp lo hi pgs idxs R1 R2 = pairFastI lk lo hi gbs idxs R1 R2  (pairFastIP_eq)
    … → pairFastIP … = pairSpec sc0 (-12) lo hi g m1 m2                    (pairFastIP_eq_pairSpec)
    checkAllPG pgs gbs → checkAllMz idxs gbs → … = pairSpec …              (pairFastIP_mz_eq_pairSpec)

`gbs` is only needed to run the two checkers; the mapper itself never reads it.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm (copies of `MapperFastAlgo` / `MapperInterleave` / `PairInterleave`) -/

@[inline] def hamStepP (r : ByteArray) (g : PGen) (a lim i stop : Nat) (clean : Bool) (m : Nat) : Nat :=
  if m ≤ lim && !clean then hammingP r g a lim i stop m else m

@[inline] def hamSeedsP (r : ByteArray) (g : PGen) (a mask lim : Nat) : Nat :=
  hamStepP r g a lim (3 * q) (4 * q) (mask / 8 % 2 == 1) <|
  hamStepP r g a lim (2 * q) (3 * q) (mask / 4 % 2 == 1) <|
  hamStepP r g a lim q (2 * q) (mask / 2 % 2 == 1) <|
  hamStepP r g a lim 0 q (mask % 2 == 1) <|
  hammingP r g a lim (4 * q) r.size 0

def gappedPen2P (r : ByteArray) (g : PGen) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdMisP r g st (n - skip) 0 1
  let E1 := bwdMisP r g st len skip n 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdMisP r g st (n - skip) 0 2
  let E2 := bwdMisP r g st len skip n 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else lim + 1

@[inline] def gapWP (R : ByteArray) (G : PGen) (c st len s : Nat) (ok : Bool) (b : Best) : Best :=
  if need b ≤ s && ok && st + len ≤ G.n then b.add c st len (gappedPen2P R G st len (min b.pen cap)) else b

@[inline] def sameStep2P (R : ByteArray) (G : PGen) (c : Nat) (b : Best) (e : Nat) : Best :=
  let A := e / 16
  if BIAS ≤ A && A - BIAS + R.size ≤ G.n && !(b.pen == 0 && b.amb) then
    let m := hamSeedsP R G (A - BIAS) (e % 16) (min 3 (b.pen / 4))
    if 4 * m ≤ cap then b.add c (A - BIAS) R.size (4 * m) else b
  else b

@[inline] def seedOnP (G : PGen) (R : ByteArray) (looked j A : Nat) : Nat :=
  if (looked >>> j) % 2 == 0 && BIAS ≤ A + j * q && A + j * q - BIAS + q ≤ G.n &&
      eqRunP G R (A + j * q - BIAS) (j * q) q then 1 else 0

@[inline] def supAtP (G : PGen) (R : ByteArray) (as : Array Nat) (looked i A : Nat) : Nat :=
  supNear as i A + seedOnP G R looked 0 A + seedOnP G R looked 1 A + seedOnP G R looked 2 A +
    seedOnP G R looked 3 A

@[inline] def gapL2P (R : ByteArray) (G : PGen) (c : Nat) (as : Array Nat) (looked i A cs L : Nat) (b : Best) : Best :=
  let n := R.size
  let sm := supAtP G R as looked i (A - L)
  let sp := supAtP G R as looked i (A + L)
  gapWP R G c (A + L - BIAS) (n - L) (cs + sp) (BIAS ≤ A + L) <|
  gapWP R G c (A - L - BIAS) (n + L) (cs + sm) (BIAS + L ≤ A) <|
  gapWP R G c (A - BIAS) (n - L) (cs + sm) (BIAS ≤ A) <|
  gapWP R G c (A - BIAS) (n + L) (cs + sp) (BIAS ≤ A) b

def gapAll2P (R : ByteArray) (G : PGen) (c : Nat) (as : Array Nat) (looked : Nat) : (k i : Nat) → Best → Best
  | 0, _, b => b
  | k + 1, i, b =>
    let A := as[i]! / 16
    let cs := supAtP G R as looked i A
    gapAll2P R G c as looked k (i + 1)
      (gapL2P R G c as looked i A cs 3 (gapL2P R G c as looked i A cs 2 (gapL2P R G c as looked i A cs 1 b)))

/-- A seed lookup reading a packed genome (the `Look.look` of a packed index). -/
abbrev LookPk (L P : Type) := L → PGen → ByteArray → Nat → P → Array Nat

@[inline] def lzStepP {L P : Type} [Inhabited P] (R : ByteArray) (G : PGen) (c : Nat)
    (lp : LookPk L P) (ix : L) (ps : Array P) (j k : Nat) (as : Array Nat) (looked : Nat) (b : Best) :
    Array Nat × Best :=
  let lj := lp ix G R j ps[j]!
  let fresh := newOnly as lj 0 0 #[]
  let as := merge as lj 0 0 #[]
  let looked := looked + pow2 j
  let b := fresh.foldl (sameStep2P R G c) b
  (as, if 2 ≤ k && 8 ≤ b.pen then gapAll2P R G c as looked as.size 0 b else b)

@[inline] def LzS.advP {L P : Type} [Inhabited P] (R : ByteArray) (G : PGen) (c : Nat)
    (lp : LookPk L P) (ix : L) (ps : Array P) (s : LzS) (b : Best) : LzS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := lzStepP R G c lp ix ps j s.k s.as s.looked b
    (⟨rest, s.k + 1, r.1, s.looked + pow2 j⟩, r.2)

@[specialize] def ilLoopP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (G : PGen) (ix : L)
    (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) : Nat → LzS → LzS → Best → Best
  | 0, _, _, b => b
  | f + 1, s1, s2, b =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := s1.advP R1 G c1 lp ix ps1 b
      ilLoopP lk lp G ix R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advP R2 G c2 lp ix ps2 b
      ilLoopP lk lp G ix R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2
    else b

@[inline] def mapChromIP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (G : PGen) (ix : L)
    (R1 R2 : ByteArray) (c1 c2 : Nat) (hs1 hs2 : Array (Option UInt64)) (b : Best) : Best :=
  let ps1 := prepAll lk ix hs1
  let ps2 := prepAll lk ix hs2
  ilLoopP lk lp G ix R1 R2 c1 c2 ps1 ps2 8 (LzS.init lk ix ps1) (LzS.init lk ix ps2) b

@[specialize] def mapChromsIP {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lp : LookPk L P)
    (R : ByteArray) (gbs : Array PGen) (idxs : Array L) (rf : Bool := false) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let hs := seedHashes R
  let hr := seedHashes Rr
  (List.range n).foldl (fun b c =>
    if rf then mapChromIP lk lp gbs[c]! idxs[c]! Rr R (n + c) c hr hs b
    else mapChromIP lk lp gbs[c]! idxs[c]! R Rr c (n + c) hs hr b) {}

def mapFastIP {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lp : LookPk L P) (gbs : Array PGen)
    (idxs : Array L) (R : ByteArray) (rf : Bool := false) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsIP lk lp R gbs idxs rf)

def pairFastIP {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lp : LookPk L P) (lo hi : Nat)
    (gbs : Array PGen) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastIP lk lp gbs idxs R1 false with
  | none => none
  | some a =>
    match mapFastIP lk lp gbs idxs R2 (a.1.2 == Strand.fwd) with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ### Minimizer-index lookup over a packed genome (copies of `Mz.okAt` … `mzLook`) -/

section MzP
open Mz

@[inline] def okAtP (ix : MzIdx) (G : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) : Bool :=
  let e := (ix.slot t)
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     let tg := ix.tagOf e
     decide (o ≤ pos) &&
      (if ix.flagF tg = 0 then (ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw &&
         decide (pos - o + Mz.q ≤ G.n) && eqRunP G R (pos - o) s n1 &&
         eqRunP G R (pos + a2) (s + o + a2) n2 &&
         (ix.kf == ix.kb || eqRunP G R pos (s + o) ix.k)
       else decide (pos - o + Mz.q ≤ G.n) && eqRunP G R (pos - o) s Mz.q))

def scanAP (ix : MzIdx) (G : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanAP ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t then acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

@[inline] def okEdgeP (ix : MzIdx) (G : PGen) (R : ByteArray) (side d s i : Nat) : Bool :=
  let x := ix.runs[2 * i + side]!
  decide (d ≤ x) && decide (x - d + Mz.q ≤ G.n) && eqRunP G R (x - d) s Mz.q

def scanEdgeAP (ix : MzIdx) (G : PGen) (R : ByteArray) (side d s base bit : Nat) (i : Nat) (acc : Array Nat) :
    Array Nat :=
  if i < ix.nr then
    scanEdgeAP ix G R side d s base bit (i + 1)
      (if okEdgeP ix G R side d s i then acc.push (anc base bit (ix.runs[2 * i + side]! - d)) else acc)
  else acc
termination_by ix.nr - i

def scanRangeAP (G : PGen) (R : ByteArray) (s stop base bit : Nat) (p : Nat) (acc : Array Nat) : Array Nat :=
  if p < stop then
    scanRangeAP G R s stop base bit (p + 1)
      (if decide (p + Mz.q ≤ G.n) && eqRunP G R p s Mz.q then acc.push (anc base bit p) else acc)
  else acc
termination_by stop - p

def scanInsideAP (ix : MzIdx) (G : PGen) (R : ByteArray) (s base bit : Nat) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i < ix.nr then
    scanInsideAP ix G R s base bit (i + 1) (scanRangeAP G R s (ix.rb i + 1 - Mz.q) base bit (ix.ra i) acc)
  else acc
termination_by ix.nr - i

def lookupCodeAP (ix : MzIdx) (G : PGen) (R : ByteArray) (s v base bit : Nat) : Array Nat :=
  let o := ix.mini v
  let h := ix.hsh (ix.sub v o)
  let b := h >>> ix.kb
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanAP ix G R s o (h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB b) base bit (ix.loB b) #[]

def lookupSeedAP (ix : MzIdx) (G : PGen) (R : ByteArray) (s base bit : Nat) : Array Nat :=
  let u := Mz.firstOdd R s (s + Mz.q)
  if u = s + Mz.q then lookupCodeAP ix G R s (Mz.wcGo R s (s + Mz.q) 0) base bit
  else if s < u then scanEdgeAP ix G R 0 (u - s) s base bit 0 #[]
  else
    let u2 := Mz.firstAcgt R s (s + Mz.q)
    if u2 < s + Mz.q then scanEdgeAP ix G R 1 (u2 - s) s base bit 0 #[]
    else scanInsideAP ix G R s base bit 0 #[]

@[inline] def lookupPP (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanAP ix G R s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base bit (ix.loB p.b) #[]

def mzLookP (ix : MzIdx) (G : PGen) (R : ByteArray) (j : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupPP ix G R (j * q) p (BIAS - j * q) (pow2 j)
  else lookupSeedAP ix G R (j * q) (BIAS - j * q) (pow2 j)

end MzP

/-- Every chromosome passes `checkPG`. -/
def checkAllPG (pgs : Array PGen) (gbs : Array ByteArray) : Bool :=
  pgs.size == gbs.size && (List.range gbs.size).all fun c => checkPG pgs[c]! gbs[c]!

/-! ## Proofs: under `Rep`, each copy computes what the byte version computes -/

def RepAll (pgs : Array PGen) (gbs : Array ByteArray) : Prop := pgs.size = gbs.size ∧ ∀ c : Nat, Rep pgs[c]! gbs[c]!

theorem checkAllPG_ok (pgs : Array PGen) (gbs : Array ByteArray) (h : checkAllPG pgs gbs = true) :
    RepAll pgs gbs := by
  simp only [checkAllPG, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun c => ?_⟩
  by_cases hc : c < gbs.size
  · exact checkPG_ok _ _ (h.2 c hc)
  · rw [getElem!_neg pgs c (by omega), getElem!_neg gbs c (by omega)]
    refine ⟨rfl, fun i => ?_⟩
    rw [get!_out _ i (Nat.zero_le _)]; rfl

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem hamSeedsP_eq (r : ByteArray) (a mask lim : Nat) : hamSeedsP r P a mask lim = hamSeeds r G a mask lim := by
  simp only [hamSeedsP, hamSeeds, hamStepP, hamStep, hammingP_eq' h] <;> rfl

theorem gappedPen2P_eq (r : ByteArray) (st len lim : Nat) : gappedPen2P r P st len lim = gappedPen2 r G st len lim := by
  simp only [gappedPen2P, gappedPen2, fwdMisP_eq' h, bwdMisP_eq' h]

theorem gapWP_eq (R : ByteArray) (c st len s : Nat) (ok : Bool) (b : Best) :
    gapWP R P c st len s ok b = gapW R G c st len s ok b := by
  simp only [gapWP, gapW, addGap, gappedPen2P_eq h, h.1]

theorem sameStep2P_eq (R : ByteArray) (c : Nat) : sameStep2P R P c = sameStep2 R G c := by
  funext b e; simp only [sameStep2P, sameStep2, hamSeedsP_eq h, h.1]

theorem supAtP_eq (R : ByteArray) (as : Array Nat) (looked i A : Nat) :
    supAtP P R as looked i A = supAt G R as looked i A := by
  simp only [supAtP, supAt, seedOnP, seedOn, eqRunP_eq h, h.1]

theorem gapL2P_eq (R : ByteArray) (c : Nat) (as : Array Nat) (looked i A cs L : Nat) (b : Best) :
    gapL2P R P c as looked i A cs L b = gapL2 R G c as looked i A cs L b := by
  simp only [gapL2P, gapL2, supAtP_eq h, gapWP_eq h]

theorem gapAll2P_eq (R : ByteArray) (c : Nat) (as : Array Nat) (looked : Nat) :
    ∀ k i b, gapAll2P R P c as looked k i b = gapAll2 R G c as looked k i b := by
  intro k
  induction k with
  | zero => intro i b; rfl
  | succ k ih => intro i b; simp only [gapAll2P, gapAll2, gapL2P_eq h, supAtP_eq h, ih]

variable {L Q : Type} [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q)
  (hlp : ∀ ix R j p, lp ix P R j p = lk.look ix G R j p)
include hlp

theorem advP_eq (R : ByteArray) (c : Nat) (ix : L) (ps : Array Q) (s : LzS) (b : Best) :
    s.advP R P c lp ix ps b = s.adv R G c lk ix ps b := by
  unfold LzS.advP LzS.adv
  split <;> simp only [lzStepP, lzStep, hlp, sameStep2P_eq h, gapAll2P_eq h] <;> simp only [*]

theorem ilLoopP_eq (ix : L) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array Q) :
    ∀ f s1 s2 b, ilLoopP lk lp P ix R1 R2 c1 c2 ps1 ps2 f s1 s2 b = ilLoop lk G ix R1 R2 c1 c2 ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilLoopP, ilLoop, advP_eq h lk lp hlp, ih]

theorem mapChromIP_eq (ix : L) (R1 R2 : ByteArray) (c1 c2 : Nat) (hs1 hs2 : Array (Option UInt64)) (b : Best) :
    mapChromIP lk lp P ix R1 R2 c1 c2 hs1 hs2 b = mapChromI lk G ix R1 R2 c1 c2 hs1 hs2 b := by
  simp only [mapChromIP, mapChromI, ilLoopP_eq h lk lp hlp]

end

theorem pairFastIP_eq {L Q : Type} [Inhabited L] [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q) (lo hi : Nat)
    (pgs : Array PGen) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) (hrep : RepAll pgs gbs)
    (hlp : ∀ P G, Rep P G → ∀ ix R j p, lp ix P R j p = lk.look ix G R j p) :
    pairFastIP lk lp lo hi pgs idxs R1 R2 = pairFastI lk lo hi gbs idxs R1 R2 := by
  have e : ∀ R rf, mapFastIP lk lp pgs idxs R rf = mapFastI lk gbs idxs R rf := fun R rf => by
    simp only [mapFastIP, mapFastI, mapChromsIP, mapChromsI, hrep.1,
      mapChromIP_eq (hrep.2 _) lk lp (hlp _ _ (hrep.2 _))]
  simp only [pairFastIP, pairFastI, e] <;> rfl

theorem pairFastIP_eq_pairSpec {L Q : Type} [Inhabited L] [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q)
    (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (pgs : Array PGen) (gbs : Array ByteArray) (idxs : Array L)
    (R1 R2 : ByteArray) (hrep : RepAll pgs gbs) (hlp : ∀ P G, Rep P G → ∀ ix R j p, lp ix P R j p = lk.look ix G R j p)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastIP lk lp lo hi pgs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  rw [pairFastIP_eq lk lp lo hi pgs gbs idxs R1 R2 hrep hlp]
  exact pairFastI_eq_pairSpec lk lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 hlk hok1 hok2

/-! ### The minimizer lookup -/

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h
open Mz

theorem okAtP_eq (ix : MzIdx) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) :
    okAtP ix P R s o key bw aw pmo o2 n1 a2 n2 t = Mz.okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t := by
  simp only [okAtP, Mz.okAt, eqRunP_eqMz h, h.1]

theorem scanAP_eq (ix : MzIdx) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ d t acc, hi - t = d → scanAP ix P R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
      scanA ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanAP scanA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro t acc hd
    unfold scanAP scanA
    have ih' := fun acc => ih (t + 1) acc (by omega)
    simp only [show t < hi from by omega, if_true, okAtP_eq h, ih']

theorem scanEdgeAP_eq (ix : MzIdx) (R : ByteArray) (side d0 s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanEdgeAP ix P R side d0 s base bit i acc = scanEdgeA ix G R side d0 s base bit i acc := by
  intro d
  induction d with
  | zero => intro i acc hd; unfold scanEdgeAP scanEdgeA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i acc hd
    unfold scanEdgeAP scanEdgeA
    have ih' := fun acc => ih (i + 1) acc (by omega)
    simp only [show i < ix.nr from by omega, if_true, ih', okEdgeP, Mz.okEdge, eqRunP_eqMz h, h.1] <;> rfl

theorem scanRangeAP_eq (R : ByteArray) (s stop base bit : Nat) :
    ∀ d p acc, stop - p = d → scanRangeAP P R s stop base bit p acc = scanRangeA G R s stop base bit p acc := by
  intro d
  induction d with
  | zero => intro p acc hd; unfold scanRangeAP scanRangeA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro p acc hd
    unfold scanRangeAP scanRangeA
    have ih' := fun acc => ih (p + 1) acc (by omega)
    simp only [show p < stop from by omega, if_true, ih', Mz.okIn, eqRunP_eqMz h, h.1] <;> rfl

theorem scanInsideAP_eq (ix : MzIdx) (R : ByteArray) (s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanInsideAP ix P R s base bit i acc = scanInsideA ix G R s base bit i acc := by
  intro d
  induction d with
  | zero => intro i acc hd; unfold scanInsideAP scanInsideA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i acc hd
    unfold scanInsideAP scanInsideA
    have ih' := fun acc => ih (i + 1) acc (by omega)
    simp only [show i < ix.nr from by omega, if_true, ih', scanRangeAP_eq h _ _ _ _ _ _ _ _ rfl]

theorem mzLookP_eq (ix : MzIdx) (R : ByteArray) (j : Nat) (p : MzP) : mzLookP ix P R j p = mzLook ix G R j p := by
  simp only [mzLookP, mzLook, lookupPP, lookupP, lookupSeedAP, lookupSeedA, lookupCodeAP, lookupCodeA,
    fun ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =>
      scanAP_eq h ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit _ t acc rfl,
    fun ix R side d0 s base bit i acc => scanEdgeAP_eq h ix R side d0 s base bit _ i acc rfl,
    fun ix R s base bit i acc => scanInsideAP_eq h ix R s base bit _ i acc rfl]

end

/-- **Packed genome + minimizer index.**  A packed genome and an index that pass
their runtime checkers against the byte genome give the specification's answer. -/
theorem pairFastIP_mz_eq_pairSpec (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (pgs : Array PGen)
    (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hpk : checkAllPG pgs gbs = true)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : checkAllMz idxs gbs = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastIP mzL mzLookP lo hi pgs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  rw [pairFastIP_eq mzL mzLookP lo hi pgs gbs idxs R1 R2 (checkAllPG_ok pgs gbs hpk)
    (fun P G h ix R j p => mzLookP_eq h ix R j p)]
  exact pairFastI_mz_eq_pairSpec lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 hchk hok1 hok2

/-- Every index passes the checker on its packed chromosome (no byte genome needed). -/
def checkAllMzP (idxs : Array Mz.MzIdx) (pgs : Array PGen) : Bool :=
  (List.range pgs.size).all fun c => Mz.check2P idxs[c]! pgs[c]!

/-- **Packed genome only.**  For a packed genome that spells `g` (`GenomeBytes` of its
bytes, `Mz.unpack`, which is never computed) and indexes that pass `checkAllMzP`
against it, the packed mapper gives the specification's answer. -/
theorem pairFastIP_mzP_eq_pairSpec (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (pgs : Array PGen)
    (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hg : GenomeBytes (pgs.map Mz.unpack) g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : checkAllMzP idxs pgs = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastIP mzL mzLookP lo hi pgs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold checkAllMzP at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  have hrep : RepAll pgs (pgs.map Mz.unpack) := by
    refine ⟨by simp, fun c => ?_⟩
    by_cases hc : c < pgs.size
    · rw [show (pgs.map Mz.unpack)[c]! = Mz.unpack pgs[c]! by simp [hc]]; exact Mz.rep_unpack _
    · rw [getElem!_neg pgs c (by omega), getElem!_neg _ c (by simp; omega)]
      exact ⟨rfl, fun i => by rw [get!_out _ i (Nat.zero_le _)]; rfl⟩
  rw [pairFastIP_eq mzL mzLookP lo hi pgs _ idxs R1 R2 hrep (fun P G h ix R j p => mzLookP_eq h ix R j p)]
  refine pairFastI_mz_eq_pairSpec lo hi g m1 m2 _ idxs R1 R2 hg h1 h2 ?_ hok1 hok2
  unfold checkAllMz
  simp only [List.all_eq_true, List.mem_range, Array.size_map]
  intro c hc
  rw [show (pgs.map Mz.unpack)[c]! = Mz.unpack pgs[c]! by simp [hc], ← Mz.check2P_eq (Mz.rep_unpack _)]
  exact hchk c hc

end MapSpec.Fast

#print axioms MapSpec.Fast.pairFastIP_eq
#print axioms MapSpec.Fast.pairFastIP_mzP_eq_pairSpec
#print axioms MapSpec.Fast.pairFastIP_eq_pairSpec
#print axioms MapSpec.Fast.pairFastIP_mz_eq_pairSpec
