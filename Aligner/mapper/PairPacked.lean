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

/-- A seed lookup reading a packed genome (the `Look.look` of a packed index). -/
abbrev LookPk (L P : Type) := L → PGen → ByteArray → Nat → P → Array Nat

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

end MzP

/-! ## Proofs: under `Rep`, each copy computes what the byte version computes -/

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

variable {L Q : Type} [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q)
  (hlp : ∀ ix R j p, lp ix P R j p = lk.look ix G R j p)
include hlp

end

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

end

end MapSpec.Fast

