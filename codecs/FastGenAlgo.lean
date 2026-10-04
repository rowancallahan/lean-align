import FastMapper
import MapperGenBest
import MapperGenScore
import MapperGenLook
import SeedMapper2

/-!
# The general fast mapper: any read length, any threshold `T = −P`

Read `R` of `n` letters, `m = n / 25` seeds of `Ls = n / m ≥ 25` letters (seed
`j` starts at `j·Ls`); the first 25 letters of each seed are looked up in the
25-mer index (`LookG`).  A genome place `p` of seed `j` is the anchor
`D = p + n − j·Ls` (stored as `D·16`); a shape `(a, b)` gives the window
`(D − n − a, n + a + b)`.

Per chromosome (`chromG`), with `lim = min P 15`:

1. `phase1`: seeds in `ord` (smallest bucket first); each anchor's same-length
   window is scored by the kernel `kerG` (exact up to `lim`).  Stop once
   `seedBound sc0 (−min best P)` is below the number of seeds looked up: a
   window that ties or beats the best has a clean seed among them.
2. `stageK`: when one gap fits (`gapBound > 0`), every anchor's windows of the
   shapes allowed at the best (`shapes`, without `(0, 0)`), kernel-scored.
3. `stageB`: when the best is still above `lim` (`P ≥ 16` and nothing `≤ 15`
   found), every anchor's windows of the allowed shapes, scored exactly by the
   banded kernel (`bandScore`), which also covers windows with two gap runs.

The best is carried over the chromosomes (`mapChromsG`); `mapFastTG` falls
back to the slow proved path when the read has too few seeds
(`seedBound sc0 T ≥ m`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Add window `(st, len)` scored by the kernel when its penalty is `≤ lim`. -/
@[inline] def addK (R G : ByteArray) (c lim : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then
    let r := kerG R G st.toNat len.toNat lim
    if r ≤ lim then b.add c st.toNat len.toNat r else b
  else b

/-- Penalty through the banded kernel: exact at `T = −P` (`P + 1` = not a hit). -/
@[inline] def bandPen (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (w : Window) : Nat :=
  match bandScore sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs w with
  | some s => if -(P : Int) ≤ s then (-s).toNat else P + 1
  | none => P + 1

@[inline] def addB (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then b.add c st.toNat len.toNat (bandPen P R gbs ⟨c, st.toNat, len.toNat⟩) else b

/-- The seed count for the penalty bound `x`: how many seeds a window within
penalty `x` can spoil. -/
@[inline] def sbound (x : Nat) : Nat := seedBound sc0 (-(x : Int))

/-- Look up the seeds of `ord`; each anchor's same-length window goes through the
kernel.  Returns the best, the anchor arrays and the seeds looked up (newest first). -/
def phase1 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (R G : ByteArray) (c P lim Ls : Nat)
    (ps : Array Pp) : (ord : List Nat) → List Nat → List (Array Nat) → Best → Best × List (Array Nat) × List Nat
  | [], J, acc, b => (b, acc, J)
  | j :: rest, J, acc, b =>
    let arr := LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!
    let b := arr.foldl (fun b e => addK R G c lim ((e / 16 : Nat) - (R.size : Int)) R.size b) b
    if sbound (min b.pen P) < J.length + 1 then (b, arr :: acc, j :: J)
    else phase1 ix R G c P lim Ls ps rest (j :: J) (arr :: acc) b

/-- Window of anchor `e` and shape `sh`: start and length. -/
@[inline] def wst (n e : Nat) (sh : Int × Int) : Int := ((e / 16 : Nat) : Int) - n - sh.1
@[inline] def wlen (n : Nat) (sh : Int × Int) : Int := (n : Int) + sh.1 + sh.2

def stageK (R G : ByteArray) (c lim : Nat) (shs : List (Int × Int)) (acc : List (Array Nat)) (b : Best) : Best :=
  acc.foldl (fun b arr => arr.foldl (fun b e => shs.foldl (fun b sh =>
    addK R G c lim (wst R.size e sh) (wlen R.size sh) b) b) b) b

def stageB (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (shs : List (Int × Int))
    (acc : List (Array Nat)) (b : Best) : Best :=
  acc.foldl (fun b arr => arr.foldl (fun b e => shs.foldl (fun b sh =>
    addB P R gbs c (wst R.size e sh) (wlen R.size sh) b) b) b) b

/-- Shapes allowed within penalty `x`. -/
@[inline] def shapesAt (x : Nat) : List (Int × Int) :=
  shapes (gapBound sc0 (-(x : Int))) (gapBound2 sc0 (-(x : Int)))

/-- One chromosome. -/
def chromG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (R : ByteArray) (gbs : Array ByteArray)
    (c P Ls : Nat) (ps : Array Pp) (ord : List Nat) (b : Best) : Best :=
  let G := gbs[c]!
  let lim := min P 15
  let r1 := phase1 ix R G c P lim Ls ps ord [] [] b
  let b1 := r1.1
  let acc := r1.2.1
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageK R G c lim ((shapesAt Q1).filter (· != (0, 0))) acc b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then stageB P R gbs c (shapesAt Q2) acc b2 else b2

/-- Seeds `0 … m-1`, smallest `size` first. -/
@[inline] def ordG (ks : Array Nat) (m : Nat) : List Nat :=
  (List.range m).foldl (fun l j => insKey ks j l) []

/-- All chromosomes; the seed hashes are computed once. -/
@[specialize] def mapChromsG {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) : Best :=
  let m := R.size / 25
  let Ls := R.size / m
  let hs := (Array.range m).map fun j => seedHashAt R (j * Ls)
  (List.range gbs.size).foldl (fun b c =>
    let ix := idxs[c]!
    let ps := hs.map (LookG.prep ix)
    chromG ix R gbs c P Ls ps (ordG (ps.map (LookG.size ix)) m) b) (initP P)

/-- Reads the general fast path takes: enough seeds for the bound. -/
def fastT (P : Nat) (R : ByteArray) : Bool := decide (0 < R.size / 25) && decide (sbound P < R.size / 25)

/-- Slow proved path at threshold `T`. -/
def slowMapT (T : Int) (gbs : Array ByteArray) (R : ByteArray) : Option (Window × Int) :=
  let g := decodeGenomeB gbs
  let read := decodeBytes R
  let l0 := read.length / (errBound sc0 T + 1)
  mapWith (scanLookup g l0) (kernelScore sc0 read g) l0 T (errBound sc0 T) g read

/-- Map one read at threshold `T = −P`. -/
@[specialize] def mapFastTG {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) : Option (Window × Int) :=
  if fastT P R then
    match resultP P (mapChromsG P R gbs idxs) with
    | some (c, st, len, pen) => some (⟨c, st, len⟩, -(pen : Int))
    | none => none
  else slowMapT (-(P : Int)) gbs R

end MapSpec.Fast
