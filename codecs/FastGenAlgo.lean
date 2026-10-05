import FastMapper
import MapperGenBest
import MapperGenScore
import MapperGenLook
import MapperGenSearch
import MapperGen16
import MapperGenShare
import MapperEvents
import MapperBandPrune
import SeedMapper2

/-!
# The general fast mapper: any read length, any threshold `T = −P`

Read `R` of `n` letters, `m = n / 25` seeds of `Ls = n / m ≥ 25` letters (seed
`j` starts at `j·Ls`); the first 25 letters of each seed are looked up in the
25-mer index (`LookG`).  A genome place `p` of seed `j` is the anchor
`D = p + n − j·Ls` (stored as `D·16`); a shape `(a, b)` gives the window
`(D − n − a, n + a + b)`.

Per chromosome (`chromG`), with `lim = min P 16`:

1. `phase1`: seeds in `ord` (smallest bucket first); each anchor's same-length
   window is scored by the kernel `kerH` (exact up to `lim`: `kerG` up to 15,
   `ker16` at 16).  Stop once
   `seedBound sc0 (−min best P)` is below the number of seeds looked up: a
   window that ties or beats the best has a clean seed among them.
2. `stageK`: when one gap fits (`gapBound > 0`), the windows of the shapes
   allowed at the best (`shapes`, without `(0, 0)`), kernel-scored, of the distinct
   anchor diagonals supported by enough seeds (as in stage 3, for `min lim best`).
3. `stageB`: when the best is still above `lim` (`P ≥ 17` and nothing `≤ 16`
   found; phase 1 then looks up every seed), the windows of the allowed shapes
   of the anchors supported by at least `#seeds − sbound P` seeds within
   `2·gapBound` diagonals, scored exactly by the banded kernel (`bandScore`),
   which also covers windows with two gap runs.  (A window within penalty `P`
   leaves at most `sbound P` looked-up seeds without a clean anchor near it.)

The best is carried over the chromosomes (`mapChromsG`); `mapFastTG` falls
back to the slow proved path when the read has too few seeds
(`seedBound sc0 T ≥ m`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Penalty through the banded kernel: exact at `T = −P` (`P + 1` = not a hit). -/
@[inline] def bandPen {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (w : Window) : Nat :=
  match bandScore sc0 (-(P : Int)) (bandOf sc0 (-(P : Int))) R gbs w with
  | some s => if -(P : Int) ≤ s then (-s).toNat else P + 1
  | none => P + 1

/-- The kernel capped at `17`: exact up to `15` by `kerG`; above, `16` for four
mismatches at the same length or an exact two-gap walk (`twoGapB`), else `16`
only when `filt16` passes, and then the banded kernel decides. -/
@[inline] def ker16 {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c st len : Nat) : Nat :=
  let k := kerG R gbs[c]! st len 15
  if k ≤ 15 then k
  else if st + len ≤ GRead.size gbs[c]! ∧ len = R.size ∧ hamming R gbs[c]! st 4 0 R.size 0 = 4 then 16
  else if st + len ≤ GRead.size gbs[c]! ∧ twoGapB R gbs[c]! st len = true then 16
  else if filt16 R gbs[c]! st len then bandPen 16 R gbs ⟨c, st, len⟩ else 17

/-- The kernel capped at `l + 1` (`l ≤ 16`). -/
@[inline] def kerH {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c st len l : Nat) : Nat :=
  if l ≤ 15 then kerG R gbs[c]! st len l else ker16 R gbs c st len

/-- Add window `(st, len)` scored by the kernel capped at `min lim best` (a window
above the best cannot change it; the best's own window is not scored again). -/
@[inline] def addK {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c lim : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then
    if b.pen ≤ lim ∧ b.chr = c ∧ b.st = st.toNat ∧ b.len = len.toNat then b else
    let l := min lim b.pen
    let r := kerH R gbs c st.toNat len.toNat l
    if r ≤ l then b.add c st.toNat len.toNat r else b
  else b

@[inline] def addB {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (c : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then b.add c st.toNat len.toNat (bandPen P R gbs ⟨c, st.toNat, len.toNat⟩) else b

/-- The seed count for the penalty bound `x`: how many seeds a window within
penalty `x` can spoil. -/
def sbTbl : Array Nat := ((List.range 33).map fun (x : Nat) => seedBoundE sc0 (-(x : Int))).toArray

/-- (`sbound_def`: `seedBoundE sc0 (−x)` = `x / 4`, events counted; from a table below `33`.) -/
@[inline] def sbound (x : Nat) : Nat := if x < 33 then sbTbl[x]! else seedBoundE sc0 (-(x : Int))

/-- Look up the seeds of `ord`; each anchor's same-length window goes through the
kernel.  Returns the best, the anchor arrays and the seeds looked up (newest first). -/
def phase1 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (R : ByteArray) (gbs : Array ByteArray) (c P lim Ls : Nat)
    (ps : Array Pp) : (ord : List Nat) → List Nat → List (Array Nat) → Best → Best × List (Array Nat) × List Nat
  | [], J, acc, b => (b, acc, J)
  | j :: rest, J, acc, b =>
    let arr := LookG.look ix gbs[c]! R (j * Ls) (R.size - j * Ls) ps[j]!
    let b := arr.foldl (fun b e => addK R gbs c lim ((e / 16 : Nat) - (R.size : Int)) R.size b) b
    if sbound (min b.pen P) < J.length + 1 ∧ (b.pen ≤ lim ∨ lim = P) then (b, arr :: acc, j :: J)
    else phase1 ix R gbs c P lim Ls ps rest (j :: J) (arr :: acc) b

/-- Window of anchor `e` and shape `sh`: start and length. -/
@[inline] def wst (n e : Nat) (sh : Int × Int) : Int := ((e / 16 : Nat) : Int) - n - sh.1
@[inline] def wlen (n : Nat) (sh : Int × Int) : Int := (n : Int) + sh.1 + sh.2

/-- The distinct diagonals of the anchors. -/
def diags (acc : List (Array Nat)) : List Nat :=
  dedupAdj ((acc.flatMap fun arr => arr.toList.map (· / 16)).mergeSort fun a b => decide (a ≤ b))

/-- Window of diagonal `D` and shape `sh`: start and length. -/
@[inline] def dst (n D : Nat) (sh : Int × Int) : Int := (D : Int) - n - sh.1

@[specialize] def stageK {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (b : Best) : Best :=
  ds.foldl (fun b D => shs.foldl (fun b sh => addK R gbs c lim (dst R.size D sh) (wlen R.size sh) b) b) b

/-! ### Stage K with shared profiles

The kernels with the start diagonal's profile `pf` and the end diagonal's `pb`
passed in (`kerHP_eq`: with the true profiles they are `kerH`); stage K computes
the profiles of each diagonal's `2d + 1` start and end diagonals once
(`stageKP_eq`: it is `stageK`). -/

@[inline] def kerGP {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (st len lim : Nat) (pf pb : Nat × Nat × Nat) : Nat :=
  if st + len ≤ GRead.size G then
    if len = R.size then
      let h := hamming R G st (lim / 4) 0 R.size 0
      if 4 * h ≤ lim then 4 * h else lim + 1
    else gappedPen2P R G st len lim pf.1 pf.2.1 pb.1 pb.2.1
  else lim + 1

@[inline] def ker16P {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c st len : Nat) (pf pb : Nat × Nat × Nat) : Nat :=
  let k := kerGP R gbs[c]! st len 15 pf pb
  if k ≤ 15 then k
  else if st + len ≤ GRead.size gbs[c]! ∧ len = R.size ∧ hamming R gbs[c]! st 4 0 R.size 0 = 4 then 16
  else if st + len ≤ GRead.size gbs[c]! ∧ twoGapBP R gbs[c]! st len pf.1 pb.1 = true then 16
  else if filt16P R gbs[c]! st len pf.1 pb.1 pf.2.2 pb.2.2 then bandPen 16 R gbs ⟨c, st, len⟩ else 17

@[inline] def kerHP {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c st len l : Nat) (pf pb : Nat × Nat × Nat) : Nat :=
  if l ≤ 15 then kerGP R gbs[c]! st len l pf pb else ker16P R gbs c st len pf pb

@[inline] def addKP {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c lim : Nat) (st len : Int) (pf pb : Nat × Nat × Nat)
    (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then
    if b.pen ≤ lim ∧ b.chr = c ∧ b.st = st.toNat ∧ b.len = len.toNat then b else
    let l := min lim b.pen
    let r := kerHP R gbs c st.toNat len.toNat l pf pb
    if r ≤ l then b.add c st.toNat len.toNat r else b
  else b

/-- Largest shift of the shapes. -/
def shapeR (shs : List (Int × Int)) : Nat := shs.foldl (fun m sh => max m (max sh.1.natAbs sh.2.natAbs)) 0

@[specialize] def stageKP {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c lim : Nat) (shs : List (Int × Int)) (ds : List Nat)
    (b : Best) : Best :=
  let d := shapeR shs
  ds.foldl (fun b (D : Nat) =>
    let FA := (Array.range (2 * d + 1)).map fun (i : Nat) => fwdProf R gbs[c]! ((D : Int) - R.size - ((i : Int) - d)).toNat
    let BA := (Array.range (2 * d + 1)).map fun (i : Nat) => bwdProf R gbs[c]! ((D : Int) + ((i : Int) - d)).toNat
    shs.foldl (fun b sh => addKP R gbs c lim (dst R.size D sh) (wlen R.size sh)
      FA[(sh.1 + d).toNat]! BA[(sh.2 + d).toNat]! b) b) b

/-- Penalty of window `(·, len)` from the banded rows `opt` ending where it ends
(`fits`: the window fits the chromosome); `bandPenE_eq`: this is `bandPen`. -/
@[inline] def bandPenE (P n len : Nat) (fits : Bool) (opt : Option (Array Int)) : Nat :=
  if fits ∧ n ≤ len + bandOf sc0 (-(P : Int)) ∧ len ≤ n + bandOf sc0 (-(P : Int)) then
    match opt with
    | some A =>
      let s := A[len + bandOf sc0 (-(P : Int)) - n + 1]!
      if -(P : Int) ≤ s then (-s).toNat else P + 1
    | none => P + 1
  else P + 1

/-- The last `k` letters of read block `[a, a + 25)` occur at `p + 25 - k …`. -/
def blockEq {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (a p : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => R.get! (a + 25 - (k + 1)) == GRead.get G (p + 25 - (k + 1)) && blockEq R G a p k

/-- Read block `[a, a + 25)` occurs in `G` at one of `lo, lo + 1, …, lo + t − 1`. -/
def anyCopy {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (a : Nat) (lo : Int) : Nat → Bool
  | 0 => false
  | t + 1 =>
    (decide (0 ≤ lo + t) && decide ((lo + t).toNat + 25 ≤ GRead.size G) && blockEq R G a (lo + t).toNat 25) ||
      anyCopy R G a lo t

/-- Spoiled blocks of diagonal `D` (end shifts within `d`, band `B`): read block `j`
has no exact copy at any position a band cell of any end `D ± d` can reach. -/
def spoiledArr {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (D d B : Nat) : Array Bool :=
  (Array.range (R.size / 25)).map fun j =>
    !anyCopy R G (25 * j) ((D : Int) - d - R.size + (25 * j : Nat) - B) (2 * (d + B) + 1)

/-- Largest end shift. -/
def shiftMax (bs : List Int) : Nat := bs.foldl (fun m bb => max m bb.natAbs) 0

/-- Banded rows ending at `D + bb` (`D` a diagonal, `bb` an end shift), pruned by the
spoiled blocks `sp` (`bandEndP_spec`). -/
@[inline] def bandEndAt {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (c D : Nat)
    (sp : Nat → Bool) (bb : Int) : Option (Array Int) :=
  bandEndP (-(P : Int)) (bandOf sc0 (-(P : Int))) sp R gbs[c]! ((D : Int) + bb).toNat

/-- Add the window of diagonal `D` and shape `sh`, read from the rows `opt`. -/
@[inline] def addBS {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (c D : Nat) (opt : Option (Array Int))
    (b : Best) (sh : Int × Int) : Best :=
  let st : Int := (D : Int) - R.size - sh.1
  let len : Int := (R.size : Int) + sh.1 + sh.2
  if 0 ≤ st ∧ 0 ≤ len then
    b.add c st.toNat len.toNat (bandPenE P R.size len.toNat (decide (st.toNat + len.toNat ≤ GRead.size gbs[c]!)) opt)
  else b

/-- One diagonal and end shift: one banded pass, every shape with that end. -/
@[inline] def stageBD {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (c : Nat) (shs : List (Int × Int))
    (D : Nat) (sp : Nat → Bool) (b : Best) (bb : Int) : Best :=
  if 0 ≤ (D : Int) + bb then (shs.filter (·.2 == bb)).foldl (addBS P R gbs c D (bandEndAt P R gbs c D sp bb)) b
  else b

/-- The band stage over diagonals `ds` and end shifts `bs`. -/
@[specialize] def stageB {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (R : ByteArray) (gbs : Array Gt) (c : Nat) (shs : List (Int × Int))
    (bs : List Int) (ds : List Nat) (b : Best) : Best :=
  ds.foldl (fun b D =>
    let A := spoiledArr R gbs[c]! D (shiftMax bs) (bandOf sc0 (-(P : Int)))
    bs.foldl (stageBD P R gbs c shs D fun j => A[j]?.getD false) b) b

/-- Seeds (anchor arrays) with an anchor within `r` diagonals of `D`. -/
def suppA (acc : List (Array Nat)) (D r : Nat) : Nat :=
  (acc.filter fun arr => anyNear arr (D - r) (D + r)).length

/-- The distinct diagonals of the anchors, supported by at least `need` seeds within `r`. -/
def diagsB (acc : List (Array Nat)) (need r : Nat) : List Nat :=
  (diags acc).filter fun D => decide (need ≤ suppA acc D r)

/-- End shifts `−d … d`. -/
def shifts (d : Nat) : List Int := (List.range (2 * d + 1)).map fun (i : Nat) => (i : Int) - d

/-- Shapes allowed within penalty `x`, fewest gap letters first (an indel hit found
early lowers the best and makes the remaining kernel calls cheap). -/
@[inline] def shapesAt (x : Nat) : List (Int × Int) :=
  (shapes (gapBound sc0 (-(x : Int))) (gapBound2 sc0 (-(x : Int)))).mergeSort
    fun u v => decide (u.1.natAbs + u.2.natAbs ≤ v.1.natAbs + v.2.natAbs)

/-- `shapesAt x` and its gapped shapes for `x < 33`, computed once (`shapesT_eq`, `shapesKT_eq`). -/
def shapesTbl : Array (List (Int × Int) × List (Int × Int)) :=
  ((List.range 33).map fun x => (shapesAt x, (shapesAt x).filter (· != (0, 0)))).toArray

@[inline] def shapesT (x : Nat) : List (Int × Int) := if x < 33 then shapesTbl[x]!.1 else shapesAt x

@[inline] def shapesKT (x : Nat) : List (Int × Int) :=
  if x < 33 then shapesTbl[x]!.2 else (shapesAt x).filter (· != (0, 0))

/-- Stages K and B of chromosome `c`, from phase 1's anchor arrays `acc` and best `b1`. -/
@[specialize] def chromKB {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs : Array Gt) (c P : Nat) (acc : List (Array Nat)) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      (if 16 ≤ min lim Q1 then stageKP else stageK) R gbs c lim (shapesKT Q1)
        (diagsB acc (acc.length - sbound (min lim Q1)) (2 * gapBound sc0 (-(Q1 : Int)))) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int))))
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

/-- One chromosome. -/
def chromG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (R : ByteArray) (gbs : Array ByteArray)
    (c P Ls : Nat) (ps : Array Pp) (ord : List Nat) (b : Best) : Best :=
  let r1 := phase1 ix R gbs c P (min P 16) Ls ps ord [] [] b
  chromKB R gbs c P r1.2.1 r1.1

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
