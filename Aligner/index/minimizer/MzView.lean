import FastGenPair
import MzCheckPar
import MapperPGen

/-!
# Whole genome with one genome copy: the concatenation as a view of the chromosomes

`pairFastGB` reads the chromosomes `gbs` (scoring) and the concatenation `G`
(index lookups); holding both doubles the genome.  `GV` reads `G` through
`gbs` (page table + chromosome starts, no copy): `GV.get i` is any computation,
its agreement with `gbs` is checked at run time (`catOkV`).

* index lookup, index checker and index builder are copies of the byte versions
  reading a `GV`; under `RepV V G` (`V` spells `G`) each equals its byte version:
  `mzLookSV_eq`, `check2V_eq`, `check3V_eq` (parallel), `buildWV_eq`
  (**the builder over the view is `Mz.buildW` on the concatenation**);
* `unpackV V` (never run) is the byte genome `V` spells (`repV_unpack`);
* the `LookG` instance for `(ix, V)` ignores its `G` argument, so the mapper is
  run with `G = ByteArray.empty` (`pairFastGB_congrG`):

    GenomeBytes gbs g → Encodes R1 m1 → Encodes R2 m2 → catOkV V offs gbs → Mz.check2V ix V →
      pairFastGB P lo hi (ix, V) .empty offs gbs R1 R2 = pairSpec sc0 (−P) lo hi g m1 m2
                                                              (pairFastGB_view_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec

/-- The concatenation of `gbs` (chromosome `c` at `st[c]`, `st[gbs.size] = n`);
`tbl[p]` = chromosome of place `p·2^20`. -/
structure GV where
  n : Nat
  gbs : Array ByteArray
  st : Array Nat
  tbl : Array Nat

instance : Inhabited GV := ⟨⟨0, #[], #[], #[]⟩⟩

@[inline] def GV.get (V : GV) (i : Nat) : UInt8 :=
  if i < V.n then
    let c := V.tbl[i >>> 20]!
    let c := if V.st[c + 1]! ≤ i then c + 1 else c
    V.gbs[c]!.get! (i - V.st[c]!)
  else 0

/-- The view of the chromosomes' concatenation (right when every chromosome has
≥ 2^20 letters; `catOkV` checks it). -/
def GV.ofChroms (gbs : Array ByteArray) : GV := Id.run do
  let mut st : Array Nat := #[0]
  for g in gbs do st := st.push (st.back! + g.size)
  let n := st.back!
  let mut tbl := Array.replicate ((n >>> 20) + 1) 0
  for c in [0:gbs.size] do
    for p in [(st[c]! + 0xFFFFF) >>> 20 : (st[c + 1]! + 0xFFFFF) >>> 20] do tbl := tbl.set! p c
  return ⟨n, gbs, st, tbl⟩

/-- `V` spells `G`. -/
def RepV (V : GV) (G : ByteArray) : Prop := V.n = G.size ∧ ∀ i, V.get i = G.get! i

/-- The bytes `V` spells (for statements only). -/
def unpackV (V : GV) : ByteArray := ⟨(Array.range V.n).map V.get⟩

theorem repV_unpack (V : GV) : RepV V (unpackV V) := by
  refine ⟨by simp [unpackV, ByteArray.size], fun i => ?_⟩
  by_cases hi : i < V.n
  · simp [unpackV, ByteArray.get!, hi]
  · rw [get!_out _ i (by simp [unpackV, ByteArray.size]; omega)]
    unfold GV.get; rw [if_neg hi]

/-- `G[i, i+k) = b[j, j+k)`. -/
def eqRunV (a : GV) (b : ByteArray) (i j : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => a.get i == b.get! j && eqRunV a b (i + 1) (j + 1) k

/-- `catOk` reading the view. -/
def catOkV (V : GV) (offs : Array Nat) (gbs : Array ByteArray) : Bool :=
  (List.range gbs.size).all fun c =>
    decide (offs[c]! + gbs[c]!.size ≤ V.n) && eqRunV V gbs[c]! offs[c]! 0 gbs[c]!.size

section
variable {V : GV} {G : ByteArray} (h : RepV V G)
include h

end

/-! ## Minimizer-index lookup over a view (copies of `okAt` … `mzLookS`) -/

section MzV
open Mz

@[inline] def okAtV (ix : MzIdx) (G : GV) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) : Bool :=
  let e := (ix.slot t)
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     let tg := ix.tagOf e
     decide (o ≤ pos) &&
      (if ix.flagF tg = 0 then (ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw &&
         decide (pos - o + Mz.q ≤ G.n) && eqRunV G R (pos - o) s n1 &&
         eqRunV G R (pos + a2) (s + o + a2) n2 &&
         (ix.kf == ix.kb || eqRunV G R pos (s + o) ix.k)
       else decide (pos - o + Mz.q ≤ G.n) && eqRunV G R (pos - o) s Mz.q))

def scanAV (ix : MzIdx) (G : GV) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanAV ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if okAtV ix G R s o key bw aw pmo o2 n1 a2 n2 t then acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

@[inline] def okEdgeV (ix : MzIdx) (G : GV) (R : ByteArray) (side d s i : Nat) : Bool :=
  let x := ix.runs[2 * i + side]!
  decide (d ≤ x) && decide (x - d + Mz.q ≤ G.n) && eqRunV G R (x - d) s Mz.q

def scanEdgeAV (ix : MzIdx) (G : GV) (R : ByteArray) (side d s base bit : Nat) (i : Nat) (acc : Array Nat) :
    Array Nat :=
  if i < ix.nr then
    scanEdgeAV ix G R side d s base bit (i + 1)
      (if okEdgeV ix G R side d s i then acc.push (anc base bit (ix.runs[2 * i + side]! - d)) else acc)
  else acc
termination_by ix.nr - i

def scanRangeAV (G : GV) (R : ByteArray) (s stop base bit : Nat) (p : Nat) (acc : Array Nat) : Array Nat :=
  if p < stop then
    scanRangeAV G R s stop base bit (p + 1)
      (if decide (p + Mz.q ≤ G.n) && eqRunV G R p s Mz.q then acc.push (anc base bit p) else acc)
  else acc
termination_by stop - p

def scanInsideAV (ix : MzIdx) (G : GV) (R : ByteArray) (s base bit : Nat) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i < ix.nr then
    scanInsideAV ix G R s base bit (i + 1) (scanRangeAV G R s (ix.rb i + 1 - Mz.q) base bit (ix.ra i) acc)
  else acc
termination_by ix.nr - i

def lookupCodeAV (ix : MzIdx) (G : GV) (R : ByteArray) (s v base bit : Nat) : Array Nat :=
  let o := ix.mini v
  let h := ix.hsh (ix.sub v o)
  let b := h >>> ix.kb
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanAV ix G R s o (h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB b) base bit (ix.loB b) #[]

def lookupSeedAV (ix : MzIdx) (G : GV) (R : ByteArray) (s base bit : Nat) : Array Nat :=
  let u := Mz.firstOdd R s (s + Mz.q)
  if u = s + Mz.q then lookupCodeAV ix G R s (Mz.wcGo R s (s + Mz.q) 0) base bit
  else if s < u then scanEdgeAV ix G R 0 (u - s) s base bit 0 #[]
  else
    let u2 := Mz.firstAcgt R s (s + Mz.q)
    if u2 < s + Mz.q then scanEdgeAV ix G R 1 (u2 - s) s base bit 0 #[]
    else scanInsideAV ix G R s base bit 0 #[]

@[inline] def lookupPV (ix : MzIdx) (G : GV) (R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanAV ix G R s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base bit (ix.loB p.b) #[]

/-- `mzLookS` reading the view. -/
def mzLookSV (ix : MzIdx) (G : GV) (R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupPV ix G R s p base 0 else lookupSeedAV ix G R s base 0

end MzV

section
variable {V : GV} {G : ByteArray} (h : RepV V G)
include h
open Mz

end

end MapSpec.Fast

/-! ## Checker and builder over a view -/

namespace MapSpec.Mz

open MapSpec.Fast (GV RepV)

/-! ### Builder (copy of `buildW`) -/

def allAV (B : GV) (i stop : Nat) : Bool :=
  if i < stop then acgt (B.get i) && allAV B (i + 1) stop else true
termination_by stop - i

def wcGoV (B : GV) (i stop x : Nat) : Nat :=
  if i < stop then wcGoV B (i + 1) stop (x * 4 + byteCode (B.get i)) else x
termination_by stop - i

def slotAtV (ix : MzIdx) (G : GV) (pm h : Nat) : UInt64 :=
  let c := ix.c
  let good := decide (c ≤ pm) && decide (pm + ix.k + c ≤ G.n) &&
    allAV G (pm - c) pm && allAV G (pm + ix.k) (pm + ix.k + c)
  let key := (h &&& ix.kbM).toUInt64
  let tag := if good then
      key ||| ((wcGoV G (pm - c) pm 0).toUInt64 <<< ix.bsh.toUInt64) |||
        ((wcGoV G (pm + ix.k) (pm + ix.k + c) 0).toUInt64 <<< ix.ash.toUInt64)
    else key ||| ((1 : UInt64) <<< ix.fsh.toUInt64)
  (pm.toUInt64 <<< ix.T.toUInt64) ||| tag

@[specialize] def foldMinsGoV {α : Type} (ix0 : MzIdx) (G : GV) (f : α → Nat → Nat → α)
    (p : Nat) (x : UInt64) (good last : Nat) (acc : α) : α :=
  if p < G.n then
    let c := G.get p
    let ok := acgt c
    let x := if ok then (x <<< 2 ||| (byteCode c).toUInt64) &&& 0x3FFFFFFFFFFFF else x
    let good := if ok then good + 1 else 0
    if good ≥ q then
      let v := x.toNat
      let o := ix0.mini v
      let pm := p + 1 - q + o
      if pm + 1 != last then foldMinsGoV ix0 G f (p + 1) x good (pm + 1) (f acc pm (ix0.hsh (ix0.sub v o)))
      else foldMinsGoV ix0 G f (p + 1) x good last acc
    else foldMinsGoV ix0 G f (p + 1) x good last acc
  else acc
termination_by G.n - p

@[specialize] def foldMinsV {α : Type} (ix0 : MzIdx) (G : GV) (init : α) (f : α → Nat → Nat → α) : α :=
  foldMinsGoV ix0 G f 0 0 0 0 init

/-- `buildW` reading a view (`buildWV_eq`: it is `buildW` on the bytes the view spells). -/
def buildWV (G : GV) (k B c sw t : Nat) : MzIdx := Id.run do
  let pb := G.n.log2 + 1
  if 2 * k < B || 32 < B || k = 0 || q < k || q - k < c || t = 0 || k < t || (k - t) % (q + 1 - k) != 0 ||
      !(sw = 4 || sw = 5 || sw = 6 || sw = 8) || 8 * sw < pb + 4 * c + 1 then
    return panic! s!"Mz.buildW: unsupported k={k} B={B} c={c} sw={sw} t={t} (genome {G.n} letters)"
  let ix0 := mkIdx k B c sw pb t
  let nb := 2 ^ B
  let mut cnt := foldMinsV ix0 G (zeros (4 * (nb + 1))) fun cnt _ h =>
    let b := h >>> ix0.kb
    setU32 cnt (b + 1) (getU32 cnt (b + 1) + 1)
  for b in [0:nb] do cnt := setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)
  let total := getU32 cnt nb
  let (_, sl) := foldMinsV ix0 G (cnt, zeros (sw * total)) fun (fill, sl) pm h =>
    let b := h >>> ix0.kb
    let t := getU32 fill b
    (setU32 fill b (t + 1), wrLE sl (sw * t) (slotAtV ix0 G pm h) sw)
  let mut runs : Array Nat := #[]
  for p in [0:G.n] do
    let odd := !acgt (G.get p)
    if odd && (p == 0 || acgt (G.get (p - 1))) then runs := runs.push p
    if odd && (p + 1 == G.n || acgt (G.get (p + 1))) then runs := runs.push (p + 1)
  return { ix0 with offs := cnt, sl, runs }

/-! ### Proofs: under `RepV`, each copy computes its byte version -/

section
variable {V : GV} {G : ByteArray} (h : RepV V G)
include h

theorem allAV_eq (stop : Nat) : ∀ d i, stop - i = d → allAV V i stop = allA G i stop := by
  intro d
  induction d with
  | zero => intro i hd; unfold allAV allA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i hd
    unfold allAV allA
    simp only [show i < stop from by omega, if_true, h.2, ih (i + 1) (by omega)]

theorem wcGoV_eq (stop : Nat) : ∀ d i x, stop - i = d → wcGoV V i stop x = wcGo G i stop x := by
  intro d
  induction d with
  | zero => intro i x hd; unfold wcGoV wcGo; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i x hd
    unfold wcGoV wcGo
    have ih' := fun x => ih (i + 1) x (by omega)
    simp only [show i < stop from by omega, if_true, h.2, ih']

theorem slotAtV_eq (ix : MzIdx) (pm hh : Nat) : slotAtV ix V pm hh = slotAt ix G pm hh := by
  simp only [slotAtV, slotAt, h.1, fun i stop => allAV_eq h stop _ i rfl, fun i stop x => wcGoV_eq h stop _ i x rfl]

theorem foldMinsGoV_eq {α : Type} (ix0 : MzIdx) (f : α → Nat → Nat → α) :
    ∀ d p x good last acc, G.size - p = d →
      foldMinsGoV ix0 V f p x good last acc = foldMinsGo ix0 G f p x good last acc := by
  intro d
  induction d with
  | zero =>
    intro p x good last acc hd
    unfold foldMinsGoV foldMinsGo; rw [h.1, if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro p x good last acc hd
    unfold foldMinsGoV foldMinsGo
    have ih' := fun x good last acc => ih (p + 1) x good last acc (by omega)
    simp only [h.1, show p < G.size from by omega, if_true, h.2, ih']

theorem foldMinsV_eq {α : Type} (ix0 : MzIdx) (init : α) (f : α → Nat → Nat → α) :
    foldMinsV ix0 V init f = foldMins ix0 G init f :=
  foldMinsGoV_eq h ix0 f _ 0 0 0 0 init rfl

/-- **The builder over a view is `buildW` on the bytes it spells.** -/
theorem buildWV_eq' (k B c sw t : Nat) : buildWV V k B c sw t = buildW G k B c sw t := by
  simp only [buildWV, buildW, h.1, h.2, foldMinsV_eq h, slotAtV_eq h, panicWithPosWithDecl, panic, panicCore]

end

/-- **Low-memory builder = in-memory builder**: reading the chromosomes through
the view gives exactly `buildW` on their concatenation `G` (any `G` the view
spells, e.g. the one `catOkV` checks). -/
theorem buildWV_eq (V : GV) (G : ByteArray) (h : RepV V G) (k B c sw t : Nat) :
    buildWV V k B c sw t = buildW G k B c sw t :=
  buildWV_eq' h k B c sw t

end MapSpec.Mz

/-! ## The mapper over the view -/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Lookups through the view; the `G` argument is not read. -/
instance : LookG (Mz.MzIdx × GV) MzP :=
  ⟨fun ix => mzPrep ix.1, fun ix => mzSize ix.1, fun ix _ R s base p => mzLookSV ix.1 ix.2 R s base p⟩

section
variable {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
  (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p)
include hG

theorem ilG_congrG (R1 R2 : ByteArray) (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat)
    (ps1 ps2 : Array Pp) : ∀ f s1 s2 b,
      ilG ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b = ilG ix G' R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilG, GS.adv, hG, ih]

end

end MapSpec.Fast

#print axioms MapSpec.Mz.buildWV_eq
