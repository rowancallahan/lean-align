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

/-- `catOkV`, one task per chromosome. -/
def catOkVPar (V : GV) (offs : Array Nat) (gbs : Array ByteArray) : Bool :=
  let tasks := (List.range gbs.size).map fun c => Task.spawn (prio := .dedicated) fun _ =>
    decide (offs[c]! + gbs[c]!.size ≤ V.n) && eqRunV V gbs[c]! offs[c]! 0 gbs[c]!.size
  tasks.all (·.get)

theorem catOkVPar_eq (V : GV) (offs : Array Nat) (gbs : Array ByteArray) :
    catOkVPar V offs gbs = catOkV V offs gbs := by
  unfold catOkVPar catOkV
  rw [List.all_map]
  rfl

section
variable {V : GV} {G : ByteArray} (h : RepV V G)
include h

theorem eqRunV_eq (b : ByteArray) : ∀ k i j, eqRunV V b i j k = eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunV, eqRun, h.2, ih]

theorem eqRunV_eqMz (b : ByteArray) : ∀ k i j, eqRunV V b i j k = Mz.eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunV, Mz.eqRun, h.2, ih]

theorem catOkV_eq (offs : Array Nat) (gbs : Array ByteArray) : catOkV V offs gbs = catOk G offs gbs := by
  simp only [catOkV, catOk, h.1, eqRunV_eq h]

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

theorem okAtV_eq (ix : MzIdx) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat) :
    okAtV ix V R s o key bw aw pmo o2 n1 a2 n2 t = Mz.okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t := by
  simp only [okAtV, Mz.okAt, eqRunV_eqMz h, h.1]

theorem scanAV_eq (ix : MzIdx) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ d t acc, hi - t = d → scanAV ix V R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =
      scanA ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanAV scanA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro t acc hd
    unfold scanAV scanA
    have ih' := fun acc => ih (t + 1) acc (by omega)
    simp only [show t < hi from by omega, if_true, okAtV_eq h, ih']

theorem scanEdgeAV_eq (ix : MzIdx) (R : ByteArray) (side d0 s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanEdgeAV ix V R side d0 s base bit i acc = scanEdgeA ix G R side d0 s base bit i acc := by
  intro d
  induction d with
  | zero => intro i acc hd; unfold scanEdgeAV scanEdgeA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i acc hd
    unfold scanEdgeAV scanEdgeA
    have ih' := fun acc => ih (i + 1) acc (by omega)
    simp only [show i < ix.nr from by omega, if_true, ih', okEdgeV, Mz.okEdge, eqRunV_eqMz h, h.1] <;> rfl

theorem scanRangeAV_eq (R : ByteArray) (s stop base bit : Nat) :
    ∀ d p acc, stop - p = d → scanRangeAV V R s stop base bit p acc = scanRangeA G R s stop base bit p acc := by
  intro d
  induction d with
  | zero => intro p acc hd; unfold scanRangeAV scanRangeA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro p acc hd
    unfold scanRangeAV scanRangeA
    have ih' := fun acc => ih (p + 1) acc (by omega)
    simp only [show p < stop from by omega, if_true, ih', Mz.okIn, eqRunV_eqMz h, h.1] <;> rfl

theorem scanInsideAV_eq (ix : MzIdx) (R : ByteArray) (s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanInsideAV ix V R s base bit i acc = scanInsideA ix G R s base bit i acc := by
  intro d
  induction d with
  | zero => intro i acc hd; unfold scanInsideAV scanInsideA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i acc hd
    unfold scanInsideAV scanInsideA
    have ih' := fun acc => ih (i + 1) acc (by omega)
    simp only [show i < ix.nr from by omega, if_true, ih', scanRangeAV_eq h _ _ _ _ _ _ _ _ rfl]

theorem mzLookSV_eq (ix : MzIdx) (R : ByteArray) (s base : Nat) (p : MzP) :
    mzLookSV ix V R s base p = mzLookS ix G R s base p := by
  simp only [mzLookSV, mzLookS, lookupPV, lookupP, lookupSeedAV, lookupSeedA, lookupCodeAV, lookupCodeA,
    fun ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc =>
      scanAV_eq h ix R s o key bw aw pmo o2 n1 a2 n2 hi base bit _ t acc rfl,
    fun ix R side d0 s base bit i acc => scanEdgeAV_eq h ix R side d0 s base bit _ i acc rfl,
    fun ix R s base bit i acc => scanInsideAV_eq h ix R s base bit _ i acc rfl]

end

end MapSpec.Fast

/-! ## Checker and builder over a view -/

namespace MapSpec.Mz

open MapSpec.Fast (GV RepV)

def wcUV (B : GV) (i stop : Nat) (x : UInt64) : UInt64 :=
  if i < stop then
    let b := B.get i
    if acgt b then wcUV B (i + 1) stop (x * 4 + (byteCode b).toUInt64) else BADU
  else x
termination_by stop - i

def allNotV (B : GV) (i stop : Nat) : Bool :=
  if i < stop then !acgt (B.get i) && allNotV B (i + 1) stop else true
termination_by stop - i

def rollToV (G : GV) : (e : Nat) → UInt64 × Nat
  | 0 => (0, 0)
  | e + 1 => roll (G.get e) (rollToV G e).1 (rollToV G e).2

def compRV (ix : MzIdx) (G : GV) (fill : ByteArray) (last : Nat) :
    (n p : Nat) → (x : UInt64) → (g : Nat) → Bool
  | 0, _, _, _ => true
  | n + 1, p, x, g =>
    let s := roll (G.get (p + q - 1)) x g
    if q ≤ s.2 then
      let v := s.1.toNat
      let o := ix.mini v
      let pm := p + o
      if pm + 1 = last then compRV ix G fill last n (p + 1) s.1 s.2
      else
        let b := ix.hsh (ix.sub v o) >>> ix.kb
        let t := getU32 fill b
        decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf (ix.slot t) == pm &&
          compRV ix G (setU32 fill b (t + 1)) (pm + 1) n (p + 1) s.1 s.2
    else compRV ix G fill last n (p + 1) s.1 s.2

def entryOkV (ix : MzIdx) (G : GV) (b hi t : Nat) : Bool :=
  let e := (ix.slot t)
  let pos := ix.posOf e
  let tg := ix.tagOf e
  let x := wcUV G pos (pos + ix.k) 0
  let h := ix.hsh x.toNat
  let w1 := ix.c
  decide (pos + ix.k ≤ G.n) && x != BADU && (h >>> ix.kb) == b &&
    ix.keyF tg == (h &&& ix.kbM) &&
    (ix.flagF tg != 0 ||
      (decide (w1 ≤ pos) && decide (pos + ix.k + w1 ≤ G.n) &&
        (let bf := wcUV G (pos - w1) pos 0
         let af := wcUV G (pos + ix.k) (pos + ix.k + w1) 0
         bf != BADU && af != BADU && ix.befF tg == bf.toNat && ix.aftF tg == af.toNat))) &&
    (decide (hi ≤ t + 1) || decide (pos < ix.posOf (ix.slot (t + 1))))

def checkBucketV (ix : MzIdx) (G : GV) (b hi : Nat) : (n t : Nat) → Bool
  | 0, _ => true
  | n + 1, t => entryOkV ix G b hi t && checkBucketV ix G b hi n (t + 1)

def checkSoundV (ix : MzIdx) (G : GV) : (n b : Nat) → Bool
  | 0, _ => true
  | n + 1, b =>
    checkBucketV ix G b (ix.hiB b) (ix.hiB b - ix.loB b) (ix.loB b) && checkSoundV ix G n (b + 1)

def runOkV (ix : MzIdx) (G : GV) (i : Nat) : Bool :=
  let a := ix.ra i
  let b := ix.rb i
  decide (a < b) && decide (b ≤ G.n) && allNotV G a b &&
    (decide (b = G.n) || acgt (G.get b)) && (decide (a = 0) || acgt (G.get (a - 1))) &&
    (decide (ix.nr ≤ i + 1) || decide (b < ix.ra (i + 1)))

def checkRunsV (ix : MzIdx) (G : GV) : (n i : Nat) → Bool
  | 0, _ => true
  | n + 1, i => runOkV ix G i && checkRunsV ix G n (i + 1)

def checkCoverV (ix : MzIdx) (G : GV) (c : Nat) : (n x : Nat) → Bool
  | 0, _ => true
  | n + 1, x =>
    if acgt (G.get x) then checkCoverV ix G c n (x + 1)
    else
      let c := advance ix x ix.nr c
      decide (c < ix.nr) && decide (ix.ra c ≤ x) && decide (x < ix.rb c) && checkCoverV ix G c n (x + 1)

/-- `check2` reading a view. -/
def check2V (ix : MzIdx) (G : GV) : Bool :=
  checkParams ix && checkSoundV ix G (2 ^ ix.B) 0 &&
    (let s := rollToV G (q - 1); compRV ix G ix.offs 0 (G.n + 1 - q) 0 s.1 s.2) &&
    checkRunsV ix G ix.nr 0 && checkCoverV ix G 0 G.n 0

/-- `checkSoundV` on `P` tasks (as `checkSoundPar`). -/
def checkSoundParV (ix : MzIdx) (G : GV) (P : Nat) : Bool :=
  let N := 2 ^ ix.B
  let P := max P 1
  let ch := (N + P - 1) / P
  let tasks := (List.range P).map fun j =>
    Task.spawn (prio := .dedicated) fun _ => checkSoundV ix G (min ((j + 1) * ch) N - j * ch) (j * ch)
  tasks.all (·.get)

/-- `check2V` with the per-entry pass on `P` tasks, run beside the sequential passes. -/
def check3V (ix : MzIdx) (G : GV) (P : Nat) : Bool :=
  let seq := Task.spawn (prio := .dedicated) fun _ =>
    (let s := rollToV G (q - 1); compRV ix G ix.offs 0 (G.n + 1 - q) 0 s.1 s.2) &&
      checkRunsV ix G ix.nr 0 && checkCoverV ix G 0 G.n 0
  checkParams ix && checkSoundParV ix G P && seq.get

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

theorem wcUV_eq (stop : Nat) : ∀ d i x, stop - i = d → wcUV V i stop x = wcU G i stop x := by
  intro d
  induction d with
  | zero => intro i x hd; unfold wcUV wcU; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i x hd
    unfold wcUV wcU
    have ih' := fun x => ih (i + 1) x (by omega)
    simp only [show i < stop from by omega, if_true, h.2, ih']

theorem allNotV_eq (stop : Nat) : ∀ d i, stop - i = d → allNotV V i stop = allNot G i stop := by
  intro d
  induction d with
  | zero => intro i hd; unfold allNotV allNot; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i hd
    unfold allNotV allNot
    simp only [show i < stop from by omega, if_true, h.2, ih (i + 1) (by omega)]

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

theorem rollToV_eq : ∀ e, rollToV V e = rollTo G e := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih => simp only [rollToV, rollTo, h.2, ih]

theorem compRV_eq (ix : MzIdx) : ∀ n fill last p x g, compRV ix V fill last n p x g = compR ix G fill last n p x g := by
  intro n
  induction n with
  | zero => intro fill last p x g; rfl
  | succ n ih => intro fill last p x g; simp only [compRV, compR, h.2, ih]

theorem checkSoundV_eq (ix : MzIdx) : ∀ n b, checkSoundV ix V n b = checkSound ix G n b := by
  have eo : ∀ b hi t, entryOkV ix V b hi t = entryOk ix G b hi t := fun b hi t => by
    simp only [entryOkV, entryOk, h.1, fun i stop x => wcUV_eq h stop _ i x rfl]
  have cb : ∀ b hi n t, checkBucketV ix V b hi n t = checkBucket ix G b hi n t := fun b hi n => by
    induction n with
    | zero => intro t; rfl
    | succ n ih => intro t; simp only [checkBucketV, checkBucket, eo, ih]
  intro n
  induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; simp only [checkSoundV, checkSound, cb, ih]

theorem checkRunsV_eq (ix : MzIdx) : ∀ n i, checkRunsV ix V n i = checkRuns ix G n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    simp only [checkRunsV, checkRuns, runOkV, runOk, h.1, h.2, ih, fun i stop => allNotV_eq h stop _ i rfl]

theorem checkCoverV_eq (ix : MzIdx) : ∀ n c x, checkCoverV ix V c n x = checkCover ix G c n x := by
  intro n
  induction n with
  | zero => intro c x; rfl
  | succ n ih => intro c x; simp only [checkCoverV, checkCover, h.2, ih]

theorem check2V_eq' (ix : MzIdx) : check2V ix V = check2 ix G := by
  simp only [check2V, check2, checkSoundV_eq h, rollToV_eq h, compRV_eq h, checkRunsV_eq h,
    checkCoverV_eq h, h.1]

theorem check3V_eq' (ix : MzIdx) (P : Nat) : check3V ix V P = check2 ix G := by
  have e : checkSoundParV ix V P = checkSoundPar ix G P := by
    simp only [checkSoundParV, checkSoundPar, soundChunk, checkSoundV_eq h]
  rw [check2_eq, ← check3_eq ix G P]
  simp only [check3V, check3, e, rollToV_eq h, compRV_eq h, checkRunsV_eq h, checkCoverV_eq h, h.1]
  show _ = (checkParams ix && checkSoundPar ix G P && _ && _ && _)
  simp only [Bool.and_assoc]
  rfl

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

theorem check2V_eq (ix : MzIdx) (V : GV) : check2V ix V = check2 ix (Fast.unpackV V) :=
  check2V_eq' (Fast.repV_unpack V) ix

theorem check3V_eq (ix : MzIdx) (V : GV) (P : Nat) : check3V ix V P = check2V ix V := by
  rw [check3V_eq' (Fast.repV_unpack V), check2V_eq]

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

/-- A mapper whose index ignores `G` gives the same answers for any `G`. -/
theorem pairFastGB_congrG (P lo hi : Nat) (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    pairFastGB P lo hi ix G offs gbs R1 R2 = pairFastGB P lo hi ix G' offs gbs R1 R2 := by
  simp only [pairFastGB, mapFastGB, mapChromsGB, ilG_congrG ix G G' hG]

end

/-- **Proper pairs, whole genome held once.**  Chromosomes `gbs` (byte-encoded),
the view `V` checked against them (`catOkV`), and a minimizer index passing the
checker over the view: the mapper (run with an empty `G`) is `pairSpec`. -/
theorem pairFastGB_view_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : Mz.MzIdx) (V : GV) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOkV V offs gbs = true)
    (hchk : Mz.check2V ix V = true) :
    pairFastGB P lo hi (ix, V) ByteArray.empty offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  have hr := repV_unpack V
  rw [pairFastGB_congrG (ix, V) ByteArray.empty (unpackV V) (fun _ _ _ _ => rfl)]
  refine pairFastGB_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 (ix, V) (unpackV V) offs hg h1 h2
    (by rw [← catOkV_eq hr]; exact hcat) ?_
  intro R' s base _
  show LookOkS _ R' s base 0 (mzLookSV ix V R' s base (mzPrep ix (seedHashAt R' s)))
  rw [mzLookSV_eq hr]
  exact mzLookS_ok ix _ R' s base (by rw [← Mz.check2_eq, ← Mz.check2V_eq]; exact hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.catOkVPar_eq
#print axioms MapSpec.Mz.check3V_eq
#print axioms MapSpec.Mz.buildWV_eq
#print axioms MapSpec.Fast.pairFastGB_view_eq_pairSpec
