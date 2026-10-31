import MzView
import WgPacked
import PairRegion
import PairRouter
import PairNear
import PairGuarantee
import PairGuarFast
import PairGuarQ
import AlignmentCigarCheck
import TierOpt

/-! # Router helpers the tier router is run with (moved from Testing/benches/WholeGenome.lean, mode RTX).

None of this needs a proof: `tierPair_sound` holds for every `TierCfg`, so these only decide how hard
the router searches. `ceilX` (rarest-seed ceiling diagonal), `heurP` (tier 2 heuristic: banded affine
re-alignment, pair-consistent seeds; its alignments are re-checked by `tierPair` with `checkRuns`),
and `rtxCfg`: the bench's default RTX settings in one place. -/

open MapSpec MapSpec.Fast

namespace TierHeur

def rawLook (ix : Mz.MzIdx) (p : MzP) (base : Nat) : Array Nat := Id.run do
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  let key := p.h &&& ix.kbM
  let bw := (v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!
  let aw := (v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!
  let pmo := ix.pm[m1]!
  let o2 := 2 * (ix.c - m2)
  let mut out : Array Nat := #[]
  let mut sorted := true
  for t in [ix.loB p.b:ix.hiB p.b] do
    let e := ix.slot t
    if (e &&& ix.kbM) == key then
      let pos := ix.posOf e
      let tg := ix.tagOf e
      if o ≤ pos && (ix.flagF tg != 0 || ((ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw)) then
        let a := (pos - o + base) * 16
        if let some l := out.back? then
          if a < l then sorted := false
        out := out.push a
  return if sorted then out else out.qsort (· < ·)


@[inline] def baseCode (b : UInt8) : Nat :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4


def hamD (R Rr : ByteArray) (pgs : Array PGen) (v D lim : Nat) : Nat := Id.run do
  let nc := pgs.size
  let n := R.size
  let Rx := if v < nc then R else Rr
  let G := pgs[v % nc]!
  let st := D - n
  let mut mm := 0
  for i in [0:n] do
    if Rx.get! i != G.get (st + i) then
      mm := mm + 1
      if mm > lim then return mm
  return mm


def interS (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  let mut j := 0
  while i < a.size && j < b.size do
    let x := a[i]!
    let y := b[j]!
    if x < y then i := i + 1
    else if y < x then j := j + 1
    else
      out := out.push x
      i := i + 1
      j := j + 1
  return out


def unionS (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    let x := if i < a.size then a[i]! else 0
    let y := if j < b.size then b[j]! else 0
    let v := if j ≥ b.size || (i < a.size && x ≤ y) then x else y
    if i < a.size && x == v then i := i + 1
    if j < b.size && y == v then j := j + 1
    if out.back? != some v then out := out.push v
  return out


def hitsFS (lim : Nat) (pk : PkMz) (offs : Array Nat) (pgs2 : Array PGen) (n t : Nat) (Rs : ByteArray) :
    Array (Window × Nat) := Id.run do
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG pk Rs m Ls
  let J := (ordG (ps.map (LookG.size pk)) m).take (sbound lim + 2)
  let A := (J.map fun j => (LookG.look pk ByteArray.empty Rs (j * Ls) (Rs.size - j * Ls) ps[j]!).map (· / 16)).toArray
  let cs := if A.size == 1 then A[0]! else if A.size == 2 then interS A[0]! A[1]!
    else unionS (unionS (interS A[0]! A[1]!) (interS A[0]! A[2]!)) (interS A[1]! A[2]!)
  let ny := Rs.size
  let mut out : Array (Window × Nat) := #[]
  for D in cs do
    if D < ny then continue
    let st0 := D - ny
    let mut lo := 0
    let mut hi := n
    while lo + 1 < hi do
      let mid := (lo + hi) / 2
      if offs[mid]! ≤ st0 then lo := mid else hi := mid
    if st0 < offs[lo]! then continue
    let st := st0 - offs[lo]!
    let k := kerHKG Rs K pgs2 pgs2 (t + lo) st ny lim
    if k ≤ lim then out := out.push (⟨t + lo, st, ny⟩, k)
  return out


def hitsFB (lim : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsFS lim pk offs pgs2 n 0 R ++ hitsFS lim pk offs pgs2 n n (revCompK R)).toList.map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

/-- Prototype join: both mates' hit lists, the pairs with score ≥ −Gc (nested filter). -/
def pairsJB (dc : Nat → Nat) (sl lo hi Gc : Nat) (l1 l2 : List (Placement × Int)) : List PairHit :=
  l1.flatMap fun x => l2.filterMap fun y =>
    if properPairU sl lo hi x.1 y.1 && decide (-(Gc : Int) ≤ pairScoreD dc (x, y)) then some (x, y) else none

/-- The ceiling candidate of one mate (bench, untrusted; re-checked by `tierPair`): the best gapless
diagonal `(vc, D, mismatches)` among at most `top` places of the rarest seed (bucket 1 … `BK`, either
strand) that lie inside the chromosome. -/
def ceilX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (BK top : Nat) :
    Option (Nat × Nat × Nat) := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 || top == 0 then return none
  let Ls := n / m
  let nc := pgs.size
  let mut rb : Option (Nat × Nat × Nat) := none   -- (bucket size, strand, block)
  for b in [0:2] do
    let pp := if b == 0 then s.ps else s.pr
    for j in [0:m] do
      let p := pp[j]!
      if p.ok then
        let z := LookG.size pk p
        if z != 0 && z ≤ BK && rb.all (fun r => z < r.1) then rb := some (z, b, j)
  let mut best : Option (Nat × Nat × Nat) := none
  if let some (_, b, j) := rb then
    let Rx := if b == 0 then R else s.Rr
    let pp := if b == 0 then s.ps else s.pr
    let a := LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
    for e in a.extract 0 top do
      let p := e / 16 + j * Ls - n
      let mut lo := 0
      let mut hi := nc
      while lo + 1 < hi do
        let mid := (lo + hi) / 2
        if offs[mid]! ≤ p then lo := mid else hi := mid
      if offs[lo]! ≤ p && p + 25 ≤ offs[lo]! + pgs[lo]!.n then
        let D := e / 16 - offs[lo]!
        if n ≤ D && D ≤ pgs[lo]!.n then
          let v := b * nc + lo
          let lim := match best with | some x => x.2.2 | none => n
          let mm := hamD R s.Rr pgs v D lim
          if mm < lim || best.isNone then best := some (v, D, mm)
  return best

/-! ### Tier 2 heuristic (bench only, unproved search; mode RTX, WG_XH=1)

Ceilings for the pairs left in T2/T3: a gapped (banded affine) re-alignment of gapless ceilings,
pair-consistent diagonals of the mates' rarest seeds, and a search of each mate near its partner's
placement (the proper-pair window).  Every alignment it reports is re-scored by the proved checker
`AlignmentSpec.checkRuns` (`rescoreRuns`) and kept only when the score agrees; floors are untouched. -/

/-- Letters `i …` of `G` pushed onto `out` (`fuel` letters). -/
def winLg (G : PGen) : (fuel i : Nat) → ByteArray → ByteArray
  | 0, _, out => out
  | f + 1, i, out => winLg G f (i + 1) (out.push (G.get i))

/-- Letters `[a, b)` of `G` (cut to `G.n`). -/
def winL (G : PGen) (a b : Nat) : ByteArray :=
  let b := min b G.n
  winLg G (b - a) a (ByteArray.emptyWithCapacity (b - a))

/-- Steps as runs. -/
def runsOf (steps : List AlignmentSpec.Step) : List (AlignmentSpec.Step × Nat) :=
  steps.foldr (fun s acc => match acc with
    | (t, c) :: rest => if s == t then (t, c + 1) :: rest else (s, 1) :: acc
    | [] => [(s, 1)]) []

/-- The cells of `bandDP`, row by row (cell `(i, k)` at `i * K + k` of `H`, `F`, `tb`, all preset to
`INF` / `0`; window column of cell `(i, k)` = `i + k + c0s − SH`, shifted by `SH = 2^20`).  Only cells
that can get under `lim` are written; the previous row's cells under `lim` lie in `[pa, pb)`, this row's
so far in `[nlo, nhi)`.  `false` when a whole row is `≥ lim`.  One loop with its state in (unboxed)
arguments; the arrays stay unshared and are updated in place. -/
def bandCells (X W : @& ByteArray) (K c0s m lim : UInt32) :
    (fuel : Nat) → (i k hl e pa pb nlo nhi : UInt32) → (H F : Array UInt32) → (tb : ByteArray) →
    Array UInt32 × ByteArray × Bool
  | 0, _, _, _, _, _, _, _, _, H, _, tb => (H, tb, true)
  | f + 1, i, k, hl, e, pa, pb, nlo, nhi, H, F, tb =>
    let INF : UInt32 := 16777216
    let SH : UInt32 := 1048576
    if k == K then
      if nlo == K then (H, tb, false)
      else bandCells X W K c0s m lim f (i + 1) 0 INF INF nlo nhi K 0 H F tb
    else
      let col := i + k + c0s
      if col < SH || col > SH + m || k + 1 < pa || (k ≥ pb && hl + 8 ≥ lim && e + 2 ≥ lim) then
        bandCells X W K c0s m lim f i (k + 1) INF INF pa pb nlo nhi H F tb
      else
        let j := (i - 1) * K + k
        let fa := if k + 1 < pb then H[(j + 1).toNat]! + 8 else INF
        let fb := if k + 1 < pb then F[(j + 1).toNat]! + 2 else INF
        let fx := fb < fa
        let fv := if fx then fb else fa
        let ea := hl + 8
        let eb := e + 2
        let ex := eb < ea
        let ev := if ex then eb else ea
        let d := if col > SH && k < pb then
          H[j.toNat]! + (if X.get! (i - 1).toNat == W.get! (col - SH - 1).toNat then 0 else 4) else INF
        let src : UInt8 := if d ≤ ev && d ≤ fv then 0 else if ev ≤ fv then 1 else 2
        let h := if src == 0 then d else if src == 1 then ev else fv
        let byte := src ||| (if ex then 4 else 0) ||| (if fx then 8 else 0)
        let jc := (j + K).toNat
        if h < lim then
          bandCells X W K c0s m lim f i (k + 1) h ev pa pb (if nlo == K then k else nlo) (k + 1)
            (H.set! jc h) (F.set! jc fv) (tb.set! jc byte)
        else
          bandCells X W K c0s m lim f i (k + 1) INF (if ev < lim then ev else INF) pa pb nlo nhi
            H F (tb.set! jc byte)

/-- Banded semi-global affine DP (sc0 penalties: mismatch 4, gap 6 + 2L) of the whole read `X` in the
window letters `W` (free window ends), on the diagonals `s0 − w … s0 + w` (`s0` = read start in `W`):
(start in `W`, length, penalty, runs) when the penalty is `< lim`; stops once a whole row is `≥ lim`. -/
def bandDP (X W : ByteArray) (s0 : Int) (w lim : Nat) : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := Id.run do
  let n := X.size
  let m := W.size
  let K := 2 * w + 1
  let INF : Nat := 1 <<< 24
  let SH : Int := 1048576
  let c0 : Int := s0 - (w : Int)
  if c0 + SH < 0 || c0 > SH || m ≥ 1048576 || n ≥ 1048576 then return none
  let lim := min lim (1 <<< 23)
  -- row 0
  let mut H0 : Array UInt32 := Array.replicate ((n + 1) * K) INF.toUInt32
  let mut pa := K
  let mut pb := 0
  for k in [0:K] do
    let c := c0 + (k : Int)
    if 0 ≤ c && c ≤ (m : Int) then
      H0 := H0.set! k 0
      if pa == K then pa := k
      pb := k + 1
  if pa == K then return none
  -- (`INF − 1`: an array distinct from `H0`, not shared)
  let F0 : Array UInt32 := Array.replicate ((n + 1) * K) (INF.toUInt32 - 1)
  let tb0 : ByteArray := ByteArray.mk (Array.replicate ((n + 1) * K) 0)
  let (H, tb, ok) := bandCells X W K.toUInt32 (c0 + SH).toNat.toUInt32 m.toUInt32 lim.toUInt32 (n * (K + 1))
    1 0 INF.toUInt32 INF.toUInt32 pa.toUInt32 pb.toUInt32 K.toUInt32 0 H0 F0 tb0
  if !ok || H.size != (n + 1) * K then return none
  let cl : Int := c0 + (n : Int)
  let mut bk := K
  let mut bv := INF
  for k in [0:K] do
    let c := cl + (k : Int)
    let hv := H[n * K + k]!.toNat
    if 0 ≤ c && c ≤ (m : Int) && hv < bv then
      bv := hv
      bk := k
  if bk == K || bv ≥ lim then return none
  let mut i := n
  let mut k := bk
  let mut st : Nat := 0
  let mut steps : List AlignmentSpec.Step := []
  let mut fuel := 4 * (n + K) + 8
  while i > 0 && fuel > 0 do
    fuel := fuel - 1
    let byte := tb.get! (i * K + k)
    if st == 0 then
      let src := byte &&& 3
      if src == 0 then
        steps := .diag :: steps
        i := i - 1
      else if src == 1 then st := 1
      else st := 2
    else if st == 1 then
      steps := .gapX :: steps
      if byte &&& 4 == 0 then st := 0
      if k == 0 then return none
      k := k - 1
    else
      steps := .gapY :: steps
      if byte &&& 8 == 0 then st := 0
      i := i - 1
      k := k + 1
  if i > 0 then return none
  let cs := c0 + (k : Int)
  let ce := cl + (bk : Int)
  if cs < 0 || ce < cs then return none
  return some (cs.toNat, (ce - cs).toNat, bv, runsOf steps)

/-- First free slot of the open-addressing table `keys` from slot `s` (`fuel` probes). -/
def vFree (keys : @& Array UInt32) (TM : UInt32) : (fuel : Nat) → (s : UInt32) → UInt32
  | 0, s => s
  | f + 1, s => if keys[s.toNat]! == 0 then s else vFree keys TM f ((s + 1) &&& TM)

/-- The read's `k`-mers (code + 1 → read offset) into the table (`fuel` letters from `i`, `v` letters
since the last non-ACGT; table size `TM + 1`, a power of two). -/
def vIns (X : @& ByteArray) (k : UInt32) (sh : UInt32) (msk : UInt32) (TM : UInt32) :
    (fuel : Nat) → (i v h : UInt32) → (keys offs : Array UInt32) → Array UInt32 × Array UInt32
  | 0, _, _, _, keys, offs => (keys, offs)
  | f + 1, i, v, h, keys, offs =>
    let c := baseCode (X.get! i.toNat)
    if c == 4 then vIns X k sh msk TM f (i + 1) 0 0 keys offs else
    let h := ((h <<< 2) ||| c.toUInt32) &&& msk
    if v + 1 ≥ k then
      let s := vFree keys TM (TM.toNat + 1) ((h * 0x9E3779B1) >>> sh)
      vIns X k sh msk TM f (i + 1) (v + 1) h (keys.set! s.toNat (h + 1)) (offs.set! s.toNat (i + 1 - k))
    else vIns X k sh msk TM f (i + 1) (v + 1) h keys offs

/-- Votes (saturating bytes, index `ps + n − read offset`) of one window `k`-mer `key` (start `ps`) along
its probe chain. -/
def vProbe (keys offs : @& Array UInt32) (TM key ps n : UInt32) :
    (fuel : Nat) → (s : UInt32) → (votes : ByteArray) → ByteArray
  | 0, _, votes => votes
  | f + 1, s, votes =>
    let ks := keys[s.toNat]!
    if ks == 0 then votes else
    if ks == key then
      let t := (ps + n - offs[s.toNat]!).toNat
      let c := votes.get! t
      vProbe keys offs TM key ps n f ((s + 1) &&& TM) (if c < 255 then votes.set! t (c + 1) else votes)
    else vProbe keys offs TM key ps n f ((s + 1) &&& TM) votes

/-- The window scan of `voteD` (`fuel` letters from `p`): the votes of all shared `k`-mers. -/
def vScan (W : @& ByteArray) (keys offs : @& Array UInt32) (n k sh msk TM : UInt32) :
    (fuel : Nat) → (p v h : UInt32) → (votes : ByteArray) → ByteArray
  | 0, _, _, _, votes => votes
  | f + 1, p, v, h, votes =>
    let c := baseCode (W.get! p.toNat)
    if c == 4 then vScan W keys offs n k sh msk TM f (p + 1) 0 0 votes else
    let h := ((h <<< 2) ||| c.toUInt32) &&& msk
    if v + 1 ≥ k then
      vScan W keys offs n k sh msk TM f (p + 1) (v + 1) h
        (vProbe keys offs TM (h + 1) (p + 1 - k) n (TM.toNat + 1) ((h * 0x9E3779B1) >>> sh) votes)
    else vScan W keys offs n k sh msk TM f (p + 1) (v + 1) h votes

/-- The first index of a maximal byte (`fuel` from `i`; best so far `bt` with `bv`). -/
def argMaxB (a : @& ByteArray) : (fuel : Nat) → (i bt : UInt32) → (bv : UInt8) → UInt32 × UInt8
  | 0, _, bt, bv => (bt, bv)
  | f + 1, i, bt, bv =>
    let x := a.get! i.toNat
    if x > bv then argMaxB a f (i + 1) i x else argMaxB a f (i + 1) bt bv

/-- The read start in `W` (shifted by `n`: index `t`, start `t − n`) with the most shared `k`-mers
(`k ≤ 15`) between the read `X` and the window `W`, and its votes. -/
def voteD (X W : ByteArray) (k : Nat) : Option (Nat × Nat) :=
  let n := X.size
  let m := W.size
  if n < k || m < k || k > 15 || n + m ≥ 1 <<< 30 then none else
  let lg := (2 * n).log2 + 2
  let TM : UInt32 := ((1 <<< lg) - 1).toUInt32
  let sh : UInt32 := (32 - lg).toUInt32
  let msk : UInt32 := ((1 : UInt32) <<< (2 * k).toUInt32) - 1
  let (keys, offs) := vIns X k.toUInt32 sh msk TM n 0 0 0 (Array.replicate (1 <<< lg) 0) (Array.replicate (1 <<< lg) 1)
  let votes := vScan W keys offs n.toUInt32 k.toUInt32 sh msk TM m 0 0 0 (ByteArray.mk (Array.replicate (m + n + 1) 0))
  let (bt, bv) := argMaxB votes votes.size 0 0 0
  if bv == 0 then none else some (bt.toNat, bv.toNat)

/-- Gapless mismatches of `X` at start `st` of `W` from letter `i` (`fuel` letters left), stopping at `lim`. -/
def hamWg (X W : ByteArray) (st lim : Nat) : (fuel i mm : Nat) → Nat
  | 0, _, mm => mm
  | f + 1, i, mm =>
    let mm := if X.get! i != W.get! (st + i) then mm + 1 else mm
    if mm ≥ lim then mm else hamWg X W st lim f (i + 1) mm

/-- Gapless mismatches of `X` at start `st` of `W`, stopping at `lim`. -/
@[inline] def hamW (X W : ByteArray) (st lim : Nat) : Nat := hamWg X W st lim X.size 0 0

/-- Mismatches of `X[xi …]` against `W[wi …]` over `fuel` letters. -/
def mmSeg (X W : @& ByteArray) : (fuel xi wi mm : Nat) → Nat
  | 0, _, _, mm => mm
  | f + 1, xi, wi, mm => mmSeg X W f (xi + 1) (wi + 1) (if X.get! xi != W.get! wi then mm + 1 else mm)

/-- Whether the gapless placement of `X` at start `s` of `W` looks like it hides an indel (heuristic
gate of the banded DP): 3 or more mismatches among the first or the last `e` letters, or an end of `e`
letters that matches at least 2 mismatches better on another diagonal within `± w`. -/
def gapHint (X W : ByteArray) (s : Int) (w e : Nat) : Bool := Id.run do
  let n := X.size
  let m := W.size
  if n < 2 * e || s < 0 || s + (n : Int) > (m : Int) then return true
  let st := s.toNat
  let p0 := mmSeg X W e 0 st 0
  let q0 := mmSeg X W e (n - e) (st + n - e) 0
  if p0 ≥ 3 || q0 ≥ 3 then return true
  if p0 == 0 && q0 == 0 then return false
  for d in [1:w + 1] do
    for sg in [0:2] do
      let o : Int := if sg == 0 then s + (d : Int) else s - (d : Int)
      if p0 ≥ 2 && 0 ≤ o && o + (e : Int) ≤ (m : Int) && mmSeg X W e 0 o.toNat 0 + 2 ≤ p0 then return true
      let oq : Int := o + (n : Int) - (e : Int)
      if q0 ≥ 2 && 0 ≤ oq && oq + (e : Int) ≤ (m : Int) && mmSeg X W e (n - e) oq.toNat 0 + 2 ≤ q0 then return true
  return false

/-- A gapped alignment of the oriented read `X` inside letters `[ws, we)` of `G` with penalty `< lim`
(heuristic): reads under 32 letters, the best gapless start (scan); else the diagonal with the most
shared 11-mers (or `sv`, the read start in the window that the
read's seeds give), gapless there, then the banded DP (± `w`) when the gapless penalty is over 8.
(start, length, penalty, runs). -/
def nearY (X : ByteArray) (G : PGen) (ws we w lim bl ge : Nat) (sv : Option Int) (vf : Bool := true) : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := Id.run do
  let n := X.size
  let we := min we G.n
  if n == 0 || we < ws + n then return none
  let mut best : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := none
  let mut lim := lim
  if n < 32 then
    let W := winL G ws we
    for st in [0:W.size + 1 - n] do
      let mm := hamW X W st ((lim + 3) / 4)
      if 4 * mm < lim then
        best := some (ws + st, n, 4 * mm, [(AlignmentSpec.Step.diag, n)])
        lim := 4 * mm
        if mm == 0 then break
    return best
  let s0 : Int ← match sv with
    | some s => pure s
    | none => if !vf then return none else match voteD X (winL G ws we) 11 with
      | some (t, _) => pure ((t : Int) - (n : Int))
      | none => return none
  -- the letters around the diagonal only: [a, b) of G
  let aI : Int := max (ws : Int) ((ws : Int) + s0 - (w : Int))
  let bI : Int := min (we : Int) ((ws : Int) + s0 + (n : Int) + (w : Int))
  if bI ≤ aI then return none
  let a := aI.toNat
  let W := winL G a bI.toNat
  let m := W.size
  let s1 : Int := s0 + (ws : Int) - aI
  if 0 ≤ s1 && s1 + (n : Int) ≤ (m : Int) then
    let mm := hamW X W s1.toNat ((lim + 3) / 4)
    if 4 * mm < lim then
      best := some (a + s1.toNat, n, 4 * mm, [(AlignmentSpec.Step.diag, n)])
      lim := 4 * mm
  if lim > 8 && (ge == 0 || gapHint X W s1 w ge) then
    if let some (cs, len, p, runs) := bandDP X W s1 w (min lim bl) then
      best := some (a + cs, len, p, runs)
  return best

/-- The read start (relative to `ws`) most supported by the read's seeds (strand `pp` of `X`) looked up in
letters `[ws, we)` of chromosome `c` (lookups cut to the region, `mzLookRP`), if any seed lies there. -/
def seedVote (pk : PkMz) (offs : Array Nat) (c ws we : Nat) (X : ByteArray) (pp : Array MzP) : Option Int := Id.run do
  let n := X.size
  let m := n / 25
  if m == 0 then return none
  let Ls := n / m
  let rg : RgMz := (pk, offs[c]! + ws, offs[c]! + we)
  let mut ds : Array Nat := #[]
  for j in [0:m] do
    if pp[j]!.ok then
      for e in LookG.look rg ByteArray.empty X (j * Ls) (n - j * Ls) pp[j]! do
        ds := ds.push (e / 16)
  if ds.isEmpty then return none
  ds := ds.qsort (· < ·)
  let mut bd := ds[0]!
  let mut bc := 0
  let mut i := 0
  while i < ds.size do
    let mut j := i
    while j < ds.size && ds[j]! == ds[i]! do j := j + 1
    if j - i > bc then
      bc := j - i
      bd := ds[i]!
    i := j
  return some ((bd : Int) - (n : Int))

/-- `seedVote` with up to `k` read starts (relative to `ws`): the most supported first, then the next
most supported ones more than `sep` letters from those taken (bench knob WG_XHNK). -/
def seedVoteK (pk : PkMz) (offs : Array Nat) (c ws we : Nat) (X : ByteArray) (pp : Array MzP) (k sep : Nat) : Array Int := Id.run do
  let n := X.size
  let m := n / 25
  if m == 0 || k == 0 then return #[]
  let Ls := n / m
  let rg : RgMz := (pk, offs[c]! + ws, offs[c]! + we)
  let mut ds : Array Nat := #[]
  for j in [0:m] do
    if pp[j]!.ok then
      for e in LookG.look rg ByteArray.empty X (j * Ls) (n - j * Ls) pp[j]! do
        ds := ds.push (e / 16)
  if ds.isEmpty then return #[]
  ds := ds.qsort (· < ·)
  -- groups (count, diagonal), the larger count first (the smaller diagonal on ties, as `seedVote`)
  let mut gs : Array (Nat × Nat) := #[]
  let mut i := 0
  while i < ds.size do
    let mut j := i
    while j < ds.size && ds[j]! == ds[i]! do j := j + 1
    gs := gs.push (j - i, ds[i]!)
    i := j
  gs := gs.qsort (fun x y => x.1 > y.1 || (x.1 == y.1 && x.2 < y.2))
  let mut out : Array Nat := #[]
  for (_, d) in gs do
    if out.size ≥ k then break
    if out.all (fun e => e + sep < d || d + sep < e) then out := out.push d
  return out.map fun (d : Nat) => ((d : Int) - (n : Int) : Int)

/-- Global place `D` (read end, concatenated genome) → chromosome and start of the gapless window of
`n` letters ending there, when it lies inside one chromosome. -/
def locD (offs : Array Nat) (pgs : Array PGen) (D n : Nat) : Option (Nat × Nat) := Id.run do
  if D < n then return none
  let st0 := D - n
  let nc := pgs.size
  let mut lo := 0
  let mut hi := nc
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if offs[mid]! ≤ st0 then lo := mid else hi := mid
  if st0 < offs[lo]! then return none
  let st := st0 - offs[lo]!
  if st + n > pgs[lo]!.n then return none
  return some (lo, st)

/-- Places (read ends `D`, increasing, no repeats) of the `r` rarest seeds of one strand of a read
whose buckets hold 1 … `CK` places (bucket supersets, `rawLook`; checked later by alignment). -/
def seedDs (pk : PkMz) (n : Nat) (pp : Array MzP) (r CK : Nat) : Array Nat := Id.run do
  let m := n / 25
  if m == 0 then return #[]
  let Ls := n / m
  let sel := (((List.range m).filterMap fun j =>
      let z := LookG.size pk pp[j]!
      if pp[j]!.ok && 0 < z && z ≤ CK then some (z, j) else none).mergeSort (fun x y => x.1 ≤ y.1)).take r
  let mut out : Array Nat := #[]
  for (_, j) in sel do
    out := unionS out ((rawLook pk.1 pp[j]! (n - j * Ls)).map (· / 16))
  return out

/-- Pair-consistent seed diagonals: per orientation (mate 1 forward / mate 2 reverse, and the
converse), the places `D` of the `r` rarest seeds of each mate, merge-joined so that the forward
mate's start and the reverse mate's end lie `lo − 16 … hi + 16` apart.  At most `P` pairs
`((vc1, start1), (vc2, start2))` (gapless windows inside a chromosome). -/
def pairSeedX (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (lo hi : Nat) (a b : ByteArray)
    (s1 s2 : PrepM MzP) (r CK P : Nat) : Array ((Nat × Nat) × (Nat × Nat)) := Id.run do
  let nc := pgs.size
  let mut out : Array ((Nat × Nat) × (Nat × Nat)) := #[]
  for o in [0:2] do
    -- o = 0: mate 1 forward (ps), mate 2 reverse (pr); o = 1: mate 2 forward, mate 1 reverse
    let (nF, ppF, nR, ppR) := if o == 0 then (a.size, s1.ps, b.size, s2.pr) else (b.size, s2.ps, a.size, s1.pr)
    let AF := seedDs pk nF ppF r CK
    if AF.isEmpty then continue
    let AR := seedDs pk nR ppR r CK
    let mut j0 := 0
    for dF in AF do
      if out.size ≥ P then break
      if dF < nF then continue
      let sF := dF - nF
      -- reverse mate's end dR with sF + lo − 16 ≤ dR ≤ sF + hi + 16
      while j0 < AR.size && AR[j0]! + 16 < sF + lo do j0 := j0 + 1
      let mut j := j0
      while j < AR.size && AR[j]! ≤ sF + hi + 16 && out.size < P do
        match locD offs pgs dF nF, locD offs pgs AR[j]! nR with
        | some (cF, stF), some (cR, stR) =>
          if cF == cR then
            let f := (cF, stF)
            let rv := (nc + cR, stR)
            out := out.push (if o == 0 then (f, rv) else (rv, f))
        | _, _ => pure ()
        j := j + 1
  return out

/-- Knobs of the tier 2 heuristic. -/
structure HCfg where
  w : Nat := 8        -- band half-width
  r : Nat := 2        -- rarest seeds per mate and strand (pair-consistent diagonals)
  ck : Nat := 2000    -- their bucket limit
  np : Nat := 8       -- pairs of diagonals evaluated
  dl : Nat := 16      -- a proper pair is preferred when its sum is within `dl` of the best sum
  seeds : Bool := true
  near : Bool := true
  band : Bool := true
  sv : Bool := true       -- near the partner: the diagonal from region seed lookups first (else 11-mer votes)
  seedAll : Bool := true  -- pair-consistent seeds when either mate lacks a placement (false: both)
  bl : Nat := 1000000     -- the banded DP looks for penalties under `bl` only
  vf : Bool := true       -- near the partner without a seed in the window: 11-mer votes (else give up)
  kx : Bool := true       -- keep an exact mate (RT's unique best) in place
  ge : Nat := 12          -- the banded DP only where `gapHint` (ends of `ge` letters) flags an indel (0: always)
  nk : Nat := 1           -- near the partner: up to `nk` seed diagonals (`seedVoteK`), the best alignment kept

/-- Re-score `(vc, start, len, pen, runs)` of a read (`R` forward, `Rr` reverse) with `checkRuns`:
the placement when the score is `pen`. -/
def chkAln (pgs : Array PGen) (R Rr : ByteArray) (v st len pen : Nat) (runs : List (AlignmentSpec.Step × Nat)) :
    Option ((Placement × Int) × List (AlignmentSpec.Step × Nat)) :=
  let nc := pgs.size
  let Rx := if v < nc then R else Rr
  if rescoreRuns Rx pgs[v % nc]! st len runs == some (-(pen : Int)) then some ((decB nc ⟨v, st, len⟩, -(pen : Int)), runs)
  else none

/-- The tier 2 heuristic on one pair (`m1`, `m2` from `mateB`): returns the mates with their ceilings
replaced where it found better ones (sources: 5 banded re-alignment of a gapless ceiling, 6 near the
partner, 7 pair-consistent seed diagonals).  The pair kept is the one with the smallest summed ceiling,
a proper pair (`properPairU sl`) preferred within `dl`. -/
def heurP (cfg : HCfg) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (sl lo hi : Nat) (a b : ByteArray)
    (s1 s2 : PrepM MzP) (m1 m2 : MateX) : MateX × MateX := Id.run do
  let nc := pgs.size
  let INF := 1000000
  let ok := fun (m : MateX) => m.pH < INF && m.rs
  let exact := fun (m : MateX) => m.st == "U"
  let keep := fun (m : MateX) => cfg.kx && exact m
  -- 1. gapless ceilings over 8: banded re-alignment around their diagonal
  let refine := fun (R Rr : ByteArray) (m : MateX) => Id.run do
    if !cfg.band || exact m || !ok m || m.pH ≤ 8 then return m
    let some (p, _) := m.pl | return m
    let v := if p.2 == Strand.rev then nc + p.1.chr else p.1.chr
    let G := pgs[p.1.chr]!
    let Rx := if v < nc then R else Rr
    let ws := p.1.start - min p.1.start cfg.w
    let W := winL G ws (p.1.start + p.1.len + cfg.w)
    if cfg.ge != 0 && !gapHint Rx W ((p.1.start - ws : Nat) : Int) cfg.w cfg.ge then return m
    match bandDP Rx W ((p.1.start - ws : Nat) : Int) cfg.w (min m.pH cfg.bl) with
    | some (cs, len, pen, runs) =>
      match chkAln pgs R Rr v (ws + cs) len pen runs with
      | some h => return m.withC h.1 5 h.2
      | none => return m
    | none => return m
  let m1 := refine a s1.Rr m1
  let m2 := refine b s2.Rr m2
  let prop := fun (o : MateX × MateX) => match o.1.pl, o.2.pl with
    | some x, some y => properPairU sl lo hi x.1 y.1
    | _, _ => false
  let mut opts : Array (MateX × MateX) := #[(m1, m2)]
  -- 2. pair-consistent seed diagonals (a mate without a placement)
  if cfg.seeds && (if cfg.seedAll then m1.pl.isNone || m2.pl.isNone else m1.pl.isNone && m2.pl.isNone) then
    let ps := pairSeedX pk offs pgs lo hi a b s1 s2 cfg.r cfg.ck cfg.np
    let mut bestG : Option ((Nat × Nat × Nat) × (Nat × Nat × Nat)) := none
    let mut bsum := INF
    for ((v1, st1), (v2, st2)) in ps do
      let h1 := 4 * hamD a s1.Rr pgs v1 (st1 + a.size) (bsum / 4 + 1)
      if h1 ≥ bsum then continue
      let h2 := 4 * hamD b s2.Rr pgs v2 (st2 + b.size) ((bsum - h1) / 4 + 1)
      if h1 + h2 < bsum then
        bsum := h1 + h2
        bestG := some ((v1, st1, h1), (v2, st2, h2))
    if let some ((v1, st1, h1), (v2, st2, h2)) := bestG then
      let one := fun (R Rr : ByteArray) (v st h : Nat) => Id.run do
        let n := R.size
        let mut r : Option (Nat × Nat × Nat × List (AlignmentSpec.Step × Nat)) := some (st, n, h, [(AlignmentSpec.Step.diag, n)])
        if cfg.band && h > 8 then
          let G := pgs[v % nc]!
          let ws := st - min st cfg.w
          let W := winL G ws (st + n + cfg.w)
          let Rx := if v < nc then R else Rr
          if cfg.ge != 0 && !gapHint Rx W ((st - ws : Nat) : Int) cfg.w cfg.ge then return r.bind fun (st, len, pen, runs) => chkAln pgs R Rr v st len pen runs
          if let some (cs, len, pen, runs) := bandDP Rx W ((st - ws : Nat) : Int) cfg.w (min h cfg.bl) then
            r := some (ws + cs, len, pen, runs)
        return r.bind fun (st, len, pen, runs) => chkAln pgs R Rr v st len pen runs
      -- an exact mate (RT's unique best) is kept when `kx`
      let x1 := if keep m1 then some m1 else (one a s1.Rr v1 st1 h1).map fun h => m1.withC h.1 7 h.2
      let x2 := if keep m2 then some m2 else (one b s2.Rr v2 st2 h2).map fun h => m2.withC h.1 7 h.2
      match x1, x2 with
      | some x, some y => opts := opts.push (x, y)
      | _, _ => pure ()
  -- 3. each mate near its partner's placement (from every option so far)
  if cfg.near then
    let near := fun (R Rr : ByteArray) (s : PrepM MzP) (x : Placement) (lim : Nat) =>
      let n := R.size
      let G := pgs[x.1.chr]!
      -- x forward: the mate reverse, inside [x.start, x.start + hi); x reverse: forward, inside [x.end − hi, x.end)
      let (v, ws, we) := if x.2 == Strand.rev then (x.1.chr, x.1.start + x.1.len - min (x.1.start + x.1.len) hi, x.1.start + x.1.len)
        else (nc + x.1.chr, x.1.start, x.1.start + hi)
      let X := if v < nc then R else Rr
      if cfg.nk ≤ 1 then
        let sv := if cfg.sv then seedVote pk offs x.1.chr ws we X (if v < nc then s.ps else s.pr) else none
        (nearY X G ws we cfg.w lim cfg.bl cfg.ge sv cfg.vf).bind fun (st, len, pen, runs) => chkAln pgs R Rr v st len pen runs
      else Id.run do
        let svs := if cfg.sv then seedVoteK pk offs x.1.chr ws we X (if v < nc then s.ps else s.pr) cfg.nk (2 * cfg.w) else #[]
        if svs.isEmpty then
          return (nearY X G ws we cfg.w lim cfg.bl cfg.ge none cfg.vf).bind fun (st, len, pen, runs) => chkAln pgs R Rr v st len pen runs
        let mut best : Option ((Placement × Int) × List (AlignmentSpec.Step × Nat)) := none
        let mut lim := lim
        for sv in svs do
          if let some (st, len, pen, runs) := nearY X G ws we cfg.w lim cfg.bl cfg.ge (some sv) cfg.vf then
            if let some h := chkAln pgs R Rr v st len pen runs then
              best := some h
              lim := pen
              if pen == 0 then break
        return best
    for (x1, x2) in opts do
      if prop (x1, x2) then continue
      if let some (p, _) := x1.pl then
        if !keep x2 then
          if let some y := near b s2.Rr s2 p (if ok x2 then x2.pH + cfg.dl + 1 else INF) then
            opts := opts.push (x1, x2.withC y.1 6 y.2)
      if let some (p, _) := x2.pl then
        if !keep x1 then
          if let some y := near a s1.Rr s1 p (if ok x1 then x1.pH + cfg.dl + 1 else INF) then
            opts := opts.push (x1.withC y.1 6 y.2, x2)
  -- the smallest summed ceiling; a proper pair within `dl` of it preferred
  let sum := fun (o : MateX × MateX) => if ok o.1 && ok o.2 then o.1.pH + o.2.pH else INF
  let bs := opts.foldl (fun b o => min b (sum o)) INF
  let mut pick := opts[0]!
  let mut pv := sum pick
  let mut pp := prop pick && pv ≤ bs + cfg.dl
  for o in opts do
    let s := sum o
    let p := prop o && s ≤ bs + cfg.dl
    if (p && !pp) || (p == pp && s < pv) then
      pick := o
      pv := s
      pp := p
  return pick


/-- The sum of the `k` smallest buckets of seeds `0 … n-1` of `pp`. -/
def smallK (pk : PkMz) (pp : Array MzP) (n k : Nat) : Nat :=
  (((List.range n).map fun j => LookG.size pk pp[j]!).mergeSort (· ≤ ·)).take k |>.foldl (· + ·) 0

/-- `smallK`'s list of the `k` smallest, seeds `n-1` down to 0, nothing sorted or built per seed. -/
def smallKGo (pk : PkMz) (pp : Array MzP) (k : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | j + 1, acc => smallKGo pk pp k j (kStep k (LookG.size pk pp[j]!) acc)

def smallKF (pk : PkMz) (pp : Array MzP) (n k : Nat) : Nat := (smallKGo pk pp k n []).foldl (· + ·) 0

theorem smallKGo_eq (pk : PkMz) (pp : Array MzP) (k : Nat) : ∀ (n : Nat) (acc : List Nat),
    (List.range n).foldr (fun j acc => kStep k (LookG.size pk pp[j]!) acc) acc = smallKGo pk pp k n acc
  | 0, _ => rfl
  | n + 1, acc => by
    rw [List.range_succ, List.foldr_append, smallKGo_eq pk pp k n]
    rfl

/-- Compiled code runs `smallKF`. -/
@[csimp] theorem smallK_eq : @smallK = @smallKF := by
  funext pk pp n k
  unfold smallK smallKF
  rw [isortN_eq, take_isortN, List.foldr_map, smallKGo_eq]

/-- The router settings `alignPairs` runs with: the bench's mode-RTX defaults (budget gate at 60000, no
pair guarantee, the rarest-seed ceiling (bucket ≤ 500, ≤ 16 diagonals), the exact pair search on tier 2
pairs with budget 1500 (c ≤ 16)) except the tier 2 heuristic, which is off (bench: WG_XH=0). While answers
are bounds only (M1) the heuristic's ceilings never reach the output, and it costs over half the mapping
time on easy reads (chr21 mason 200k, 4 cores: 12.4 s → 5.2 s). Turn it back on for M2 (`heur` below). -/
def rtxCfg (rcfg : RouteCfg) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (lo hi usl : Nat) : TierCfg :=
  let hcfg : HCfg :=
    { w := 8, r := 2, ck := 2000, np := 8, dl := 16, seeds := true, near := true, band := true
      sv := true, seedAll := true, bl := 1000000, ge := 12, kx := true, vf := true, nk := 1 }
  -- the sum of the `k` rarest seed buckets over both strands
  let rare (k : Nat) (R : ByteArray) (s : PrepM MzP) : Nat :=
    smallK pk s.ps (R.size / 25) k + smallK pk s.pr (R.size / 25) k
  let candOf (m : MateX) : Option Cand :=
    if m.pR ≥ 5 && m.pR < 1000000 then m.pl.map fun h => { pl := h, runs := m.runs, src := m.pR } else none
  { rcfg := rcfg
    lo := lo
    hi := hi
    usl := usl
    pg := none
    gate := fun _ _ _ _ c1 c2 => 60000 < c1 || 60000 < c2
    pref := fun G0 a b s1 s2 => decide (rare (sbound G0 + 2) b s2 < rare (sbound G0 + 2) a s1)
    ceil := fun R s => ceilX pk offs pgs R s 500 16
    xe := fun t a b =>
      let c := t.m1.pH + t.m2.pH
      if 16 < c then none else
      let ca := rare (sbound c + 1) a (prepMate pk a)
      let cb := rare (sbound c + 1) b (prepMate pk b)
      if 1500 < ca + cb then none else some (decide (cb < ca)) }

end TierHeur
