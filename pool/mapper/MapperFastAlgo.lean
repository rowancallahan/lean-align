/-!
# Fast mapper: the executable code (definitions only)

Follows `bench/Proto.lean` (branch `speed/proto-tune`) closely; the proofs are
in the other `MapperFast*.lean` files and `codecs/FastMapper.lean`.
Scoring (0, −4, −6, −2), `T = −12`, so the penalty cap is 12.  Reads of
`100 .. 103` letters; 4 seeds of `q = 25`.

* Hashed 25-mer index per chromosome: CSR over `2^24` buckets, entries
  (position, key) as `UInt32` pairs.  `mix` is a bijection on 50-bit values,
  so (bucket, key) determines the word.  `checkIdx` certifies an index in one
  rolling pass (every ACGT 25-mer is the next entry of its bucket, and every
  bucket is used up), plus the odd-letter lists; the builder is not trusted.
* Anchors: packed `A·16 + mask`, `A = p + BIAS − j·q` (diagonal biased by
  `BIAS`), mask = the seeds that match exactly on that diagonal.
* Same-length windows (penalty `4·mismatches`), best support first, with the
  mismatch count capped by the current best; then, only when the best is
  `≥ 8`, the 12 one-gap windows per anchor with support pruning.
-/

namespace MapSpec.Fast

def q : Nat := 25
def BIAS : Nat := 128
def cap : Nat := 12

/-! ## Letters and word codes -/

/-- A C G T ↦ 0 1 2 3 (anything else 0). -/
@[inline] def c2 (b : UInt8) : UInt64 :=
  if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 0

@[inline] def acgt (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

/-- Base-4 code of `B[i, stop)` appended to `x`. -/
def wcode (B : ByteArray) (i stop : Nat) (x : UInt64) : UInt64 :=
  if i < stop then wcode B (i + 1) stop (x * 4 + c2 (B.get! i)) else x
termination_by stop - i

/-- Every byte of `B[i, stop)` is A, C, G or T. -/
def allACGT (B : ByteArray) (i stop : Nat) : Bool :=
  if i < stop then acgt (B.get! i) && allACGT B (i + 1) stop else true
termination_by stop - i

def MIXC : UInt64 := 0x9E3779B97F4A7C15

/-- Odd multiplier mod `2^50`: a bijection on 50-bit values. -/
@[inline] def mix (x : UInt64) : UInt64 := (x * MIXC) &&& 0x3FFFFFFFFFFFF

/-- Top 24 of the 50 bits. -/
@[inline] def bucketOf (y : UInt64) : Nat := (y >>> 26).toNat

/-- Low 26 of the 50 bits. -/
@[inline] def keyOf (y : UInt64) : UInt32 := (y &&& 0x3FFFFFF).toUInt32

/-- Hash of the 25-letter word at `p`. -/
@[inline] def hashAt (B : ByteArray) (p : Nat) : UInt64 := mix (wcode B p (p + q) 0)

/-! ## Index -/

/-- `offs`: `2^24 + 1` bucket offsets; bucket `b` is entries `offs[b] ..< offs[b+1]`.
`ent`: entry `t` is position `ent[2t]`, key `ent[2t+1]`. -/
structure HIdx where
  offs : Array UInt32
  ent : Array UInt32
  /-- `odd[v]`: the places of byte `v` (not A, C, G, T), increasing -/
  odd : Array (Array Nat)
deriving Inhabited

def NB : Nat := 1 <<< 24

/-- Builder (fast, not trusted): two passes over the chromosome with a rolling
code (`good` = length of the ACGT run ending here). -/
def buildIdx (g : ByteArray) : HIdx := Id.run do
  let wmask : UInt64 := 0x3FFFFFFFFFFFF
  let mut cnt : Array UInt32 := Array.replicate (NB + 1) 0
  let mut x : UInt64 := 0
  let mut good := 0
  for p in [0:g.size] do
    let v := g.get! p
    if acgt v then x := (x * 4 + c2 v) &&& wmask; good := good + 1 else good := 0
    if good ≥ q then
      let b := bucketOf (mix x)
      cnt := cnt.modify (b + 1) (· + 1)
  for b in [0:NB] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let mut fill := cnt
  let mut ent : Array UInt32 := Array.replicate (2 * cnt[NB]!.toNat) 0
  x := 0; good := 0
  for p in [0:g.size] do
    let v := g.get! p
    if acgt v then x := (x * 4 + c2 v) &&& wmask; good := good + 1 else good := 0
    if good ≥ q then
      let y := mix x
      let b := bucketOf y
      let i := fill[b]!.toNat
      ent := (ent.set! (2 * i) (p + 1 - q).toUInt32).set! (2 * i + 1) (keyOf y)
      fill := fill.set! b (i + 1).toUInt32
  let mut odd : Array (Array Nat) := Array.replicate 256 #[]
  for p in [0:g.size] do
    let v := g.get! p
    if !acgt v then odd := odd.modify v.toNat (·.push p)
  return { offs := cnt, ent, odd }

/-! ### Checker -/

/-- One pass over the chromosome from `e` (`k` letters).  `x` is the code of the
last `r ≤ 25` letters, all ACGT (`r` = the ACGT run ending before `e`, capped).
Each ACGT word must be the next entry `fill[b]` of its bucket `b`, with its
place and key; `none` if one is not. -/
def scanIdx (ix : HIdx) (G : ByteArray) : (k e : Nat) → (x : UInt64) → (r : Nat) → Array UInt32 →
    Option (Array UInt32)
  | 0, _, _, _, fill => some fill
  | k + 1, e, x, r, fill =>
    let v := G.get! e
    if acgt v then
      let x := (x * 4 + c2 v) &&& 0x3FFFFFFFFFFFF
      let r := min (r + 1) q
      if r = q then
        let y := mix x
        let b := bucketOf y
        let t := fill[b]!.toNat
        if ix.offs[b]!.toNat ≤ t && t < ix.offs[b + 1]!.toNat && ix.ent[2 * t]!.toNat == e + 1 - q &&
            ix.ent[2 * t + 1]! == keyOf y then
          scanIdx ix G k (e + 1) x r (fill.set! b (t + 1).toUInt32)
        else none
      else scanIdx ix G k (e + 1) x r fill
    else scanIdx ix G k (e + 1) 0 0 fill

/-- After the scan every bucket was used up exactly. -/
def fillOk (ix : HIdx) (fill : Array UInt32) : (k b : Nat) → Bool
  | 0, _ => true
  | k + 1, b => fill[b]! == ix.offs[b + 1]! && fillOk ix fill k (b + 1)

/-- Every place `p, p+1, …` (`k` of them) holding a byte `v` other than ACGT is
entry `cur[v]` of `odd[v]` (`cur` is only a hint). -/
def checkOdd (ix : HIdx) (G : ByteArray) (cur : Array Nat) : (k p : Nat) → Bool
  | 0, _ => true
  | k + 1, p =>
    let v := (G.get! p).toNat
    if acgt (G.get! p) then checkOdd ix G cur k (p + 1)
    else decide (cur[v]! < ix.odd[v]!.size) && ix.odd[v]![cur[v]!]! == p && checkOdd ix G (cur.set! v (cur[v]! + 1)) k (p + 1)

def increasing (a : Array Nat) : (k i : Nat) → Bool
  | 0, _ => true
  | k + 1, i => decide (a[i]! < a[i + 1]!) && increasing a k (i + 1)

/-- The runtime checker. -/
def checkIdx (ix : HIdx) (G : ByteArray) : Bool :=
  (match scanIdx ix G G.size 0 0 0 ix.offs with
   | some fill => fillOk ix fill NB 0
   | none => false) &&
    checkOdd ix G (Array.replicate 256 0) G.size 0 &&
    (List.range 256).all fun v => increasing ix.odd[v]! (ix.odd[v]!.size - 1) 0

/-! ## Anchors -/

/-- Packed anchors `(ent[2t] + base)·16 + bit` of the entries `t ∈ [t, hi)` with this key. -/
def scanBucket (ent : Array UInt32) (key : UInt32) (base bit hi : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < hi then
    scanBucket ent key base bit hi (t + 1)
      (if ent[2 * t + 1]! == key then acc.push ((ent[2 * t]!.toNat + base) * 16 + bit) else acc)
  else acc
termination_by hi - t

/-- `a[i, i+k) = b[j, j+k)`. -/
def eqRun (a b : ByteArray) (i j : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => a.get! i == b.get! j && eqRun a b (i + 1) (j + 1) k

/-- First `i ∈ [i, stop)` with `B[i]` not ACGT (`stop` if none). -/
def firstOdd (B : ByteArray) (i stop : Nat) : Nat :=
  if i < stop then (if acgt (B.get! i) then firstOdd B (i + 1) stop else i) else stop
termination_by stop - i

/-- Packed anchors of the places `pos - o` (`pos ∈ ps[t ..]`) where the whole seed
`R[s, s+q)` occurs. -/
def scanOdd (G R : ByteArray) (ps : Array Nat) (o s base bit : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < ps.size then
    let p := ps[t]! - o
    scanOdd G R ps o s base bit (t + 1)
      (if o ≤ ps[t]! && p + q ≤ G.size && eqRun G R p s q then acc.push ((p + base) * 16 + bit) else acc)
  else acc
termination_by ps.size - t

/-- Seed `j` (letters `R[j·q, j·q+q)`): packed anchors `(p + BIAS − j·q)·16 + 2^j`
of the places `p` where it occurs, increasing. -/
def lookupSeed (ix : HIdx) (G R : ByteArray) (j : Nat) : Array Nat :=
  let s := j * q
  let o := firstOdd R s (s + q)
  if o == s + q then
    let y := hashAt R s
    let b := bucketOf y
    scanBucket ix.ent (keyOf y) (BIAS - s) (2 ^ j) ix.offs[b + 1]!.toNat ix.offs[b]!.toNat #[]
  else
    scanOdd G R ix.odd[(R.get! o).toNat]! (o - s) s (BIAS - s) (2 ^ j) 0 #[]

/-- Merge two increasing packed anchor lists, adding the masks of equal anchors. -/
def merge (x y : Array Nat) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if h : i < x.size then
    if h' : j < y.size then
      let a := x[i]
      let b := y[j]
      if a / 16 < b / 16 then merge x y (i + 1) j (acc.push a)
      else if b / 16 < a / 16 then merge x y i (j + 1) (acc.push b)
      else merge x y (i + 1) (j + 1) (acc.push (a + b % 16))
    else merge x y (i + 1) j (acc.push x[i])
  else if h' : j < y.size then merge x y i (j + 1) (acc.push y[j])
  else acc
termination_by (x.size - i) + (y.size - j)

def anchors (ix : HIdx) (G R : ByteArray) : Array Nat :=
  merge (merge (lookupSeed ix G R 0) (lookupSeed ix G R 1) 0 0 #[])
    (merge (lookupSeed ix G R 2) (lookupSeed ix G R 3) 0 0 #[]) 0 0 #[]

@[inline] def pop4 (m : Nat) : Nat := m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2

/-- Support of anchor `A` (0 if absent), looked for among `as[i-3 .. i+3]`. -/
def supScan (as : Array Nat) (A : Nat) (k stop : Nat) : Nat :=
  if k < stop then
    if as[k]! / 16 == A then pop4 (as[k]! % 16) else supScan as A (k + 1) stop
  else 0
termination_by stop - k

@[inline] def supNear (as : Array Nat) (i A : Nat) : Nat :=
  supScan as A (i - min i 3) (min as.size (i + 4))

/-! ## Window penalties -/

/-- Mismatches of `r[i, stop)` against `g[a + i ..]` added to `m`, stopping once above `lim`. -/
def hamming (r g : ByteArray) (a lim : Nat) (i stop m : Nat) : Nat :=
  if i < stop then
    if r.get! i != g.get! (a + i) then
      if lim < m + 1 then m + 1 else hamming r g a lim (i + 1) stop (m + 1)
    else hamming r g a lim (i + 1) stop m
  else m
termination_by stop - i

/-- Continue the count over `r[i, stop)` unless already above `lim` or the seed is clean. -/
@[inline] def hamStep (r g : ByteArray) (a lim i stop : Nat) (clean : Bool) (m : Nat) : Nat :=
  if m ≤ lim && !clean then hamming r g a lim i stop m else m

/-- Mismatches of the read against `g[a ..]` (capped at `lim + 1`), skipping
the seeds in `mask` (clean there). -/
@[inline] def hamSeeds (r g : ByteArray) (a mask lim : Nat) : Nat :=
  hamStep r g a lim (3 * q) (4 * q) (mask / 8 % 2 == 1) <|
  hamStep r g a lim (2 * q) (3 * q) (mask / 4 % 2 == 1) <|
  hamStep r g a lim q (2 * q) (mask / 2 % 2 == 1) <|
  hamStep r g a lim 0 q (mask % 2 == 1) <|
  hamming r g a lim (4 * q) r.size 0

/-- Mismatches of `r[k, stop)` against `g[k + d1 - d0]`, added to `m`. -/
def misCount (r g : ByteArray) (d1 d0 : Nat) (k stop m : Nat) : Nat :=
  if k < stop then
    misCount r g d1 d0 (k + 1) stop (if r.get! k != g.get! (k + d1 - d0) then m + 1 else m)
  else m
termination_by stop - k

/-- Least `pre + suf` over the gap positions `i+1 .. stop`, stopping once `pre > mmax`. -/
def gapScan (r g : ByteArray) (st len skip mmax stop : Nat) (i pre suf best : Nat) : Nat :=
  if i < stop then
    let pre := if r.get! i != g.get! (st + i) then pre + 1 else pre
    if mmax < pre then best else
    let suf := if r.get! (i + skip) != g.get! (st + len + i + skip - r.size) then suf - 1 else suf
    gapScan r g st len skip mmax stop (i + 1) pre suf (min best (pre + suf))
  else best
termination_by stop - i

/-- Penalty of window `(st, len)`, `len ≠ n`, `|len − n| ≤ 3`, if it is `≤ lim`; else `lim + 1`. -/
def gappedPen (r g : ByteArray) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let mmax := (lim - 6 - 2 * L) / 4
  let skip := if len < n then L else 0
  let suf := misCount r g (st + len) n skip n 0
  let best := gapScan r g st len skip mmax (n - skip) 0 0 suf suf
  if mmax < best then lim + 1 else 6 + 2 * L + 4 * best

/-! ## Best window -/

structure Best where
  pen : Nat := cap + 1
  chr : Nat := 0
  st : Nat := 0
  len : Nat := 0
  amb : Bool := false

@[inline] def Best.add (b : Best) (c st len pen : Nat) : Best :=
  if pen < b.pen then { pen, chr := c, st, len, amb := false }
  else if pen == b.pen && (c != b.chr || st != b.st || len != b.len) then { b with amb := true }
  else b

/-- Same-length windows of the anchors with support `sup`. -/
@[inline] def sameStep (R G : ByteArray) (c sup : Nat) (b : Best) (e : Nat) : Best :=
  let A := e / 16
  if pop4 (e % 16) == sup && BIAS ≤ A && A - BIAS + R.size ≤ G.size then
    let m := hamSeeds R G (A - BIAS) (e % 16) (min 3 (b.pen / 4))
    if 4 * m ≤ cap then b.add c (A - BIAS) R.size (4 * m) else b
  else b

/-- Pass `k`: anchors with `4 − k` clean seeds (penalty `≥ 4k`). -/
@[inline] def samePass (R G : ByteArray) (c : Nat) (as : Array Nat) (k : Nat) (b : Best) : Best :=
  if 4 * k ≤ b.pen && !(b.pen == 0 && b.amb) then as.foldl (sameStep R G c (4 - k)) b else b

@[inline] def need (b : Best) : Nat := if min b.pen cap < 10 then 3 else 2

/-- Add window `(st, len)` scored by `gappedPen` with the current cap. -/
@[inline] def addGap (R G : ByteArray) (c st len : Nat) (b : Best) : Best :=
  b.add c st len (gappedPen R G st len (min b.pen cap))

/-- Window `(st, len)` (one gap; its two diagonals carry `s` clean seeds) when
`ok` and it fits and its support can reach the current best. -/
@[inline] def gapW (R G : ByteArray) (c st len s : Nat) (ok : Bool) (b : Best) : Best :=
  if need b ≤ s && ok && st + len ≤ G.size then addGap R G c st len b else b

/-- The four windows with a gap of length `L` next to anchor `A` (support `cs`):
`(A, n+L)` ends on `A+L`, `(A, n-L)` on `A-L` (gap after the seed);
`(A-L, n+L)` and `(A+L, n-L)` end on `A` (gap before the seed). -/
@[inline] def gapL (R G : ByteArray) (c : Nat) (as : Array Nat) (i A cs L : Nat) (b : Best) : Best :=
  let n := R.size
  let sm := supNear as i (A - L)
  let sp := supNear as i (A + L)
  gapW R G c (A + L - BIAS) (n - L) (cs + sp) (BIAS ≤ A + L) <|
  gapW R G c (A - L - BIAS) (n + L) (cs + sm) (BIAS + L ≤ A) <|
  gapW R G c (A - BIAS) (n - L) (cs + sm) (BIAS ≤ A) <|
  gapW R G c (A - BIAS) (n + L) (cs + sp) (BIAS ≤ A) b

/-- One-gap windows of anchors `i, i+1, …` (`k` of them). -/
def gapAll (R G : ByteArray) (c : Nat) (as : Array Nat) : (k i : Nat) → Best → Best
  | 0, _, b => b
  | k + 1, i, b =>
    let A := as[i]! / 16
    let cs := pop4 (as[i]! % 16)
    gapAll R G c as k (i + 1) (gapL R G c as i A cs 3 (gapL R G c as i A cs 2 (gapL R G c as i A cs 1 b)))

/-- All windows of chromosome `c` worth scoring. -/
def mapChrom (R G : ByteArray) (c : Nat) (ix : HIdx) (b : Best) : Best :=
  let as := anchors ix G R
  let b := samePass R G c as 3 (samePass R G c as 2 (samePass R G c as 1 (samePass R G c as 0 b)))
  -- gapped windows cost ≥ 8: skipped when the best so far is below that
  if 8 ≤ b.pen then gapAll R G c as as.size 0 b else b

/-- Reads the fast path handles: `100 .. 103` letters. -/
def fastOk (R : ByteArray) : Bool := R.size / 4 == q

def mapChroms (R : ByteArray) (gbs : Array ByteArray) (idxs : Array HIdx) : Best :=
  (List.range gbs.size).foldl (fun b c => mapChrom R gbs[c]! c idxs[c]! b) {}

def result (b : Best) : Option (Nat × Nat × Nat × Nat) :=
  if b.pen ≤ cap && !b.amb then some (b.chr, b.st, b.len, b.pen) else none

end MapSpec.Fast
