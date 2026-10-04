/-!
# Fast mapper: the executable code (definitions only)

Follows `bench/Proto.lean` (branch `speed/proto-tune`) closely; the proofs are
in the other `MapperFast*.lean` files and `codecs/FastMapper.lean`.
Scoring (0, −4, −6, −2), `T = −12`, so the penalty cap is 12.  Reads of
`100 .. 103` letters; 4 seeds of `q = 25`.

* Hashed 25-mer index per chromosome: CSR over `2^24` buckets, entries
  (position, key) as little-endian `UInt32` pairs in `ByteArray`s.  `mix` is a bijection on 50-bit values,
  so (bucket, key) determines the word.  `checkIdx` certifies an index in one
  rolling pass (every ACGT 25-mer is the next entry of its bucket, and every
  bucket is used up), plus the odd-letter lists; the builder is not trusted.
* Anchors: packed `A·16 + mask`, `A = p + BIAS − j·q` (diagonal biased by
  `BIAS`), mask = the looked-up seeds that match exactly on that diagonal.
* Seeds are looked up lazily, smallest bucket first (`lazyLoop`); the search
  stops once the best penalty is below `4·lookups`.  A same-length window
  (penalty `4·mismatches`, count capped by the current best) is scored when its
  anchor first appears; after 3 lookups and while the best is `≥ 8`, the 12
  one-gap windows per anchor (penalty from the first/last two mismatches,
  `gappedPen2`), pruned by the support of their two diagonals.
-/

namespace MapSpec.Fast

def q : Nat := 25
def BIAS : Nat := 128
def cap : Nat := 12

/-! ## Letters and word codes -/

/-- A C G T ↦ 0 1 2 3, any other byte ↦ 4 (a table: no branches on letters). -/
@[irreducible] def codeTab : ByteArray := ⟨#[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 4, 1, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]⟩

/-- A C G T ↦ 0 1 2 3 (anything else 0). -/
@[inline] def c2 (b : UInt8) : UInt64 := (codeTab.get! b.toNat).toUInt64 &&& 3

/-- `2^j` for a seed number `j < 4` (a switch, not `Nat` shifting). -/
@[inline] def pow2 : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 8

@[inline] def acgt (b : UInt8) : Bool := codeTab.get! b.toNat < 4

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
@[inline] def keyOf (y : UInt64) : Nat := (y &&& 0x3FFFFFF).toNat

/-- Hash of the 25-letter word at `p`. -/
@[inline] def hashAt (B : ByteArray) (p : Nat) : UInt64 := mix (wcode B p (p + q) 0)

/-! ## Index -/

/-- Little-endian `UInt32` number `i` of a byte array. -/
@[inline] def u32 (B : ByteArray) (i : Nat) : Nat :=
  let j := 4 * i
  ((B.get! j).toUInt32 ||| ((B.get! (j + 1)).toUInt32 <<< 8) |||
    ((B.get! (j + 2)).toUInt32 <<< 16) ||| ((B.get! (j + 3)).toUInt32 <<< 24)).toNat

/-- Number of `UInt32`s in `B`. -/
@[inline] def len32 (B : ByteArray) : Nat := B.size / 4

@[inline] def setU32 (B : ByteArray) (i v : Nat) : ByteArray :=
  let j := 4 * i
  let v := v.toUInt32
  ((((B.set! j v.toUInt8).set! (j + 1) (v >>> 8).toUInt8).set! (j + 2) (v >>> 16).toUInt8).set!
    (j + 3) (v >>> 24).toUInt8)

/-- Little-endian bytes of the `UInt32`s. -/
def pack32 (a : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * a.size)
  for x in a do
    b := (((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push (x >>> 24).toUInt8
  return b

/-- `offs`: `2^24 + 1` bucket offsets (LE `UInt32`s); bucket `b` is entries
`offs[b] ..< offs[b+1]`.  `ent`: entry `t` is position `ent[2t]`, key `ent[2t+1]`. -/
structure HIdx where
  offs : ByteArray
  ent : ByteArray
  /-- `odd[v]`: the places of byte `v` (not A, C, G, T), increasing (LE `UInt32`s;
  flat, so sharing the index with tasks walks no boxed elements) -/
  odd : Array ByteArray
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
  let mut ents : Array UInt32 := Array.replicate (2 * cnt[NB]!.toNat) 0
  x := 0; good := 0
  for p in [0:g.size] do
    let v := g.get! p
    if acgt v then x := (x * 4 + c2 v) &&& wmask; good := good + 1 else good := 0
    if good ≥ q then
      let y := mix x
      let b := bucketOf y
      let i := fill[b]!.toNat
      ents := (ents.set! (2 * i) (p + 1 - q).toUInt32).set! (2 * i + 1) (keyOf y).toUInt32
      fill := fill.set! b (i + 1).toUInt32
  let offs := pack32 cnt
  let ent := pack32 ents
  let mut odd : Array (Array UInt32) := Array.replicate 256 #[]
  for p in [0:g.size] do
    let v := g.get! p
    if !acgt v then odd := odd.modify v.toNat (·.push p.toUInt32)
  return { offs, ent, odd := odd.map pack32 }

/-! ### Checker -/

/-- One pass over the chromosome from `e` (`k` letters).  `x` is the code of the
last `r ≤ 25` letters, all ACGT (`r` = the ACGT run ending before `e`, capped).
Each ACGT word must be the next entry `fill[b]` of its bucket `b`, with its
place and key; `none` if one is not. -/
def scanIdx (ix : HIdx) (G : ByteArray) : (k e : Nat) → (x : UInt64) → (r : Nat) → Array Nat →
    Option (Array Nat)
  | 0, _, _, _, fill => some fill
  | k + 1, e, x, r, fill =>
    let v := G.get! e
    if acgt v then
      let x := (x * 4 + c2 v) &&& 0x3FFFFFFFFFFFF
      let r := min (r + 1) q
      if r = q then
        let y := mix x
        let b := bucketOf y
        let t := fill[b]!
        if u32 ix.offs b ≤ t && t < u32 ix.offs (b + 1) && u32 ix.ent (2 * t) == e + 1 - q &&
            u32 ix.ent (2 * t + 1) == keyOf y then
          scanIdx ix G k (e + 1) x r (fill.set! b (t + 1))
        else none
      else scanIdx ix G k (e + 1) x r fill
    else scanIdx ix G k (e + 1) 0 0 fill

/-- After the scan every bucket was used up exactly. -/
def fillOk (ix : HIdx) (fill : Array Nat) : (k b : Nat) → Bool
  | 0, _ => true
  | k + 1, b => fill[b]! == u32 ix.offs (b + 1) && fillOk ix fill k (b + 1)

/-- Every place `p, p+1, …` (`k` of them) holding a byte `v` other than ACGT is
entry `cur[v]` of `odd[v]` (`cur` is only a hint). -/
def checkOdd (ix : HIdx) (G : ByteArray) (cur : Array Nat) : (k p : Nat) → Bool
  | 0, _ => true
  | k + 1, p =>
    let v := (G.get! p).toNat
    if acgt (G.get! p) then checkOdd ix G cur k (p + 1)
    else decide (cur[v]! < len32 ix.odd[v]!) && u32 ix.odd[v]! cur[v]! == p && checkOdd ix G (cur.set! v (cur[v]! + 1)) k (p + 1)

def increasing (a : ByteArray) : (k i : Nat) → Bool
  | 0, _ => true
  | k + 1, i => decide (u32 a i < u32 a (i + 1)) && increasing a k (i + 1)

/-- The runtime checker. -/
def checkIdx (ix : HIdx) (G : ByteArray) : Bool :=
  (match scanIdx ix G G.size 0 0 0 ((Array.range NB).map (u32 ix.offs)) with
   | some fill => fillOk ix fill NB 0
   | none => false) &&
    checkOdd ix G (Array.replicate 256 0) G.size 0 &&
    (List.range 256).all fun v => increasing ix.odd[v]! (len32 ix.odd[v]! - 1) 0

/-! ## Anchors -/

/-- Packed anchors `(ent[2t] + base)·16 + bit` of the entries `t ∈ [t, hi)` with this key. -/
def scanBucket (ent : ByteArray) (key : Nat) (base bit hi : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < hi then
    scanBucket ent key base bit hi (t + 1)
      (if u32 ent (2 * t + 1) == key then acc.push ((u32 ent (2 * t) + base) * 16 + bit) else acc)
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
def scanOdd (G R : ByteArray) (ps : ByteArray) (o s base bit : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < len32 ps then
    let p := u32 ps t - o
    scanOdd G R ps o s base bit (t + 1)
      (if o ≤ u32 ps t && p + q ≤ G.size && eqRun G R p s q then acc.push ((p + base) * 16 + bit) else acc)
  else acc
termination_by len32 ps - t

/-- One pass over `B[i, stop)`: base-4 code appended to `x`, and `f` counts the
letters other than ACGT; the result is `code + f·2^56`. -/
def seedCode (B : ByteArray) (i stop : Nat) (x f : UInt64) : UInt64 :=
  if i < stop then
    let c := (codeTab.get! (B.get! i).toNat).toUInt64
    seedCode B (i + 1) stop (x * 4 + (c &&& 3)) (f + (c >>> 2))
  else x + (f <<< 56)
termination_by stop - i

/-- Hash of seed `j` when all its letters are ACGT. -/
def seedHash (R : ByteArray) (j : Nat) : Option UInt64 :=
  let v := seedCode R (j * q) (j * q + q) 0 0
  if v >>> 56 == 0 then some (mix v) else none

/-- Seed `j` (letters `R[j·q, j·q+q)`), `h = seedHash R j`: packed anchors
`(p + BIAS − j·q)·16 + 2^j` of the places `p` where it occurs, increasing. -/
def lookupH (ix : HIdx) (G R : ByteArray) (j : Nat) (h : Option UInt64) : Array Nat :=
  let s := j * q
  match h with
  | some y =>
    let b := bucketOf y
    scanBucket ix.ent (keyOf y) (BIAS - s) (pow2 j) (u32 ix.offs (b + 1)) (u32 ix.offs b) #[]
  | none =>
    let o := firstOdd R s (s + q)
    scanOdd G R ix.odd[(R.get! o).toNat]! (o - s) s (BIAS - s) (pow2 j) 0 #[]

def lookupSeed (ix : HIdx) (G R : ByteArray) (j : Nat) : Array Nat := lookupH ix G R j (seedHash R j)

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

/-- Position of the `k`-th mismatch (`k ≥ 1`) of `r[i, stop)` against `g[st + i ..]`, or `stop`. -/
def fwdMis (r g : ByteArray) (st stop : Nat) (i k : Nat) : Nat :=
  if i < stop then
    if r.get! i != g.get! (st + i) then (if k ≤ 1 then i else fwdMis r g st stop (i + 1) (k - 1))
    else fwdMis r g st stop (i + 1) k
  else stop
termination_by stop - i

/-- One past the `k`-th mismatch from the right (`k ≥ 1`) of `r[lo, e)` against the end
diagonal (read letter `x` ↔ `g[st + len + x - n]`), or `lo` when there are fewer. -/
def bwdMis (r g : ByteArray) (st len lo : Nat) (e k : Nat) : Nat :=
  if lo < e then
    if r.get! (e - 1) != g.get! (st + len + (e - 1) - r.size) then
      (if k ≤ 1 then e else bwdMis r g st len lo (e - 1) (k - 1))
    else bwdMis r g st len lo (e - 1) k
  else lo
termination_by e - lo

/-- Penalty of window `(st, len)`, `len ≠ n`, `|len − n| ≤ 3`, if `≤ lim ≤ 12`; else `lim + 1`.
At most one mismatch fits, so only the first two mismatches of the prefix diagonal
(`F1`, `F2`) and the last two of the suffix diagonal (`E1`, `E2`) matter. -/
def gappedPen2 (r g : ByteArray) (st len lim : Nat) : Nat :=
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
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else lim + 1

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

@[inline] def need (b : Best) : Nat := if min b.pen cap < 10 then 3 else 2

/-- Add window `(st, len)` scored by `gappedPen` with the current cap. -/
@[inline] def addGap (R G : ByteArray) (c st len : Nat) (b : Best) : Best :=
  b.add c st len (gappedPen2 R G st len (min b.pen cap))

/-- Window `(st, len)` (one gap; its two diagonals carry `s` clean seeds) when
`ok` and it fits and its support can reach the current best. -/
@[inline] def gapW (R G : ByteArray) (c st len s : Nat) (ok : Bool) (b : Best) : Best :=
  if need b ≤ s && ok && st + len ≤ G.size then addGap R G c st len b else b

/-! ## Lazy seed lookups (the prototype's `mapCore`)

Seeds are looked up one at a time, smallest bucket first.  After `k` lookups a
hit none of whose clean seeds was looked up costs `≥ 4k`, so the search stops
once the best is below `4k`.  A same-length window is scored when its anchor
first appears; one-gap windows only after 3 lookups and when the best is `≥ 8`. -/

/-- Anchors of `y` whose diagonal is not in `x` (both increasing). -/
def newOnly (x y : Array Nat) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if h : j < y.size then
    if h' : i < x.size then
      if x[i] / 16 < y[j] / 16 then newOnly x y (i + 1) j acc
      else if x[i] / 16 == y[j] / 16 then newOnly x y (i + 1) (j + 1) acc
      else newOnly x y i (j + 1) (acc.push y[j])
    else newOnly x y i (j + 1) (acc.push y[j])
  else acc
termination_by (x.size - i) + (y.size - j)

/-- Same-length window of a new anchor. -/
@[inline] def sameStep2 (R G : ByteArray) (c : Nat) (b : Best) (e : Nat) : Best :=
  let A := e / 16
  if BIAS ≤ A && A - BIAS + R.size ≤ G.size && !(b.pen == 0 && b.amb) then
    let m := hamSeeds R G (A - BIAS) (e % 16) (min 3 (b.pen / 4))
    if 4 * m ≤ cap then b.add c (A - BIAS) R.size (4 * m) else b
  else b

/-- Is seed `j` (not looked up) clean on diagonal `A`? -/
@[inline] def seedOn (G R : ByteArray) (looked j A : Nat) : Nat :=
  if (looked >>> j) % 2 == 0 && BIAS ≤ A + j * q && A + j * q - BIAS + q ≤ G.size &&
      eqRun G R (A + j * q - BIAS) (j * q) q then 1 else 0

/-- Number of seeds clean on diagonal `A`: looked-up ones from the anchors near
index `i`, the others checked in the genome. -/
@[inline] def supAt (G R : ByteArray) (as : Array Nat) (looked i A : Nat) : Nat :=
  supNear as i A + seedOn G R looked 0 A + seedOn G R looked 1 A + seedOn G R looked 2 A +
    seedOn G R looked 3 A

@[inline] def gapL2 (R G : ByteArray) (c : Nat) (as : Array Nat) (looked i A cs L : Nat) (b : Best) : Best :=
  let n := R.size
  let sm := supAt G R as looked i (A - L)
  let sp := supAt G R as looked i (A + L)
  gapW R G c (A + L - BIAS) (n - L) (cs + sp) (BIAS ≤ A + L) <|
  gapW R G c (A - L - BIAS) (n + L) (cs + sm) (BIAS + L ≤ A) <|
  gapW R G c (A - BIAS) (n - L) (cs + sm) (BIAS ≤ A) <|
  gapW R G c (A - BIAS) (n + L) (cs + sp) (BIAS ≤ A) b

def gapAll2 (R G : ByteArray) (c : Nat) (as : Array Nat) (looked : Nat) : (k i : Nat) → Best → Best
  | 0, _, b => b
  | k + 1, i, b =>
    let A := as[i]! / 16
    let cs := supAt G R as looked i A
    gapAll2 R G c as looked k (i + 1)
      (gapL2 R G c as looked i A cs 3 (gapL2 R G c as looked i A cs 2 (gapL2 R G c as looked i A cs 1 b)))

/-- Entries in the seed's bucket (0 for a seed with a letter other than ACGT). -/
@[inline] def sizeH (ix : HIdx) (h : Option UInt64) : Nat :=
  match h with
  | some y => u32 ix.offs (bucketOf y + 1) - u32 ix.offs (bucketOf y)
  | none => 0

/-- A seed lookup.  `prep ix h` is computed once per seed (`h = seedHash R j`);
`look ix G R j (prep ix (seedHash R j))` must be seed `j`'s packed anchors
(`LookOk`); `size ix p` only orders the seeds (smallest first). -/
class Look (L P : Type) where
  prep : L → Option UInt64 → P
  size : L → P → Nat
  look : L → ByteArray → ByteArray → Nat → P → Array Nat

/-- The hashed index as a lookup. -/
def hLook : Look HIdx (Option UInt64) := ⟨fun _ h => h, sizeH, lookupH⟩

/-- Look up the seeds of `ord` in turn (`k` done, anchors `as`, `looked` mask);
`ps` holds the prepared seeds. -/
@[specialize] def lazyLoop {L P : Type} [Inhabited P] (R G : ByteArray) (c : Nat) (lk : Look L P) (ix : L)
    (ps : Array P) : (ord : List Nat) → (k : Nat) → Array Nat → Nat → Best → Best
  | [], _, _, _, b => b
  | j :: rest, k, as, looked, b =>
    let lj := lk.look ix G R j ps[j]!
    let fresh := newOnly as lj 0 0 #[]
    let as := merge as lj 0 0 #[]
    let looked := looked + pow2 j
    let b := fresh.foldl (sameStep2 R G c) b
    let b := if 2 ≤ k && 8 ≤ b.pen then gapAll2 R G c as looked as.size 0 b else b
    if b.pen < 4 * (k + 1) then b else lazyLoop R G c lk ix ps rest (k + 1) as looked b

/-- One step of `lazyLoop` (seed `j` after `k` lookups): the new anchors and best
(the new mask is `looked + pow2 j`). -/
@[inline] def lzStep {L P : Type} [Inhabited P] (R G : ByteArray) (c : Nat) (lk : Look L P) (ix : L)
    (ps : Array P) (j k : Nat) (as : Array Nat) (looked : Nat) (b : Best) : Array Nat × Best :=
  let lj := lk.look ix G R j ps[j]!
  let fresh := newOnly as lj 0 0 #[]
  let as := merge as lj 0 0 #[]
  let looked := looked + pow2 j
  let b := fresh.foldl (sameStep2 R G c) b
  (as, if 2 ≤ k && 8 ≤ b.pen then gapAll2 R G c as looked as.size 0 b else b)

def seedHashes (R : ByteArray) : Array (Option UInt64) :=
  #[seedHash R 0, seedHash R 1, seedHash R 2, seedHash R 3]

@[inline] def prepAll {L P : Type} (lk : Look L P) (ix : L) (hs : Array (Option UInt64)) : Array P :=
  #[lk.prep ix hs[0]!, lk.prep ix hs[1]!, lk.prep ix hs[2]!, lk.prep ix hs[3]!]

/-- Insert `x` before the first element with a larger key (`ks[·]`). -/
def insKey (ks : Array Nat) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if ks[x]! ≤ ks[y]! then x :: y :: ys else y :: insKey ks x ys

/-- Seeds, smallest bucket first (insertion sort of `[0, 1, 2, 3]`). -/
@[inline] def seedOrder {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (ps : Array P) : List Nat :=
  let ks := #[lk.size ix ps[0]!, lk.size ix ps[1]!, lk.size ix ps[2]!, lk.size ix ps[3]!]
  insKey ks 3 (insKey ks 2 (insKey ks 1 [0]))

/-- One chromosome; `hs` = `seedHashes R` (computed once per read). -/
@[inline] def mapChrom2 {L P : Type} [Inhabited P] (lk : Look L P) (R G : ByteArray) (c : Nat) (ix : L)
    (hs : Array (Option UInt64)) (b : Best) : Best :=
  let ps := prepAll lk ix hs
  lazyLoop R G c lk ix ps (seedOrder lk ix ps) 0 #[] 0 b

/-- Reads the fast path handles: `100 .. 103` letters. -/
def fastOk (R : ByteArray) : Bool := R.size / 4 == q

@[specialize] def mapChroms {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) : Best :=
  let hs := seedHashes R
  (List.range gbs.size).foldl (fun b c => mapChrom2 lk R gbs[c]! c idxs[c]! hs b) {}

def result (b : Best) : Option (Nat × Nat × Nat × Nat) :=
  if b.pen ≤ cap && !b.amb then some (b.chr, b.st, b.len, b.pen) else none

end MapSpec.Fast
