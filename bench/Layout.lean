/-!
Index layout bench (NOT proved, not part of the tool).

    lake exe layout <genome.fa> <reads.txt> <spec> [dump.tsv]
    spec = boxed          the `bench/Proto.lean` index (Array UInt32: 16 bytes/entry)
         | w,s,B,kb       packed ByteArray index (see `Pk`)
    env SORT=1            map reads in order of the index bucket of their first seed

The mapping code between the markers is `bench/Proto.lean` (speed/proto-tune
8e2d852) with the index lookup abstracted as `Lk`; answers must equal Proto's
(compare dumps).
-/

/-- What the mapper needs from an index: anchors of seed `j` (code `v`) of read
`r` in genome `g`, increasing, packed `(p + BIAS - j·q)·16 + 2^j`, for exactly the
starts `p` with `g[p, p+q) = seed`; and a bucket size (speed heuristic only). -/
structure Lk where
  q : Nat
  look : ByteArray → ByteArray → Nat → UInt64 → Array Nat
  size : Nat → Nat
  bucketOf : Nat → Nat

-- ─── BEGIN copied from bench/Proto.lean ───
def cap : Nat := 12

def codeTab : ByteArray := Id.run do
  let mut t := ByteArray.mk (Array.replicate 256 4)
  for (c, v) in [(65, 0), (67, 1), (71, 2), (84, 3), (78, 12)] do t := t.set! c v
  return t

/-- A C G T ↦ 0 1 2 3, N ↦ 12, anything else ↦ 4. -/
@[inline] def code (b : UInt8) : UInt64 := (codeTab.get! b.toNat).toUInt64

/-- Bijection on 50-bit values (odd multiplier mod 2^50): bucket = top 24
bits, key = low 26 bits, so (bucket, key) determines the 25-letter word. -/
def mix (x : UInt64) : UInt64 := (x * 0x9E3779B97F4A7C15) &&& 0x3FFFFFFFFFFFF
def BBITS : UInt64 := 24
def KMASK : UInt64 := 0x3FFFFFF

/-- Anchors are stored biased by `BIAS` (≥ n) so they are `Nat`s. -/
def BIAS : Nat := 128

/-- 2-bit code of r[o+i, o+stop) appended to `x`; bits 60, 61 flag a letter
other than ACGTN, an N. -/
def seedCode (r : ByteArray) (o i stop : Nat) (x f : UInt64) : UInt64 :=
  if h : i < stop then
    let c := code (r.get! (o + i))
    seedCode r o (i + 1) stop ((x <<< 2) ||| (c &&& 3)) (f ||| c)
  else x ||| ((f >>> 2) <<< 60)
termination_by stop - i

/-- a[i, stop) = b[j, j + stop - i). -/
def eqRun (a b : ByteArray) (i j stop : Nat) : Bool :=
  if h : i < stop then a.get! i == b.get! j && eqRun a b (i + 1) (j + 1) stop else true
termination_by stop - i

/-- Index of every ACGT-only q-letter word (q = 25): CSR over 2^24 buckets,
entries (pos, key) in increasing pos.  `odd` = starts of the q-windows that
contain a letter other than ACGTN (looked up directly). -/
structure Idx where
  q : Nat
  offs : Array UInt32
  ent : Array UInt32
  odd : Array Nat
deriving Inhabited

def buildIdx (g : ByteArray) (q : Nat) : Idx := Id.run do
  assert! q == 25
  let nb := 1 <<< BBITS.toNat
  let wmask : UInt64 := (1 <<< (2 * q.toUInt64)) - 1
  let mut cnt : Array UInt32 := Array.replicate (nb + 1) 0
  let mut x : UInt64 := 0
  let mut good := 0
  let mut odd : Array Nat := #[]
  let mut lastOdd : Int := -1000
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if c == 4 then lastOdd := p
    if p + 1 ≥ q && lastOdd + q > p then odd := odd.push (p + 1 - q)
    if good ≥ q then
      let b := (mix x >>> (50 - BBITS)).toNat
      cnt := cnt.modify (b + 1) (· + 1)
  for b in [0:nb] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let mut fill := cnt
  let mut ent : Array UInt32 := Array.replicate (2 * cnt[nb]!.toNat) 0
  x := 0; good := 0
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if good ≥ q then
      let y := mix x
      let b := (y >>> (50 - BBITS)).toNat
      let i := fill[b]!.toNat
      ent := (ent.set! (2 * i) (p + 1 - q).toUInt32).set! (2 * i + 1) (y &&& KMASK).toUInt32
      fill := fill.set! b (i + 1).toUInt32
  return { q, offs := cnt, ent, odd }

/-- Push `(p + BIAS - shift)·16 + bit` for entries t ∈ [t, hi) of the bucket with this key. -/
def scanBucket (ent : Array UInt32) (key : UInt32) (t hi shift bit : Nat) (acc : Array Nat) : Array Nat :=
  if h : t < hi then
    scanBucket ent key (t + 1) hi shift bit
      (if ent[2 * t + 1]! == key then acc.push ((ent[2 * t]!.toNat + BIAS - shift) * 16 + bit) else acc)
  else acc
termination_by hi - t

/-- Seed j (letters r[j·q, j·q+q)): anchors (p + BIAS - j·q)·16 + 2^j, increasing,
for every start p with g[p, p+q) = the seed. -/
def lookup (idx : Idx) (g r : ByteArray) (j : Nat) (v : UInt64) : Array Nat :=
  let q := idx.q
  let o := j * q
  if v >>> 60 == 0 then
    let y := mix v
    let b := (y >>> (50 - BBITS)).toNat
    scanBucket idx.ent (y &&& KMASK).toUInt32 idx.offs[b]!.toNat idx.offs[b + 1]!.toNat o (1 <<< j) #[]
  else
    idx.odd.foldl (init := #[]) fun acc p =>
      if eqRun g r p o (p + q) then acc.push ((p + BIAS - o) * 16 + (1 <<< j)) else acc
/-- Mismatches of r[i, stop) against g[a + i ..] plus `m`, stopping once above `lim`. -/
def hamming (r g : ByteArray) (a i stop lim m : Nat) : Nat :=
  if h : i < stop then
    if r.get! i != g.get! (a + i) then
      if m + 1 > lim then m + 1 else hamming r g a (i + 1) stop lim (m + 1)
    else hamming r g a (i + 1) stop lim m
  else m
termination_by stop - i

/-- Mismatches of the read against g[a ..] (≥ lim + 1 means > lim), only over the
seeds not in `mask` (seeds in `mask` are clean there) and the tail past 4·q. -/
def hamSeeds (r g : ByteArray) (q a mask lim : Nat) : Nat := Id.run do
  let mut m := hamming r g a (4 * q) r.size lim 0
  for j in [0:4] do
    if m ≤ lim && (mask >>> j) % 2 == 0 then m := hamming r g a (j * q) (j * q + q) lim m
  return m

@[inline] def pop4 (mask : Nat) : Nat := ((0x4332322132212110 : UInt64) >>> (4 * mask.toUInt64) &&& 15).toNat

/-- Position of the k-th mismatch (k ≥ 1) of r[i, stop) against g[st + i ..], or `stop`. -/
def fwdMis (r g : ByteArray) (st i stop k : Nat) : Nat :=
  if h : i < stop then
    if r.get! i != g.get! (st + i) then (if k ≤ 1 then i else fwdMis r g st (i + 1) stop (k - 1))
    else fwdMis r g st (i + 1) stop k
  else stop
termination_by stop - i

/-- 1 + position of the k-th mismatch from the right (k ≥ 1) of r[lo, e) against
g[e' ..] with read letter x ↔ g[x + d1 - d0], or `lo` when there are fewer. -/
def bwdMis (r g : ByteArray) (d1 d0 lo e k : Nat) : Nat :=
  if h : lo < e then
    if r.get! (e - 1) != g.get! (e - 1 + d1 - d0) then (if k ≤ 1 then e else bwdMis r g d1 d0 lo (e - 1) (k - 1))
    else bwdMis r g d1 d0 lo (e - 1) k
  else lo
termination_by e - lo

/-- Penalty of window (st, len), len ≠ n, L = |len - n| ≤ 3, if ≤ `lim`; else lim + 1.
The one gap sits before read letter i: read x < i ↔ g[st + x], read x ≥ i + skip ↔
g[st + x + len - n] (skip = L when the read has the extra letters).  With F_k the
k-th mismatch of the prefix diagonal on [0, n - skip) and E_k one past the k-th
last mismatch of the suffix diagonal on [skip, n), "≤ t + u mismatches at some i"
⟺ E_{u+1} - skip ≤ F_{t+1}. -/
def gappedPen (r g : ByteArray) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let mmax := (lim - 6 - 2 * L) / 4
  let skip := if len < n then L else 0
  let F1 := fwdMis r g st 0 (n - skip) 1
  let E1 := bwdMis r g (st + len) n skip n 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if mmax == 0 then lim + 1 else
  let F2 := fwdMis r g st 0 (n - skip) 2
  let E2 := bwdMis r g (st + len) n skip n 2
  assert! mmax == 1
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 6 + 2 * L + 4 else lim + 1

structure Best where
  pen : Nat := cap + 1
  st : Nat := 0
  len : Nat := 0
  amb : Bool := false

@[inline] def Best.add (b : Best) (st len pen : Nat) : Best :=
  if pen < b.pen then { pen, st, len, amb := false }
  else if pen == b.pen && (st != b.st || len != b.len) then { b with amb := true }
  else b

/-- Support of biased anchor `A` (number of seeds clean on its diagonal),
looked up near index `i` of the sorted packed anchors `as` (entries A·16 + seed mask). -/
@[inline] def supNear (as : Array Nat) (i A : Nat) : Nat := Id.run do
  for k in [i - min i 3 : min as.size (i + 4)] do
    if as[k]! / 16 == A then return pop4 (as[k]! % 16)
  return 0

/-- Merge two increasing packed anchor lists (A·16 + mask), joining masks of equal A. -/
partial def merge (x y : Array Nat) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if h : i < x.size then
    if h' : j < y.size then
      let a := x[i]
      let b := y[j]
      if a / 16 < b / 16 then merge x y (i + 1) j (acc.push a)
      else if b / 16 < a / 16 then merge x y i (j + 1) (acc.push b)
      else merge x y (i + 1) (j + 1) (acc.push (a ||| b % 16))
    else merge x y (i + 1) j (acc.push x[i])
  else if h' : j < y.size then merge x y i (j + 1) (acc.push y[j])
  else acc

/-- Number of seeds clean on biased diagonal `A` (checked in the genome). -/
def supAt (r g : ByteArray) (q A : Nat) : Nat := Id.run do
  let mut c := 0
  if A < BIAS then return 0
  for j in [0:4] do
    let p := A - BIAS + j * q
    if p + q ≤ g.size && eqRun g r p (j * q) (p + q) then c := c + 1
  return c

/-- Best window over the anchors of the seeds whose bucket holds ≤ K entries;
also returns B = how many seeds were skipped.  Exact when B = 0 or the result's
penalty is < 4·(4 - B): a window none of whose clean seeds was looked up has
m ≥ 4 - B - (seeds spoiled by its gap) mismatches; with one gap of length L
(spoiling ≤ min(L, 2) seeds) or none, penalty ≥ 4·(4 - B) in every case. -/
def mapK (idx : Lk) (g r : ByteArray) (vs sizes : Array Nat) (K : Nat) : Best × Nat := Id.run do
  let n := r.size
  let q := idx.q
  let l := fun (j : Nat) => if sizes[j]! ≤ K then idx.look g r j vs[j]!.toUInt64 else #[]
  let looked := (if sizes[0]! ≤ K then 1 else 0) + (if sizes[1]! ≤ K then 2 else 0) +
    (if sizes[2]! ≤ K then 4 else 0) + (if sizes[3]! ≤ K then 8 else 0)
  let nB := 4 - pop4 looked
  -- packed anchors A·16 + mask of the looked-up seeds clean on diagonal A - BIAS
  let as := merge (merge (l 0) (l 1) 0 0 #[]) (merge (l 2) (l 3) 0 0 #[]) 0 0 #[]
  let mut b : Best := {}
  -- same-length windows: penalty ≥ 4·(looked-up seeds not clean); best first
  for k in [0:4] do
    if 4 * k ≤ b.pen && !(b.pen == 0 && b.amb) then
      for e in as do
        let A := e / 16
        if pop4 (looked - (looked &&& (e % 16))) == k && A ≥ BIAS && A - BIAS + n ≤ g.size then
          let m := hamSeeds r g q (A - BIAS) (e % 16) (min 3 (b.pen / 4))
          if 4 * m ≤ cap then b := b.add (A - BIAS) n (4 * m)
  -- gapped windows cost ≥ 8; their two diagonals carry ≥ 2 clean seeds (≥ 3 when ≤ 9)
  if b.pen ≥ 8 then
    for i in [0:as.size] do
      let A := as[i]! / 16
      let c := if nB == 0 then pop4 (as[i]! % 16) else supAt r g q A
      for L in [1:4] do
        let need := if min b.pen cap < 10 then 3 else 2
        let sm := if nB == 0 then supNear as i (A - L) else supAt r g q (A - L)
        let sp := if nB == 0 then supNear as i (A + L) else supAt r g q (A + L)
        -- (A, n+L) ends on A+L; (A, n-L) ends on A-L: gap after the seed
        if c + sp ≥ need && A ≥ BIAS && A - BIAS + n + L ≤ g.size then
          b := b.add (A - BIAS) (n + L) (gappedPen r g (A - BIAS) (n + L) (min b.pen cap))
        if c + sm ≥ need && A ≥ BIAS && A - BIAS + n - L ≤ g.size then
          b := b.add (A - BIAS) (n - L) (gappedPen r g (A - BIAS) (n - L) (min b.pen cap))
        -- (A-L, n+L) and (A+L, n-L) end on A: gap before the seed
        if c + sm ≥ need && A ≥ BIAS + L && A - BIAS + n ≤ g.size then
          b := b.add (A - BIAS - L) (n + L) (gappedPen r g (A - BIAS - L) (n + L) (min b.pen cap))
        if c + sp ≥ need && A - BIAS + n ≤ g.size then
          b := b.add (A - BIAS + L) (n - L) (gappedPen r g (A - BIAS + L) (n - L) (min b.pen cap))
  return (b, nB)

/-- Seeds with more than `bigK` bucket entries are looked up only when needed. -/
def bigK : Nat := 32

def mapRead (idx : Lk) (g r : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let q := idx.q
  assert! r.size / 4 == q && r.size + 3 ≤ BIAS
  let vs := #[(seedCode r 0 0 q 0 0).toNat, (seedCode r q 0 q 0 0).toNat,
    (seedCode r (2 * q) 0 q 0 0).toNat, (seedCode r (3 * q) 0 q 0 0).toNat]
  assert! vs.all (· >>> 61 == 0)
  let sizes := vs.map idx.size
  let (b, nB) := mapK idx g r vs sizes bigK
  let b := if nB > 0 && 4 * (4 - nB) ≤ b.pen then (mapK idx g r vs sizes (1 <<< 40)).1 else b
  if b.pen ≤ cap && !b.amb then return some (b.st, b.len, b.pen)
  return none

-- ─── END copied from bench/Proto.lean ───

/-- `n` zero bytes, capacity exactly `n` (doubling with `++` then `extract` costs ~4.5n of RSS). -/
def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut B := ByteArray.emptyWithCapacity n
  for _ in [0:n] do B := B.push 0
  return B

@[inline] def rd32 (B : ByteArray) (j : Nat) : Nat :=
  ((B.get! j).toUInt32 ||| ((B.get! (j + 1)).toUInt32 <<< 8) |||
    ((B.get! (j + 2)).toUInt32 <<< 16) ||| ((B.get! (j + 3)).toUInt32 <<< 24)).toNat

/-- `k` ≤ 4 bytes at `j`, little-endian. -/
@[inline] def rdK (B : ByteArray) (j k : Nat) : Nat :=
  if k == 4 then rd32 B j else Id.run do
    let mut x := 0
    for i in [0:k] do x := x ||| ((B.get! (j + i)).toNat <<< (8 * i))
    return x

def wrK (B : ByteArray) (j k x : Nat) : ByteArray := Id.run do
  let mut B := B
  for i in [0:k] do B := B.set! (j + i) (x >>> (8 * i)).toUInt8
  return B

/-- Packed index.  Indexed: every start `p ≡ 0 (mod s)` of an ACGT-only `w`-letter
word, w = q - s + 1, in bucket `mix(code) >>> (50 - B)` (CSR, `offs` = 2^B + 1
LE UInt32s), entry = LE UInt32 `p` then `kb` bytes = low bits of the key
`mix(code) mod 2^(50-B)`, increasing `p` within a bucket.  A hit is kept when its
key bytes match and (unless the key is exact: s = 1 and 8·kb ≥ 50 - B) the full
q-letter seed equals the genome.  Completeness of sampling: in a clean seed
occurrence g[p, p+q), exactly one o < s has p + o ≡ 0 (mod s), and the w-word at
read offset j·q + o lies inside the seed. -/
structure Pk where
  q : Nat
  w : Nat
  s : Nat
  B : Nat
  kb : Nat
  offs : ByteArray
  ent : ByteArray
  odd : Array Nat
deriving Inhabited

@[inline] def Pk.es (ix : Pk) : Nat := 4 + ix.kb
@[inline] def Pk.exact (ix : Pk) : Bool := ix.s == 1 && 8 * ix.kb + ix.B ≥ 50
@[inline] def Pk.bucket (ix : Pk) (x : UInt64) : Nat := (mix x >>> (50 - ix.B).toUInt64).toNat
@[inline] def Pk.key (ix : Pk) (x : UInt64) : Nat :=
  (mix x &&& (((1 : UInt64) <<< (50 - ix.B).toUInt64) - 1) &&& (((1 : UInt64) <<< (8 * ix.kb).toUInt64) - 1)).toNat
@[inline] def Pk.lo (ix : Pk) (b : Nat) : Nat := rd32 ix.offs (4 * b)
@[inline] def Pk.hi (ix : Pk) (b : Nat) : Nat := rd32 ix.offs (4 * b + 4)

def buildPk (g : ByteArray) (q s B kb : Nat) : Pk := Id.run do
  assert! q == 25 && 1 ≤ s && s ≤ q && B ≤ 32 && kb ≤ 4
  let w := q - s + 1
  let ix0 : Pk := { q, w, s, B, kb, offs := .empty, ent := .empty, odd := #[] }
  let nb := 1 <<< B
  let wmask : UInt64 := (1 <<< (2 * w.toUInt64)) - 1
  let mut cnt := zeroBytes (4 * (nb + 1))
  let mut x : UInt64 := 0
  let mut good := 0
  let mut odd : Array Nat := #[]
  let mut lastOdd : Int := -1000
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if c == 4 then lastOdd := p
    if p + 1 ≥ q && lastOdd + q > p then odd := odd.push (p + 1 - q)
    if good ≥ w && (p + 1 - w) % s == 0 then
      let j := 4 * (ix0.bucket x + 1)
      cnt := wrK cnt j 4 (rd32 cnt j + 1)
  for b in [0:nb] do cnt := wrK cnt (4 * b + 4) 4 (rd32 cnt (4 * b + 4) + rd32 cnt (4 * b))
  let total := rd32 cnt (4 * nb)
  let es := 4 + kb
  let mut fill := cnt
  let mut ent := zeroBytes (es * total)
  x := 0; good := 0
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if good ≥ w && (p + 1 - w) % s == 0 then
      let b := ix0.bucket x
      let i := rd32 fill (4 * b)
      ent := wrK (wrK ent (es * i) 4 (p + 1 - w)) (es * i + 4) kb (ix0.key x)
      fill := wrK fill (4 * b) 4 (i + 1)
  for b in [0:nb] do assert! rd32 fill (4 * b) == rd32 cnt (4 * b + 4)
  return { ix0 with offs := cnt, ent, odd }

/-- Hits in entries [t, hi) of the w-word at read offset `o0 + o` (seed start o0). -/
def scanPk (ix : Pk) (g r : ByteArray) (key t hi o o0 bit : Nat) (acc : Array Nat) : Array Nat :=
  if h : t < hi then
    let e := ix.es * t
    let acc :=
      if ix.kb != 0 && rdK ix.ent (e + 4) ix.kb != key then acc else
      let p' := rd32 ix.ent e
      if p' < o then acc else
      let p := p' - o
      if ix.exact || (p + ix.q ≤ g.size && eqRun g r p o0 (p + ix.q)) then
        acc.push ((p + BIAS - o0) * 16 + bit) else acc
    scanPk ix g r key (t + 1) hi o o0 bit acc
  else acc
termination_by hi - t

/-- Code of the w-word at offset o of a q-letter seed with code v. -/
@[inline] def Pk.sub (ix : Pk) (v : UInt64) (o : Nat) : UInt64 :=
  (v >>> (2 * (ix.q - o - ix.w)).toUInt64) &&& (((1 : UInt64) <<< (2 * ix.w).toUInt64) - 1)

def Pk.look (ix : Pk) (g r : ByteArray) (j : Nat) (v : UInt64) : Array Nat :=
  let q := ix.q
  let o0 := j * q
  if v >>> 60 == 0 then Id.run do
    let mut out : Array Nat := #[]
    for o in [0:ix.s] do
      let x := ix.sub v o
      let b := ix.bucket x
      let l := scanPk ix g r (ix.key x) (ix.lo b) (ix.hi b) o o0 (1 <<< j) #[]
      out := if o == 0 then l else merge out l 0 0 #[]
    return out
  else
    ix.odd.foldl (init := #[]) fun acc p =>
      if eqRun g r p o0 (p + q) then acc.push ((p + BIAS - o0) * 16 + (1 <<< j)) else acc

def Pk.lk (ix : Pk) : Lk where
  q := ix.q
  look := ix.look
  size v := if v >>> 60 != 0 then 0 else
    (List.range ix.s).foldl (init := 0) fun a o =>
      let b := ix.bucket (ix.sub v.toUInt64 o); a + ix.hi b - ix.lo b
  bucketOf v := ix.bucket (ix.sub v.toUInt64 0)

def Idx.lk (idx : Idx) : Lk where
  q := idx.q
  look := lookup idx
  size v := if v >>> 60 != 0 then 0 else
    let b := (mix v.toUInt64 >>> (50 - BBITS)).toNat
    idx.offs[b + 1]!.toNat - idx.offs[b]!.toNat
  bucketOf v := (mix v.toUInt64 >>> (50 - BBITS)).toNat

def memKB : IO String := do
  let st ← IO.FS.readFile "/proc/self/status"
  let f := fun (k : String) => ((st.splitOn "\n").find? (·.startsWith k)).getD "?"
  return s!"{f "VmRSS"} {f "VmHWM"}"

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: spec :: rest := args | return 2
  let g := ((← IO.FS.readFile gpath).splitOn "\n")[1]!.toUTF8
  let rlines := (((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")).toArray
  let reads : Array ByteArray := (Array.range (rlines.size / 2)).map fun i => rlines[2*i+1]!.toUTF8
  IO.println s!"genome {g.size}  reads {reads.size}  mem before index: {← memKB}"
  let t0 ← IO.monoNanosNow
  let (lk, ibytes, nent) ← if spec == "boxed" then do
      let idx := buildIdx g 25
      pure (idx.lk, 8 * (idx.offs.size + idx.ent.size) + 8 * idx.odd.size, idx.ent.size / 2)
    else do
      let [w, s, B, kb] := (spec.splitOn ",").map String.toNat! | throw (IO.userError "spec")
      assert! w == 25
      let ix := buildPk g 25 s B kb
      pure (ix.lk, ix.offs.size + ix.ent.size + 8 * ix.odd.size, ix.ent.size / ix.es)
  IO.println s!"index {spec}: entries {nent}  bytes {ibytes}  bytes/entry {Float.ofNat ibytes / Float.ofNat nent}  bytes/genome-letter {Float.ofNat ibytes / Float.ofNat g.size}"
  let t1 ← IO.monoNanosNow
  IO.println s!"index_seconds {secs t0 t1}  mem after index: {← memKB}"
  let codes := reads.map fun r => (List.range 4).toArray.map fun j => (seedCode r (j * 25) 0 25 0 0).toNat
  -- lookup stage alone: all 4 seeds of every read
  let t2 ← IO.monoNanosNow
  let mut hits := 0
  for i in [0:reads.size] do
    for j in [0:4] do hits := hits + (lk.look g reads[i]! j codes[i]![j]!.toUInt64).size
  let t3 ← IO.monoNanosNow
  IO.println s!"lookup_only_seconds {secs t2 t3}  ns/read {Float.ofNat (t3 - t2) / Float.ofNat reads.size}  seed hits {hits}"
  let sorted := (← IO.getEnv "SORT") == some "1"
  let t4 ← IO.monoNanosNow
  let order : Array Nat := if sorted then
      ((Array.range reads.size).map (fun i => (lk.bucketOf codes[i]![0]!) <<< 24 ||| i)).qsort (· < ·)
        |>.map (· &&& 0xFFFFFF)
    else Array.range reads.size
  assert! reads.size < 1 <<< 24
  let t5 ← IO.monoNanosNow
  let mut res : Array (Option (Nat × Nat × Nat)) := Array.replicate reads.size none
  for i in order do res := res.set! i (mapRead lk g reads[i]!)
  let t6 ← IO.monoNanosNow
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped {mapped}  sort_seconds {secs t4 t5}  map_seconds {secs t5 t6}  reads/s {Float.ofNat reads.size / secs t5 t6}  reads/s incl sort {Float.ofNat reads.size / secs t4 t6}"
  IO.println s!"mem end: {← memKB}"
  if let [dp] := rest then
    IO.FS.writeFile dp (String.join ((List.range reads.size).map fun i =>
      let nm := (rlines[2*i]!.drop 1).toString
      match res[i]! with
      | some (s, l, p) => s!"{nm}\t{s}\t{l}\t{-(Int.ofNat p)}\n"
      | none => s!"{nm}\tnone\n"))
  return 0
