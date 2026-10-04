import Std.Data.HashMap
/-!
Speed prototype only (NOT proved, not part of the tool).  Measures how fast
the planned fast mapper can go before the proofs are written.

    lake exe proto <genome.fa> <reads.txt> 25 [truth.tsv|-] [dump.tsv]
    env: PROTO_REPS=k (map k times, profiling), LEAN_ABORT_ON_PANIC=1 (asserts abort)

Same answer as `mapSpec` with scoring (0, -4, -6, -2) and T = -12, i.e.
penalty cap 12 (mismatch 4, gap of length L costs 6 + 2L); reads of 100
letters, no N (asserted).  Checked read by read with `bench/check.sh`.
Why each step is exact:

* One gap: cap 12 < 16 = two gaps, so a hit window has at most one gap, of
  length L ≤ 3, and L = |len - n|.
* Seeds and index: 4 seeds of q = 25 letters; a hit window has a seed aligned
  without edits (proved: `exists_clean_seed`).  The index maps every ACGT-only
  25-letter word to its starts (CSR over 2^24 buckets of an invertible hash,
  each entry storing the rest of the hash, so key equality = word equality);
  words with other letters (not N) are found by a direct scan of `odd`.
  So the lookup returns exactly the starts where a seed is clean.
* Shape: the gap is before or after a clean seed, so a hit window with anchor
  a = p - j·q is (a, n), (a, n±L) (gap after) or (a∓L, n±L) (gap before).
* Same-length window: a gapped alignment of it needs 2 gaps (≥ 16), so its
  penalty is 4·mismatches when ≤ 12 (word XOR + popcount on the packed genome).
* Other window: penalty = 6 + 2L + 4·m, m = fewest mismatches over the gap
  position (prefix on the start diagonal, suffix on the end diagonal); m ≤ 1
  under the cap, read off the first two / last two mismatches (`gappedPen`).
* Pigeonhole: a seed looked up but not clean at an anchor costs ≥ 1 mismatch;
  after k seeds are looked up, any window none of whose clean seeds was looked
  up costs ≥ 4k (`mapStreams`), so lookups stop once 4k > best; gapped windows
  (≥ 8) are only scored when best ≥ 8 and only near diagonals carrying ≥ 2
  clean seeds (≥ 3 when the bound is < 10).
* Strands (PROTO_BOTH): the reverse complement is a second stream with the
  same shared best; a window on the other strand is a different window.
* Pairs (PROTO_PAIR): the answer is per-mate `mapSpec` over both strands,
  then the proper-pair filter.  Pairing never prunes a mate's search: a
  pairing window is reported only if it is the mate's unique best over the
  whole genome and both strands, so every other window with penalty ≤ its
  penalty must be ruled out (by the 4k bound above: P/4 + 1 seeds per strand)
  — dropping far candidates would turn a tie into a false unique hit.  The
  only shortcut is skipping mate 2 when mate 1 has no unique best (the filter
  then rejects the pair whatever mate 2 gives).
-/

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

/-- Index of every ACGT-only q-letter word (q = 25): CSR over 2^24 buckets,
entries (pos, key) in increasing pos.  `odd` = starts of the q-windows that
contain a letter other than ACGTN (looked up directly). -/
structure Idx where
  q : Nat
  offs : ByteArray    -- 2^24 + 1 bucket starts, 4 bytes each (little endian)
  ent : ByteArray     -- entries (pos, key), 4 + 4 bytes
  -- ByteArrays, not `Array UInt32`: sharing an Array with a Task makes Lean
  -- walk all its elements once (lean_mark_mt, ~3 s on chr21).
  odd : Array Nat
  pk : ByteArray      -- genome, 2 bits per letter, first letter in the top bits (non-ACGT ↦ 0)
  amb : ByteArray     -- per 32-letter block: 1 when it holds a letter other than ACGT
deriving Inhabited

/-- Little-endian 4-byte packing. -/
def pack32 (a : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * a.size)
  for x in a do
    b := ((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
  return b

@[inline] def get32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! (4 * i)).toUInt32 ||| (b.get! (4 * i + 1)).toUInt32 <<< 8 |||
    (b.get! (4 * i + 2)).toUInt32 <<< 16 ||| (b.get! (4 * i + 3)).toUInt32 <<< 24

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
  let mut pk := ByteArray.mk (Array.replicate (g.size / 4 + 9) 0)
  let mut amb := ByteArray.mk (Array.replicate (g.size / 32 + 1) 0)
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then pk := pk.set! (p / 4) (pk.get! (p / 4) ||| (c.toUInt8 <<< (6 - 2 * (p % 4)).toUInt8))
    else amb := amb.set! (p / 32) 1
  return { q, offs := pack32 cnt, ent := pack32 ent, odd, pk, amb }

/-- 2-bit code of the 25 letters g[p, p+25), first letter in the top bits (as `seedCode`). -/
@[inline] def gword (pk : ByteArray) (p : Nat) : UInt64 :=
  let k := p / 4
  let w := (pk.get! k).toUInt64 <<< 48 ||| (pk.get! (k + 1)).toUInt64 <<< 40 |||
    (pk.get! (k + 2)).toUInt64 <<< 32 ||| (pk.get! (k + 3)).toUInt64 <<< 24 |||
    (pk.get! (k + 4)).toUInt64 <<< 16 ||| (pk.get! (k + 5)).toUInt64 <<< 8 ||| (pk.get! (k + 6)).toUInt64
  (w <<< (8 + 2 * (p % 4)).toUInt64) >>> 14

def M1 : UInt64 := 0x5555555555555555
def M2 : UInt64 := 0x3333333333333333
def M4 : UInt64 := 0x0F0F0F0F0F0F0F0F
def H01 : UInt64 := 0x0101010101010101

/-- Number of nonzero 2-bit groups of x (mismatching letters of an XOR). -/
@[inline] def pop2 (x : UInt64) : Nat :=
  let y := (x ||| (x >>> 1)) &&& M1
  let y := (y &&& M2) + ((y >>> 2) &&& M2)
  let y := (y + (y >>> 4)) &&& M4
  ((y * H01) >>> 56).toNat

/-- g[p, p+len) is all ACGT (so the packed genome is exact there). -/
@[inline] def clean (idx : Idx) (p len : Nat) : Bool := Id.run do
  for k in [p / 32 : (p + len - 1) / 32 + 1] do
    if idx.amb.get! k != 0 then return false
  return true

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

/-- Push `(p + BIAS - shift)·16 + bit` for entries t ∈ [t, hi) of the bucket with this key. -/
def scanBucket (ent : ByteArray) (key : UInt32) (t hi shift bit : Nat) (acc : Array Nat) : Array Nat :=
  if h : t < hi then
    scanBucket ent key (t + 1) hi shift bit
      (if get32 ent (2 * t + 1) == key then acc.push (((get32 ent (2 * t)).toNat + BIAS - shift) * 16 + bit) else acc)
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
    scanBucket idx.ent (y &&& KMASK).toUInt32 (get32 idx.offs b).toNat (get32 idx.offs (b + 1)).toNat o (1 <<< j) #[]
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
seeds not in `mask` (seeds in `mask` are clean there) and the tail past 4·q.
Word compares when read (`plain`) and window are all ACGT. -/
def hamSeeds (idx : Idx) (vs : Array Nat) (plain : Bool) (r g : ByteArray) (q a mask lim : Nat) : Nat := Id.run do
  let mut m := hamming r g a (4 * q) r.size lim 0
  if plain && clean idx a r.size then
    for j in [0:4] do
      if m ≤ lim && (mask >>> j) % 2 == 0 then m := m + pop2 (vs[j]!.toUInt64 ^^^ gword idx.pk (a + j * q))
    return m
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
deriving Inhabited

@[inline] def Best.add (b : Best) (st len pen : Nat) : Best :=
  if pen < b.pen then { pen, st, len, amb := false }
  else if pen == b.pen && (st != b.st || len != b.len) then { b with amb := true }
  else b

/-- Mask of looked-up seeds clean on biased diagonal `A`, found near index `i`
of the increasing packed anchors `as` (entries A·16 + mask). -/
@[inline] def maskNear (as : Array Nat) (i A : Nat) : Nat := Id.run do
  for k in [i - min i 3 : min as.size (i + 4)] do
    if as[k]! / 16 == A then return as[k]! % 16
  return 0

/-- Number of seeds clean on biased diagonal `A`: the looked-up ones from the
masks, the others (not in `looked`) checked in the genome. -/
def supAt (idx : Idx) (vs : Array Nat) (plain : Bool) (r g : ByteArray) (q : Nat) (as : Array Nat) (looked i A : Nat) : Nat := Id.run do
  let mut c := pop4 (maskNear as i A)
  if A < BIAS then return c
  for j in [0:4] do
    let p := A - BIAS + j * q
    if (looked >>> j) % 2 == 0 && p + q ≤ g.size &&
        (if plain && clean idx p q then gword idx.pk p == vs[j]!.toUInt64 else eqRun g r p (j * q) (p + q)) then
      c := c + 1
  return c

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

/-- Gapped windows near the anchors `as` with penalty ≤ min(b.pen, cap).  They cost
≥ 8 and their two diagonals carry ≥ 2 clean seeds (≥ 3 when ≤ 9); supports come
from the masks and, for seeds not looked up, the genome. -/
def gappedStage (idx : Idx) (vs : Array Nat) (plain : Bool) (r g : ByteArray) (q : Nat) (as : Array Nat) (looked tag : Nat) (b : Best) : Best := Id.run do
  let n := r.size
  let mut b := b
  for i in [0:as.size] do
    let A := as[i]! / 16
    let c := supAt idx vs plain r g q as looked i A
    for L in [1:4] do
      let need := if min b.pen cap < 10 then 3 else 2
      let sm := supAt idx vs plain r g q as looked i (A - L)
      let sp := supAt idx vs plain r g q as looked i (A + L)
      -- (A, n+L) ends on A+L; (A, n-L) ends on A-L: gap after the seed
      if c + sp ≥ need && A ≥ BIAS && A - BIAS + n + L ≤ g.size then
        b := b.add (tag + A - BIAS) (n + L) (gappedPen r g (A - BIAS) (n + L) (min b.pen cap))
      if c + sm ≥ need && A ≥ BIAS && A - BIAS + n - L ≤ g.size then
        b := b.add (tag + A - BIAS) (n - L) (gappedPen r g (A - BIAS) (n - L) (min b.pen cap))
      -- (A-L, n+L) and (A+L, n-L) end on A: gap before the seed
      if c + sm ≥ need && A ≥ BIAS + L && A - BIAS + n ≤ g.size then
        b := b.add (tag + A - BIAS - L) (n + L) (gappedPen r g (A - BIAS - L) (n + L) (min b.pen cap))
      if c + sp ≥ need && A - BIAS + n ≤ g.size then
        b := b.add (tag + A - BIAS + L) (n - L) (gappedPen r g (A - BIAS + L) (n - L) (min b.pen cap))
  return b

/-- Anchors of `y` whose diagonal is not in `x` (both increasing). -/
partial def newOnly (x y : Array Nat) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if h : j < y.size then
    if h' : i < x.size then
      if x[i] / 16 < y[j] / 16 then newOnly x y (i + 1) j acc
      else if x[i] / 16 == y[j] / 16 then newOnly x y (i + 1) (j + 1) acc
      else newOnly x y i (j + 1) (acc.push y[j])
    else newOnly x y i (j + 1) (acc.push y[j])
  else acc

/-- One read variant being searched (the read, or its reverse complement);
its windows are told apart from other streams' by adding `tag` to the start. -/
structure Strand where
  r : ByteArray
  vs : Array Nat
  plain : Bool
  sizes : Array Nat
  order : Array Nat
  as : Array Nat := #[]
  looked : Nat := 0
  k : Nat := 0          -- seeds looked up
  tag : Nat
deriving Inhabited

def TAG : Nat := 1 <<< 40

def mkStream (idx : Idx) (r : ByteArray) (tag : Nat) : Strand :=
  let q := idx.q
  let vs := #[(seedCode r 0 0 q 0 0).toNat, (seedCode r q 0 q 0 0).toNat,
    (seedCode r (2 * q) 0 q 0 0).toNat, (seedCode r (3 * q) 0 q 0 0).toNat]
  let sizes := vs.map fun v =>
    if v >>> 60 != 0 then 0 else
    let b := (mix v.toUInt64 >>> (50 - BBITS)).toNat
    (get32 idx.offs (b + 1)).toNat - (get32 idx.offs b).toNat
  { r, vs, plain := vs.all (· >>> 60 == 0) && r.size == 4 * q, sizes, tag,
    order := #[0, 1, 2, 3].insertionSort (fun i j => sizes[i]! < sizes[j]!) }

/-- Look up the stream's next seed (smallest bucket first), score the
same-length windows of its new anchors, and its gapped windows when best ≥ 8
and ≥ 3 seeds are in. -/
def step (idx : Idx) (g : ByteArray) (s : Strand) (b : Best) : Strand × Best := Id.run do
  let n := s.r.size
  let q := idx.q
  let j := s.order[s.k]!
  let looked := s.looked ||| (1 <<< j)
  let lj := lookup idx g s.r j s.vs[j]!.toUInt64
  let fresh := newOnly s.as lj 0 0 #[]
  let as := merge s.as lj 0 0 #[]
  let mut b := b
  for e in fresh do
    let A := e / 16
    if A ≥ BIAS && A - BIAS + n ≤ g.size && !(b.pen == 0 && b.amb) then
      let m := hamSeeds idx s.vs s.plain s.r g q (A - BIAS) (e % 16) (min 3 (b.pen / 4))
      if 4 * m ≤ cap then b := b.add (s.tag + A - BIAS) n (4 * m)
  if s.k ≥ 2 && b.pen ≥ 8 then b := gappedStage idx s.vs s.plain s.r g q as looked s.tag b
  return ({ s with as, looked, k := s.k + 1 }, b)

/-! `mapStreams`: seeds of all streams are looked up one at a time.  After a
stream has looked up k seeds, a window of it none of whose clean seeds was
looked up has penalty ≥ 4k (its k looked-up seeds are spoiled: by ≥ k
mismatches, or by one gap of length L spoiling ≤ min(L, 2) seeds plus
mismatches: 6 + 2L + 4(k - min(L, 2)) ≥ 4k), so a stream is done once
4k > best (shared best: windows of all streams compete).  The next lookup goes
to the stream with fewest lookups, then smallest bucket.  Same-length windows
are scored when their anchor first appears (later seeds cannot change their
penalty, and best only decreases); gapped ones (≥ 8) at every lookup with
k ≥ 3 while best ≥ 8: if the final best is ≥ 8, every stream ended with such a
lookup, over all its anchors. -/
def mapStreams (idx : Idx) (g : ByteArray) (rs : Array ByteArray) : Best × Nat := Id.run do
  assert! rs.all fun r => r.size / 4 == idx.q && r.size + 3 ≤ BIAS && r.size == 4 * idx.q
  let mut ss : Array Strand := (List.range rs.size).toArray.map fun i => mkStream idx rs[i]! (i * TAG)
  assert! ss.all fun s => s.vs.all (· >>> 61 == 0)
  let mut b : Best := {}
  let mut lookups := 0
  for _ in [0:4 * rs.size] do
    if b.pen == 0 && b.amb then break
    let mut pick := ss.size
    for i in [0:ss.size] do
      let s := ss[i]!
      if s.k < 4 && 4 * s.k ≤ b.pen then
        if pick == ss.size then pick := i
        else
          let t := ss[pick]!
          if s.k < t.k || (s.k == t.k && s.sizes[s.order[s.k]!]! < t.sizes[t.order[t.k]!]!) then pick := i
    if pick == ss.size then break
    let (s', b') := step idx g ss[pick]! b
    ss := ss.set! pick s'
    b := b'
    lookups := lookups + 1
  return (b, lookups)

def compTab : ByteArray := Id.run do
  let mut t := ByteArray.mk ((List.range 256).toArray.map (·.toUInt8))
  for (c, v) in [(65, 84), (84, 65), (67, 71), (71, 67)] do t := t.set! c v
  return t

def revCompGo (r : ByteArray) (i : Nat) (o : ByteArray) : ByteArray :=
  if h : i < r.size then revCompGo r (i + 1) (o.set! (r.size - 1 - i) (compTab.get! (r.get! i).toNat)) else o
termination_by r.size - i

/-- Reverse complement (letters other than ACGT kept). -/
def revComp (r : ByteArray) : ByteArray := revCompGo r 0 r   -- first set! copies (r is shared)

/-- Unique best window (start, len, penalty, reverse?) over the read (and
with `both` its reverse complement: a different strand is a different window),
and the number of seed lookups. -/
def mapRead (idx : Idx) (g r : ByteArray) (both : Bool) : Option (Nat × Nat × Nat × Bool) × Nat :=
  let (b, k) := mapStreams idx g (if both then #[r, revComp r] else #[r])
  (if b.pen ≤ cap && !b.amb then some (b.st % TAG, b.len, b.pen, b.st ≥ TAG) else none, k)

abbrev Hit := Nat × Nat × Nat × Bool    -- start, len, penalty, reverse strand?

/-- Chromosome of a hit.  The prototype takes one-chromosome genomes only
(`main` asserts it), so every hit is on chromosome 0. -/
def Hit.chr (_ : Hit) : Nat := 0

/-- Proper pair (`MapSpec.properPair`, spec/PairSpec.lean): same chromosome,
opposite strands, facing, fragment (forward mate start to reverse mate end)
in [lo, hi]. -/
def proper (lo hi : Nat) (a b : Hit) : Bool :=
  let (f, rv) := if a.2.2.2 then (b, a) else (a, b)
  f.chr == rv.chr && f.2.2.2 != rv.2.2.2 && f.1 ≤ rv.1 + rv.2.1 && lo ≤ rv.1 + rv.2.1 - f.1 &&
    rv.1 + rv.2.1 - f.1 ≤ hi

/-- Proper-pair-only mapping: the answer is exactly "each mate's `mapSpec` over
both strands (unique best window), then keep the pair only if both mates map
and `proper` holds", i.e. (mapRead m1 both, mapRead m2 both) filtered.  Mate 2
is not searched when mate 1 is unmapped or ambiguous: the filter rejects the
pair whatever mate 2 gives. -/
def mapPair (idx : Idx) (g : ByteArray) (lo hi : Nat) (m1 m2 : ByteArray) : Option (Hit × Hit) × Nat :=
  match mapRead idx g m1 true with
  | (none, k1) => (none, k1)
  | (some a, k1) =>
    match mapRead idx g m2 true with
    | (some b, k2) => (if proper lo hi a b then some (a, b) else none, k1 + k2)
    | (none, k2) => (none, k1 + k2)

def mapPairs (idx : Idx) (g : ByteArray) (lo hi : Nat) (ps : Array (ByteArray × ByteArray)) (tasks : Nat) :
    Array (Option (Hit × Hit) × Nat) :=
  let f := fun (p : ByteArray × ByteArray) => mapPair idx g lo hi p.1 p.2
  if tasks ≤ 1 then ps.map f else
  let csz := (ps.size + tasks - 1) / tasks
  let ts := (List.range tasks).map fun t => Task.spawn fun _ => (ps.extract (t * csz) (t * csz + csz)).map f
  ts.foldl (fun acc t => acc ++ t.get) #[]

def showHit (h : Hit) : String := s!"{h.1}\t{h.2.1}\t{-(Int.ofNat h.2.2.1)}\t{if h.2.2.2 then "-" else "+"}"

/-- PROTO_PAIR=<mate 2 reads>: `rpath` holds mate 1.  Dump: name, then both hits or none. -/
def pairMain (g : ByteArray) (idx : Idx) (rlines : Array String) (m2path : String) (rest : List String) : IO UInt32 := do
  let l2 := (((← IO.FS.readFile m2path).splitOn "\n").filter (· ≠ "")).toArray
  assert! l2.size == rlines.size
  let ps := (List.range (rlines.size / 2)).toArray.map fun i => (rlines[2*i+1]!.toUTF8, l2[2*i+1]!.toUTF8)
  let lo := ((← IO.getEnv "PAIR_MIN").getD "100").toNat!
  let hi := ((← IO.getEnv "PAIR_MAX").getD "1000").toNat!
  let tasks := ((← IO.getEnv "PROTO_TASKS").getD "1").toNat!
  let t1 ← IO.monoNanosNow
  let out := mapPairs idx g lo hi ps tasks
  let kept := (out.filter (·.1.isSome)).size
  IO.println s!"pairs: {ps.size}  kept: {kept}  lookups/pair: {Float.ofNat (out.foldl (· + ·.2) 0) / Float.ofNat ps.size}"
  let t2 ← IO.monoNanosNow
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"map_seconds: {secs}  pairs/s: {Float.ofNat ps.size / secs}  reads/s: {Float.ofNat (2 * ps.size) / secs}"
  match rest with
  | [_, dp] =>
    let names := (List.range ps.size).map fun i => (rlines[2*i]!.drop 1).toString
    IO.FS.writeFile dp (String.join ((names.zip (out.map (·.1)).toList).map fun (nm, x) => match x with
      | some (a, b) => s!"{nm}\t{showHit a}\t{showHit b}\n"
      | none => s!"{nm}\tnone\n"))
  | _ => pure ()
  match rest with
  | tp :: _ =>
    if tp == "-" then return 0
    let tl := ((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, r) in tl.zip (out.map (·.1)).toList do
      match line.splitOn "\t", r with
      | [_, _, p1, s1, p2, s2], some (a, b) =>
        if p1.toNat! == a.1 + 1 && (s1 == "-") == a.2.2.2 && p2.toNat! == b.1 + 1 && (s2 == "-") == b.2.2.2 then
          right := right + 1
      | _, _ => pure ()
    IO.println s!"pairs_at_true_positions: {right}"
  | [] => pure ()
  return 0

def rss : IO String := do
  let st ← IO.FS.readFile "/proc/self/status"
  return " ".intercalate ((st.splitOn "\n").filter (fun l => l.startsWith "VmRSS" || l.startsWith "VmHWM"))

/-- Map `reads` in `tasks` chunks, one `Task.spawn` each (pure: = reads.map). -/
def mapAll (idx : Idx) (g : ByteArray) (both : Bool) (reads : Array ByteArray) (tasks : Nat) :
    Array (Option (Nat × Nat × Nat × Bool) × Nat) :=
  if tasks ≤ 1 then reads.map (mapRead idx g · both) else
  let csz := (reads.size + tasks - 1) / tasks
  let ts := (List.range tasks).map fun t =>
    Task.spawn fun _ => (reads.extract (t * csz) (t * csz + csz)).map (mapRead idx g · both)
  ts.foldl (fun acc t => acc ++ t.get) #[]

/-- `mapAll` mapping each distinct read once (identical read ⇒ identical answer). -/
def mapDedup (idx : Idx) (g : ByteArray) (both : Bool) (reads : Array ByteArray) (tasks : Nat) :
    Array (Option (Nat × Nat × Nat × Bool) × Nat) := Id.run do
  let mut first : Std.HashMap ByteArray Nat := {}
  let mut uniq : Array ByteArray := #[]
  let mut slot : Array Nat := Array.emptyWithCapacity reads.size
  for r in reads do
    match first.get? r with
    | some i => slot := slot.push i
    | none => first := first.insert r uniq.size; slot := slot.push uniq.size; uniq := uniq.push r
  let out := mapAll idx g both uniq tasks
  return slot.map (out[·]!)

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: l0s :: rest := args | return 2
  let l0 := l0s.toNat!
  let glines := ((← IO.FS.readFile gpath).splitOn "\n").filter (· ≠ "")
  assert! glines.length == 2   -- one chromosome (see `Hit.chr`)
  let g := glines[1]!.toUTF8
  let rlines := (((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")).toArray
  let mut reads : Array ByteArray := #[]
  for i in [0:rlines.size / 2] do reads := reads.push rlines[2*i+1]!.toUTF8
  let t0 ← IO.monoNanosNow
  let idx := buildIdx g l0
  assert! l0 == 25
  IO.println s!"index entries: {idx.ent.size / 8}"
  IO.println (← rss)
  if let some m2 ← IO.getEnv "PROTO_PAIR" then
    IO.println s!"index_seconds: {Float.ofNat ((← IO.monoNanosNow) - t0) / 1e9}"
    return ← pairMain g idx rlines m2 rest
  let t1 ← IO.monoNanosNow
  let reps := ((← IO.getEnv "PROTO_REPS").getD "1").toNat!   -- for profiling
  let tasks := ((← IO.getEnv "PROTO_TASKS").getD "1").toNat!
  let both := (← IO.getEnv "PROTO_BOTH").isSome
  let mut out : Array (Option (Nat × Nat × Nat × Bool) × Nat) := #[]
  let dedup := (← IO.getEnv "PROTO_DEDUP").isSome
  for _ in [0:reps] do out := if dedup then mapDedup idx g both reads tasks else mapAll idx g both reads tasks
  let res := out.map (·.1)
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped: {mapped}  lookups/read: {Float.ofNat (out.foldl (· + ·.2) 0) / Float.ofNat reads.size}"
  let t2 ← IO.monoNanosNow
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}  map_seconds: {secs}  reads/s: {Float.ofNat (reps * reads.size) / secs}  {← rss}"
  match rest with
  | [_, dp] =>
    let names := (List.range (rlines.size / 2)).map fun i => (rlines[2*i]!.drop 1).toString
    IO.FS.writeFile dp (String.join ((names.zip res.toList).map fun (nm, x) => match x with
      | some (s, l, p, rv) => s!"{nm}\t{s}\t{l}\t{-(Int.ofNat p)}" ++ (if both then (if rv then "\t-" else "\t+") else "") ++ "\n"
      | none => s!"{nm}\tnone\n"))
  | _ => pure ()
  match rest with
  | tp :: _ =>
    if tp == "-" then return 0
    let tl := ((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, r) in tl.zip res.toList do
      match line.splitOn "\t", r with
      | [_, _, pos, _], some (s, _, _, false) => if pos.toNat! == s + 1 then right := right + 1
      | _, _ => pure ()
    IO.println s!"at_true_position: {right}"
  | [] => pure ()
  return 0
