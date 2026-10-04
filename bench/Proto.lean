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
  up costs ≥ 4k (`mapCore`), so lookups stop once 4k > best; gapped windows
  (≥ 8) are only scored when best ≥ 8 and only near diagonals carrying ≥ 2
  clean seeds (≥ 3 when the bound is < 10).
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
def gappedStage (idx : Idx) (vs : Array Nat) (plain : Bool) (r g : ByteArray) (q : Nat) (as : Array Nat) (looked : Nat) (b : Best) : Best := Id.run do
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
        b := b.add (A - BIAS) (n + L) (gappedPen r g (A - BIAS) (n + L) (min b.pen cap))
      if c + sm ≥ need && A ≥ BIAS && A - BIAS + n - L ≤ g.size then
        b := b.add (A - BIAS) (n - L) (gappedPen r g (A - BIAS) (n - L) (min b.pen cap))
      -- (A-L, n+L) and (A+L, n-L) end on A: gap before the seed
      if c + sm ≥ need && A ≥ BIAS + L && A - BIAS + n ≤ g.size then
        b := b.add (A - BIAS - L) (n + L) (gappedPen r g (A - BIAS - L) (n + L) (min b.pen cap))
      if c + sp ≥ need && A - BIAS + n ≤ g.size then
        b := b.add (A - BIAS + L) (n - L) (gappedPen r g (A - BIAS + L) (n - L) (min b.pen cap))
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

/-- Seeds are looked up one at a time, smallest bucket first.  After k seeds,
a window none of whose clean seeds was looked up has penalty ≥ 4k (its k
looked-up seeds are spoiled: by ≥ k mismatches, or by one gap of length L
spoiling ≤ min(L, 2) seeds plus mismatches: 6 + 2L + 4(k - min(L, 2)) ≥ 4k),
so the search stops once 4k > best.  Same-length windows are scored when their
anchor first appears (later seeds cannot change their penalty); gapped ones
only when best ≥ 8, which needs k ≥ 3. -/
def mapCore (idx : Idx) (g r : ByteArray) (init : Best) : Best × Nat := Id.run do
  let n := r.size
  let q := idx.q
  assert! n / 4 == q && n + 3 ≤ BIAS
  let vs := #[(seedCode r 0 0 q 0 0).toNat, (seedCode r q 0 q 0 0).toNat,
    (seedCode r (2 * q) 0 q 0 0).toNat, (seedCode r (3 * q) 0 q 0 0).toNat]
  assert! vs.all (· >>> 61 == 0)
  let plain := vs.all (· >>> 60 == 0) && n == 4 * q
  let sizes := vs.map fun v =>
    if v >>> 60 != 0 then 0 else
    let b := (mix v.toUInt64 >>> (50 - BBITS)).toNat
    (get32 idx.offs (b + 1)).toNat - (get32 idx.offs b).toNat
  let order := #[0, 1, 2, 3].insertionSort (fun i j => sizes[i]! < sizes[j]!)
  let mut as : Array Nat := #[]
  let mut b : Best := init
  let mut looked := 0
  let mut lookups := 0
  for k in [0:4] do
    let j := order[k]!
    looked := looked ||| (1 <<< j)
    lookups := lookups + 1
    let lj := lookup idx g r j vs[j]!.toUInt64
    let fresh := newOnly as lj 0 0 #[]
    as := merge as lj 0 0 #[]
    -- same-length windows of the new anchors
    for e in fresh do
      let A := e / 16
      if A ≥ BIAS && A - BIAS + n ≤ g.size && !(b.pen == 0 && b.amb) then
        let m := hamSeeds idx vs plain r g q (A - BIAS) (e % 16) (min 3 (b.pen / 4))
        if 4 * m ≤ cap then b := b.add (A - BIAS) n (4 * m)
    if k ≥ 2 && b.pen ≥ 8 then b := gappedStage idx vs plain r g q as looked b
    if 4 * (k + 1) > b.pen then break
  return (b, lookups)

/-- Reverse complement (letters other than ACGT kept). -/
def revComp (r : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.emptyWithCapacity r.size
  for i in [0:r.size] do
    let c := r.get! (r.size - 1 - i)
    o := o.push (if c == 65 then 84 else if c == 84 then 65 else if c == 67 then 71 else if c == 71 then 67 else c)
  return o

/-- Placeholder start for "the best so far is on the other strand". -/
def OTHER : Nat := 1 <<< 62

/-- Unique best window (start, len, penalty, reverse?) and the number of seed
lookups.  With `both`, the reverse complement is mapped too, starting from the
forward best: a reverse window that only ties it makes the read ambiguous
(different strand = different window), one that beats it wins.  Exact given
that each strand's search is exact for windows with penalty ≤ its start best. -/
def mapRead (idx : Idx) (g r : ByteArray) (both : Bool) : Option (Nat × Nat × Nat × Bool) × Nat := Id.run do
  let (f, kf) := mapCore idx g r {}
  if !both then
    return (if f.pen ≤ cap && !f.amb then some (f.st, f.len, f.pen, false) else none, kf)
  let (b, kr) := mapCore idx g (revComp r) { f with st := OTHER, len := 0 }
  -- b.amb covers f.amb and reverse windows tying the forward best
  let res := if b.st == OTHER then
      (if b.pen ≤ cap && !b.amb then some (f.st, f.len, f.pen, false) else none)
    else (if b.pen ≤ cap && !b.amb then some (b.st, b.len, b.pen, true) else none)
  return (res, kf + kr)

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
  let glines := (← IO.FS.readFile gpath).splitOn "\n"
  let g := glines[1]!.toUTF8
  let rlines := (((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")).toArray
  let mut reads : Array ByteArray := #[]
  for i in [0:rlines.size / 2] do reads := reads.push rlines[2*i+1]!.toUTF8
  let t0 ← IO.monoNanosNow
  let idx := buildIdx g l0
  assert! l0 == 25
  IO.println s!"index entries: {idx.ent.size / 8}"
  IO.println (← rss)
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
