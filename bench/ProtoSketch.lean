/-!
Speed prototype only (NOT proved, not part of the tool).  Measures how fast
the planned fast mapper can go before the proofs are written.

    lake exe proto <genome.fa> <reads.txt> <l0> [truth.tsv|-] [dump.tsv]

Same answer as `mapSpec` with scoring (0, -4, -6, -2) and T = -12, i.e.
penalty cap 12 (mismatch 4, gap of length L costs 6 + 2L).  Why each step is exact:

* Cap 12 < 16 = two gaps, so a hit window has at most one gap, of length
  L ≤ 3 (6 + 2·3 = 12), and L = |len - n|.
* Seeds: 4 seeds of q = n/4 letters; a hit window has ≤ 3 edits, so one seed
  is aligned without edits (proved: `exists_clean_seed`).  The index is
  `LookupComplete` for ACGT words (reads must be ACGT), the full q-letter
  seed is then checked, so every hit window has an anchor a = p - j·q.
* Shape: the one gap is before or after the clean seed, so a hit window is
  (a, n) (no gap), (a, n+e) (gap after the seed) or (a+s, n-s) (gap before),
  0 < |e|, |s| ≤ 3: 13 windows per anchor.
* Same-length window: any gapped alignment needs ≥ 2 gaps (≥ 16), so its
  penalty is 4·(mismatches) when ≤ 12.
* Other window, L = |len - n|: penalty = 6 + 2L + 4·m, m = fewest mismatches
  over the gap position, prefix on the start diagonal, suffix on the end one.
* Gapped windows cost ≥ 8, so when the best same-length window costs ≤ 4 they
  cannot tie or beat it and are not scored.
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

/-- Seed scheme.  kind 0: every k-mer; 1: (w,k) minimizers, random order;
2: closed (k,s) syncmers; 3: open (k,s,t=w) syncmers (no window guarantee:
only for counting).  Keys are k-mer codes; the 25-letter seed is verified at
the anchor, so a lookup returns exactly the occurrences of the seed. -/
structure Scheme where
  kind : Nat
  k : Nat
  w : Nat := 1
  s : Nat := 0
deriving Inhabited

/-- Guaranteed length: every ACGT string of this length has a selected k-mer
that is selected wherever the string occurs. -/
def Scheme.L (sc : Scheme) : Nat :=
  match sc.kind with
  | 1 => sc.w + sc.k - 1
  | 2 => 2 * sc.k - sc.s - 1
  | _ => sc.k

/-- Order hash (splitmix finaliser). -/
@[inline] def ordH (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 31)) * 0xBF58476D1CE4E5B9
  let x := (x ^^^ (x >>> 29)) * 0x94D049BB133111EB
  x ^^^ (x >>> 32)

/-- Leftmost minimum of `h` over [i, i + w). -/
@[inline] def argminH (h : Nat → UInt64) (i w : Nat) : Nat := Id.run do
  let mut m := i
  let mut v := h i
  for d in [i + 1 : i + w] do
    if h d < v then m := d; v := h d
  return m

/-- Closed syncmer test for the k-mer code `x`: its smallest s-mer (by ordH)
is its first or its last. -/
@[inline] def closedSync (k s : Nat) (x : UInt64) : Bool := Id.run do
  let sm : UInt64 := (1 <<< (2 * s.toUInt64)) - 1
  let first := ordH ((x >>> (2 * (k - s)).toUInt64) &&& sm)
  let last := ordH (x &&& sm)
  let mut mn := min first last
  for i in [1 : k - s] do
    mn := min mn (ordH ((x >>> (2 * (k - s - i)).toUInt64) &&& sm))
  return mn == first || mn == last

/-- Open syncmer test: smallest s-mer at offset t (value tie allowed). -/
@[inline] def openSync (k s t : Nat) (x : UInt64) : Bool := Id.run do
  let sm : UInt64 := (1 <<< (2 * s.toUInt64)) - 1
  let atV := ordH ((x >>> (2 * (k - s - t)).toUInt64) &&& sm)
  for i in [0 : k - s + 1] do
    if ordH ((x >>> (2 * (k - s - i)).toUInt64) &&& sm) < atV then return false
  return true

/-- Index of the selected ACGT k-mers: CSR over 2^24 buckets,
entries (pos, key) in increasing pos.  `odd` = starts of the q-windows that
contain a letter other than ACGTN (looked up directly). -/
structure Idx where
  q : Nat
  sch : Scheme
  offs : Array UInt32
  ent : Array UInt32
  odd : Array Nat
  pk : ByteArray      -- genome, 2 bits per letter, first letter in the top bits (non-ACGT ↦ 0)
  amb : ByteArray     -- per 32-letter block: 1 when it holds a letter other than ACGT
deriving Inhabited

/-- Marks (1) the starts of the selected k-mers. -/
def selectPositions (g : ByteArray) (sch : Scheme) : ByteArray := Id.run do
  let k := sch.k
  let wmask : UInt64 := (1 <<< (2 * k.toUInt64)) - 1
  let mut sel := ByteArray.mk (Array.replicate g.size 0)
  let mut x : UInt64 := 0
  let mut good := 0
  let mut ring : Array UInt64 := Array.replicate 64 0   -- ordH of the k-mer starting at i, at i % 64
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if good ≥ k then
      let i := p + 1 - k
      match sch.kind with
      | 0 => sel := sel.set! i 1
      | 1 =>
        ring := ring.set! (i % 64) (ordH x)
        if good ≥ sch.L then
          let m := argminH (fun d => ring[d % 64]!) (i + 1 - sch.w) sch.w
          sel := sel.set! m 1
      | 2 => if closedSync k sch.s x then sel := sel.set! i 1
      | _ => if openSync k sch.s sch.w x then sel := sel.set! i 1
  return sel

def buildIdx (g : ByteArray) (q : Nat) (sch : Scheme) : Idx := Id.run do
  assert! q == 25 && sch.k ≤ 25 && sch.L ≤ q
  let k := sch.k
  let sel := selectPositions g sch
  let nb := 1 <<< BBITS.toNat
  let wmask : UInt64 := (1 <<< (2 * k.toUInt64)) - 1
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
    if good ≥ k && sel.get! (p + 1 - k) == 1 then
      let b := (mix x >>> (50 - BBITS)).toNat
      cnt := cnt.modify (b + 1) (· + 1)
  for b in [0:nb] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let mut fill := cnt
  let mut ent : Array UInt32 := Array.replicate (2 * cnt[nb]!.toNat) 0
  x := 0; good := 0
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then x := ((x <<< 2) ||| c) &&& wmask; good := good + 1 else good := 0
    if good ≥ k && sel.get! (p + 1 - k) == 1 then
      let y := mix x
      let b := (y >>> (50 - BBITS)).toNat
      let i := fill[b]!.toNat
      ent := (ent.set! (2 * i) (p + 1 - k).toUInt32).set! (2 * i + 1) (y &&& KMASK).toUInt32
      fill := fill.set! b (i + 1).toUInt32
  let mut pk := ByteArray.mk (Array.replicate (g.size / 4 + 9) 0)
  let mut amb := ByteArray.mk (Array.replicate (g.size / 32 + 1) 0)
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then pk := pk.set! (p / 4) (pk.get! (p / 4) ||| (c.toUInt8 <<< (6 - 2 * (p % 4)).toUInt8))
    else amb := amb.set! (p / 32) 1
  return { q, sch, offs := cnt, ent, odd, pk, amb }

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
def scanBucket (ent : Array UInt32) (key : UInt32) (t hi shift bit : Nat) (acc : Array Nat) : Array Nat :=
  if h : t < hi then
    scanBucket ent key (t + 1) hi shift bit
      (if ent[2 * t + 1]! == key then acc.push ((ent[2 * t]!.toNat + BIAS - shift) * 16 + bit) else acc)
  else acc
termination_by hi - t

/-- k-mer of the q-letter seed code `v` at offset d. -/
@[inline] def subCode (v : UInt64) (q k d : Nat) : UInt64 :=
  (v >>> (2 * (q - k - d)).toUInt64) &&& ((1 <<< (2 * k.toUInt64)) - 1)

/-- Offsets (in the seed) of the k-mers the scheme selects inside the seed,
seen from the seed alone.  Each of them is selected at the matching place of
every genome occurrence of the seed. -/
def seedOffsets (sch : Scheme) (q : Nat) (v : UInt64) : Array Nat := Id.run do
  let k := sch.k
  match sch.kind with
  | 0 => return (List.range (q - k + 1)).toArray
  | 1 =>
    let mut ds : Array Nat := #[]
    for i in [0 : q - sch.L + 1] do
      let m := argminH (fun d => ordH (subCode v q k d)) i sch.w
      if !ds.contains m then ds := ds.push m
    return ds
  | _ =>
    let mut ds : Array Nat := #[]
    for d in [0 : q - k + 1] do
      if closedSync k sch.s (subCode v q k d) then ds := ds.push d
    return ds

@[inline] def bucketSize (idx : Idx) (x : UInt64) : Nat :=
  let b := (mix x >>> (50 - BBITS)).toNat
  idx.offs[b + 1]!.toNat - idx.offs[b]!.toNat

/-- The selected offset with the smallest bucket, and that bucket's size. -/
def bestOffset (idx : Idx) (v : UInt64) : Nat × Nat := Id.run do
  if idx.sch.kind == 0 && idx.sch.k == idx.q then return (0, bucketSize idx v)
  let ds := seedOffsets idx.sch idx.q v
  assert! ds.size > 0
  let mut best := (ds[0]!, bucketSize idx (subCode v idx.q idx.sch.k ds[0]!))
  for d in ds do
    let z := bucketSize idx (subCode v idx.q idx.sch.k d)
    if z < best.2 then best := (d, z)
  return best

/-- The q letters at p equal the seed (code `v`, read letters r[o, o+q)). -/
@[inline] def seedAt (idx : Idx) (g r : ByteArray) (v : UInt64) (p o : Nat) : Bool :=
  p + idx.q ≤ g.size &&
    (if clean idx p idx.q then gword idx.pk p == v else eqRun g r p o (p + idx.q))

/-- Bucket entries t ∈ [t, hi) with this key at genome pos ≥ d whose seed matches at pos − d:
push (pos − d + BIAS − o)·16 + bit. -/
def scanBucketV (idx : Idx) (g r : ByteArray) (v : UInt64) (key : UInt32) (t hi d o bit : Nat)
    (acc : Array Nat) : Array Nat :=
  if h : t < hi then
    let pos := idx.ent[2 * t]!.toNat
    scanBucketV idx g r v key (t + 1) hi d o bit
      (if idx.ent[2 * t + 1]! == key && pos ≥ d && (idx.sch.k == idx.q || seedAt idx g r v (pos - d) o)
       then acc.push ((pos - d + BIAS - o) * 16 + bit) else acc)
  else acc
termination_by hi - t

/-- Seed j (letters r[j·q, j·q+q)): anchors (p + BIAS - j·q)·16 + 2^j, increasing,
for every start p with g[p, p+q) = the seed. -/
def lookup (idx : Idx) (g r : ByteArray) (j : Nat) (v : UInt64) (d : Nat) : Array Nat :=
  let q := idx.q
  let o := j * q
  if v >>> 60 == 0 then
    let y := mix (subCode v q idx.sch.k d)
    let b := (y >>> (50 - BBITS)).toNat
    scanBucketV idx g r v (y &&& KMASK).toUInt32 idx.offs[b]!.toNat idx.offs[b + 1]!.toNat d o (1 <<< j) #[]
  else
    idx.odd.foldl (init := #[]) fun acc p =>
      if eqRun g r p o (p + q) then acc.push ((p + BIAS - o) * 16 + (1 <<< j)) else acc

/-- Per-seed counts for one ACGT seed: (bucket entries scanned, key matches, verified). -/
def seedStats (idx : Idx) (g r : ByteArray) (j : Nat) (v : UInt64) : Nat × Nat × Nat := Id.run do
  let q := idx.q
  let (d, _) := bestOffset idx v
  let y := mix (subCode v q idx.sch.k d)
  let b := (y >>> (50 - BBITS)).toNat
  let key := (y &&& KMASK).toUInt32
  let mut kh := 0
  let mut ok := 0
  for t in [idx.offs[b]!.toNat : idx.offs[b + 1]!.toNat] do
    if idx.ent[2 * t + 1]! == key then
      kh := kh + 1
      let pos := idx.ent[2 * t]!.toNat
      if pos ≥ d && seedAt idx g r v (pos - d) (j * q) then ok := ok + 1
  return (idx.offs[b + 1]!.toNat - idx.offs[b]!.toNat, kh, ok)

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
def mapRead (idx : Idx) (g r : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let n := r.size
  let q := idx.q
  assert! n / 4 == q && n + 3 ≤ BIAS
  let vs := #[(seedCode r 0 0 q 0 0).toNat, (seedCode r q 0 q 0 0).toNat,
    (seedCode r (2 * q) 0 q 0 0).toNat, (seedCode r (3 * q) 0 q 0 0).toNat]
  assert! vs.all (· >>> 61 == 0)
  let plain := vs.all (· >>> 60 == 0) && n == 4 * q
  let bo := vs.map fun v =>
    if v >>> 60 != 0 then (0, 0) else bestOffset idx v.toUInt64
  let order := #[0, 1, 2, 3].insertionSort (fun i j => bo[i]!.2 < bo[j]!.2)
  let mut as : Array Nat := #[]
  let mut b : Best := {}
  let mut looked := 0
  for k in [0:4] do
    let j := order[k]!
    looked := looked ||| (1 <<< j)
    let lj := lookup idx g r j vs[j]!.toUInt64 bo[j]!.1
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
  if b.pen ≤ cap && !b.amb then return some (b.st, b.len, b.pen)
  return none


def parseScheme (s : String) : Scheme :=
  match (s.splitOn ":").map String.toNat! with
  | [0, k] => { kind := 0, k }
  | [1, k, w] => { kind := 1, k, w }
  | [2, k, s] => { kind := 2, k, s }
  | [3, k, s, t] => { kind := 3, k, s, w := t }
  | _ => panic! "scheme: 0:k | 1:k:w | 2:k:s | 3:k:s:t"

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: schs :: rest := args | return 2
  let sch := parseScheme schs
  let glines := (← IO.FS.readFile gpath).splitOn "\n"
  let g := glines[1]!.toUTF8
  let rlines := (((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")).toArray
  let mut reads : Array ByteArray := #[]
  for i in [0:rlines.size / 2] do reads := reads.push rlines[2*i+1]!.toUTF8
  let t0 ← IO.monoNanosNow
  let idx := buildIdx g 25 sch
  let ne := idx.ent.size / 2
  IO.println s!"scheme {schs}  L={sch.L}  index entries: {ne}  ({Float.ofNat ne / Float.ofNat g.size} per base)  index MB (8/entry + 64 offs): {Float.ofNat (8 * ne + 4 * idx.offs.size) / 1e6}"
  let t1 ← IO.monoNanosNow
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}"
  if sch.kind == 3 then
    -- open syncmers: no window guarantee; count read seeds without one
    let mut none := 0
    let mut tot := 0
    for r in reads do
      for j in [0:4] do
        let v := seedCode r (j * 25) 0 25 0 0
        if v >>> 60 == 0 then
          tot := tot + 1
          let any := (List.range (25 - sch.k + 1)).any fun d => openSync sch.k sch.s sch.w (subCode v 25 sch.k d)
          if !any then none := none + 1
    IO.println s!"open syncmer: seeds without a syncmer: {none} / {tot}"
    return 0
  -- per-seed lookup statistics (all 4 seeds, no early stop)
  let mut sc := 0
  let mut kh := 0
  let mut ok := 0
  let mut ns := 0
  for r in reads do
    for j in [0:4] do
      let v := seedCode r (j * 25) 0 25 0 0
      if v >>> 60 == 0 then
        let (a, b, c) := seedStats idx g r j v
        sc := sc + a; kh := kh + b; ok := ok + c; ns := ns + 1
  let f (x : Nat) : Float := Float.ofNat x / Float.ofNat ns
  IO.println s!"per seed: bucket entries scanned {f sc}  key matches {f kh}  verified anchors {f ok}"
  let t2 ← IO.monoNanosNow
  let reps := ((← IO.getEnv "PROTO_REPS").getD "1").toNat!
  let mut res : Array (Option (Nat × Nat × Nat)) := #[]
  for _ in [0:reps] do
    res := #[]
    for r in reads do res := res.push (mapRead idx g r)
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped: {mapped}"
  let t3 ← IO.monoNanosNow
  let secs := Float.ofNat (t3 - t2) / 1e9
  IO.println s!"map_seconds: {secs}  reads/s: {Float.ofNat (reps * reads.size) / secs}"
  match rest with
  | [_, dp] =>
    let names := (List.range (rlines.size / 2)).map fun i => (rlines[2*i]!.drop 1).toString
    IO.FS.writeFile dp (String.join ((names.zip res.toList).map fun (nm, x) => match x with
      | some (s, l, p) => s!"{nm}\t{s}\t{l}\t{-(Int.ofNat p)}\n"
      | none => s!"{nm}\tnone\n"))
  | _ => pure ()
  return 0
