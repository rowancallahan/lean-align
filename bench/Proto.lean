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

def code (b : UInt8) : UInt64 :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

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
    if c == 4 && g.get! p != 78 then lastOdd := p
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

/-- Anchors are stored biased by `BIAS` (≥ n) so they are `Nat`s. -/
def BIAS : Nat := 128

/-- Push `p + BIAS - shift` for every start p with g[p, p+q) = r[o, o+q). -/
def lookup (idx : Idx) (g r : ByteArray) (o : Nat) (acc : Array Nat) (shift : Nat) : Array Nat := Id.run do
  let q := idx.q
  let mut x : UInt64 := 0
  let mut plain := true
  for i in [0:q] do
    let c := code (r.get! (o + i))
    assert! r.get! (o + i) != 78
    if c == 4 then plain := false
    x := (x <<< 2) ||| (c &&& 3)
  let mut acc := acc
  if plain then
    let y := mix x
    let b := (y >>> (50 - BBITS)).toNat
    let key := (y &&& KMASK).toUInt32
    for t in [idx.offs[b]!.toNat:idx.offs[b + 1]!.toNat] do
      if idx.ent[2 * t + 1]! == key then acc := acc.push (idx.ent[2 * t]!.toNat + BIAS - shift)
  else
    for p in idx.odd do
      let mut ok := true
      for u in [0:q] do
        if g.get! (p + u) != r.get! (o + u) then ok := false; break
      if ok then acc := acc.push (p + BIAS - shift)
  return acc

/-- Mismatches of `r` against `g[a ..]`, stopping once above `lim`. -/
def hamming (r g : ByteArray) (a lim : Nat) : Nat := Id.run do
  let mut m := 0
  for i in [0:r.size] do
    if r.get! i != g.get! (a + i) then
      m := m + 1
      if m > lim then return m
  return m

/-- Penalty of window (st, len), len ≠ n, |len - n| ≤ 3, if ≤ `lim`; else lim + 1. -/
def gappedPen (r g : ByteArray) (st len lim : Nat) : Nat := Id.run do
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then return lim + 1
  let mmax := (lim - 6 - 2 * L) / 4
  let skip := if len < n then L else 0
  -- read k < i ↔ g[st + k];  read k ≥ i + skip ↔ g[st + k + len - n]
  let mut suf := 0
  for k in [skip:n] do
    if r.get! k != g.get! (st + len + k - n) then suf := suf + 1
  let mut pre := 0
  let mut best := pre + suf
  for i in [0:n - skip] do
    if r.get! i != g.get! (st + i) then pre := pre + 1
    if pre > mmax then break
    if r.get! (i + skip) != g.get! (st + len + i + skip - n) then suf := suf - 1
    best := min best (pre + suf)
  if best > mmax then return lim + 1
  return 6 + 2 * L + 4 * best

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
looked up near index `i` of the sorted packed anchors `as` (entries A·8 + support). -/
@[inline] def supNear (as : Array Nat) (i A : Nat) : Nat := Id.run do
  for k in [i - min i 3 : min as.size (i + 4)] do
    if as[k]! / 8 == A then return as[k]! % 8
  return 0

def mapRead (idx : Idx) (g r : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let n := r.size
  let q := idx.q
  assert! n / 4 == q && n + 3 ≤ BIAS
  let mut raw : Array Nat := #[]
  for j in [0:4] do raw := lookup idx g r (j * q) raw (j * q)
  let sorted := raw.qsort (· < ·)
  -- packed anchors A·8 + support, support = number of seeds clean on diagonal A - BIAS
  let mut as : Array Nat := #[]
  for A in sorted do
    if as.size > 0 && as.back! / 8 == A then as := as.modify (as.size - 1) (· + 1)
    else as := as.push (A * 8 + 1)
  let mut b : Best := {}
  -- same-length windows: penalty ≥ 4·(4 - support); best first
  for k in [0:4] do
    let sup := 4 - k
    if 4 * k ≤ b.pen && !(b.pen == 0 && b.amb) then
      for e in as do
        let A := e / 8
        if e % 8 == sup && A ≥ BIAS && A - BIAS + n ≤ g.size then
          let m := hamming r g (A - BIAS) (min 3 (b.pen / 4))
          if 4 * m ≤ cap then b := b.add (A - BIAS) n (4 * m)
  -- gapped windows cost ≥ 8; their two diagonals carry ≥ 2 clean seeds (≥ 3 when ≤ 9)
  if b.pen ≥ 8 then
    for i in [0:as.size] do
      let A := as[i]! / 8
      let c := as[i]! % 8
      for L in [1:4] do
        let need := if min b.pen cap < 10 then 3 else 2
        let sm := supNear as i (A - L)
        let sp := supNear as i (A + L)
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
  if b.pen ≤ cap && !b.amb then return some (b.st, b.len, b.pen)
  return none

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
  IO.println s!"index entries: {idx.ent.size / 2}"
  let t1 ← IO.monoNanosNow
  let reps := ((← IO.getEnv "PROTO_REPS").getD "1").toNat!   -- for profiling
  let mut res : Array (Option (Nat × Nat × Nat)) := #[]
  for _ in [0:reps] do
    res := #[]
    for r in reads do res := res.push (mapRead idx g r)
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped: {mapped}"
  let t2 ← IO.monoNanosNow
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}  map_seconds: {secs}  reads/s: {Float.ofNat (reps * reads.size) / secs}"
  match rest with
  | [_, dp] =>
    let names := (List.range (rlines.size / 2)).map fun i => (rlines[2*i]!.drop 1).toString
    IO.FS.writeFile dp (String.join ((names.zip res.toList).map fun (nm, x) => match x with
      | some (s, l, p) => s!"{nm}\t{s}\t{l}\t{-(Int.ofNat p)}\n"
      | none => s!"{nm}\tnone\n"))
  | _ => pure ()
  match rest with
  | tp :: _ =>
    if tp == "-" then return 0
    let tl := ((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, r) in tl.zip res.toList do
      match line.splitOn "\t", r with
      | [_, _, pos, _], some (s, _, _) => if pos.toNat! == s + 1 then right := right + 1
      | _, _ => pure ()
    IO.println s!"at_true_position: {right}"
  | [] => pure ()
  return 0
