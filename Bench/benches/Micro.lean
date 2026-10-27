/-!
Micro-benchmarks of Lean code patterns used by a mapper (NOT proved, not part
of the tool).  Inspect the C with `.lake/build/ir/Micro.c`.

    lake exe micro
-/

/-- Deterministic pseudo-random bytes over ACGT. -/
def genome (n : Nat) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := 88172645463325252
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    a := a.push ((#[65, 67, 71, 84] : Array UInt8)[(x >>> 30 &&& 3).toNat]!)
  return a

/-! ### 1. Position table: `Array UInt32` (boxed, 8 B/entry) vs packed `ByteArray` (4 B/entry) -/

def gatherArray (pos : Array UInt32) (iters : Nat) : UInt64 := Id.run do
  let mut s : UInt64 := 0
  let mut x : UInt64 := 1
  for _ in [0:iters] do
    x := x * 6364136223846793005 + 1442695040888963407
    s := s + (pos[(x >>> 20).toNat % pos.size]!).toUInt64
  return s

@[inline] def getU32 (a : ByteArray) (i : Nat) : UInt32 :=
  (a.get! (4*i)).toUInt32 ||| (a.get! (4*i+1)).toUInt32 <<< 8 |||
  (a.get! (4*i+2)).toUInt32 <<< 16 ||| (a.get! (4*i+3)).toUInt32 <<< 24

def gatherBytes (pos : ByteArray) (iters : Nat) : UInt64 := Id.run do
  let n := pos.size / 4
  let mut s : UInt64 := 0
  let mut x : UInt64 := 1
  for _ in [0:iters] do
    x := x * 6364136223846793005 + 1442695040888963407
    s := s + (getU32 pos ((x >>> 20).toNat % n)).toUInt64
  return s

/-! ### 2. Byte compare loop: `for i in [0:n]` + `get!` + Nat vs USize tail recursion + `uget` -/

def hamNat (r g : ByteArray) (s : Nat) : Nat := Id.run do
  let mut h := 0
  for i in [0:r.size] do
    if g.get! (s + i) != r.get! i then h := h + 1
  return h

def hamUSizeLoop (r g : ByteArray) (s : USize) (i : USize) (h : UInt32) : (fuel : Nat) → UInt32
  | 0 => h
  | fuel + 1 =>
    if hi : i.toNat < r.size then
      if hg : (s + i).toNat < g.size then
        let h := if g.uget (s + i) hg != r.uget i hi then h + 1 else h
        hamUSizeLoop r g s (i + 1) h fuel
      else h
    else h

/-! ### 3. 2-bit packed genome, 32 letters per UInt64, Hamming by XOR + popcount -/

@[inline] def code2 (b : UInt8) : UInt64 :=
  if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 0

/-- Packed genome as a ByteArray of little-endian UInt64 words, 32 letters per word. -/
def pack (g : ByteArray) : ByteArray := Id.run do
  let nw := g.size / 32 + 2
  let mut out := ByteArray.emptyWithCapacity (8 * nw)
  for w in [0:nw] do
    let mut x : UInt64 := 0
    for k in [0:32] do
      let p := 32 * w + k
      if p < g.size then x := x ||| code2 (g.get! p) <<< (2 * k).toUInt64
    for b in [0:8] do out := out.push (x >>> (8 * b).toUInt64).toUInt8
  return out

@[inline] def word (pk : ByteArray) (w : Nat) : UInt64 :=
  (pk.get! (8*w)).toUInt64 ||| (pk.get! (8*w+1)).toUInt64 <<< 8 |||
  (pk.get! (8*w+2)).toUInt64 <<< 16 ||| (pk.get! (8*w+3)).toUInt64 <<< 24 |||
  (pk.get! (8*w+4)).toUInt64 <<< 32 ||| (pk.get! (8*w+5)).toUInt64 <<< 40 |||
  (pk.get! (8*w+6)).toUInt64 <<< 48 ||| (pk.get! (8*w+7)).toUInt64 <<< 56

/-- 32 letters starting at letter `p`. -/
@[inline] def letters32 (pk : ByteArray) (p : Nat) : UInt64 :=
  let w := p / 32
  let o := (2 * (p % 32)).toUInt64
  if o == 0 then word pk w else (word pk w >>> o) ||| (word pk (w + 1) <<< (64 - o))

@[inline] def popcnt (x : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0f0f0f0f0f0f0f0f
  let h1 : UInt64 := 0x0101010101010101
  let x := x - ((x >>> 1) &&& m1)
  let x := (x &&& m2) + ((x >>> 2) &&& m2)
  let x := (x + (x >>> 4)) &&& m4
  (x * h1) >>> 56

/-- Mismatching letters among 32: OR the two bits of each 2-bit lane. -/
@[inline] def mm32 (a b : UInt64) : UInt64 :=
  let x := a ^^^ b
  popcnt ((x ||| (x >>> 1)) &&& 0x5555555555555555)

/-- Hamming distance of a 100-letter read (packed in 4 words, last one 4 letters). -/
def hamPacked (rd : Array UInt64) (pk : ByteArray) (s : Nat) : UInt64 :=
  mm32 rd[0]! (letters32 pk s) + mm32 rd[1]! (letters32 pk (s + 32)) +
  mm32 rd[2]! (letters32 pk (s + 64)) + mm32 rd[3]! (letters32 pk (s + 96) &&& 0xff)


/-! ### 3b. Same, with USize indices and `uget` (no bounds checks, no Nat arithmetic) -/

theorem idx_le (i : USize) (k : Nat) (hk : k < 4294967296) : (i + USize.ofNat k).toNat ≤ i.toNat + k := by
  have hk' : (USize.ofNat k).toNat = k := USize.toNat_ofNat_of_lt_32 hk
  rw [USize.toNat_add, hk']; exact Nat.mod_le _ _

@[inline] def wordU (pk : ByteArray) (i : USize) (h : i.toNat + 8 ≤ pk.size) : UInt64 :=
  (pk.uget i (by omega)).toUInt64 |||
  (pk.uget (i + USize.ofNat 1) (by have := idx_le i 1 (by decide); omega)).toUInt64 <<< 8 |||
  (pk.uget (i + USize.ofNat 2) (by have := idx_le i 2 (by decide); omega)).toUInt64 <<< 16 |||
  (pk.uget (i + USize.ofNat 3) (by have := idx_le i 3 (by decide); omega)).toUInt64 <<< 24 |||
  (pk.uget (i + USize.ofNat 4) (by have := idx_le i 4 (by decide); omega)).toUInt64 <<< 32 |||
  (pk.uget (i + USize.ofNat 5) (by have := idx_le i 5 (by decide); omega)).toUInt64 <<< 40 |||
  (pk.uget (i + USize.ofNat 6) (by have := idx_le i 6 (by decide); omega)).toUInt64 <<< 48 |||
  (pk.uget (i + USize.ofNat 7) (by have := idx_le i 7 (by decide); omega)).toUInt64 <<< 56

/-- 32 letters starting at letter `p` (0 when out of range). -/
@[inline] def letters32U (pk : ByteArray) (p : USize) : UInt64 :=
  let i := (p >>> 5) <<< 3
  let o := ((p &&& 31) <<< 1).toUInt64
  if h : i.toNat + 16 ≤ pk.size then
    let a := wordU pk i (by omega)
    let b := wordU pk (i + USize.ofNat 8) (by have := idx_le i 8 (by decide); omega)
    if o == 0 then a else (a >>> o) ||| (b <<< (64 - o))
  else 0

/-- Read packed as 32 bytes (4 LE words) in a ByteArray, so nothing is boxed. -/
def hamPackedU (rd : ByteArray) (pk : ByteArray) (s : USize) : UInt64 :=
  if h : 32 ≤ rd.size then
    mm32 (wordU rd 0 (by simp; omega)) (letters32U pk s) +
    mm32 (wordU rd (USize.ofNat 8) (by rw [USize.toNat_ofNat_of_lt_32 (by decide)]; omega)) (letters32U pk (s + 32)) +
    mm32 (wordU rd (USize.ofNat 16) (by rw [USize.toNat_ofNat_of_lt_32 (by decide)]; omega)) (letters32U pk (s + 64)) +
    mm32 (wordU rd (USize.ofNat 24) (by rw [USize.toNat_ofNat_of_lt_32 (by decide)]; omega)) (letters32U pk (s + 96) &&& 0xff)
  else 0

/-! ### 4. Returning a pair (allocates) vs packing into UInt64 (no allocation) -/

@[noinline] def pairRet (x : Nat) : Nat × Nat := (x % 7, x % 11)
@[noinline] def packRet (x : UInt64) : UInt64 := (x % 7) <<< 32 ||| (x % 11)

def time (label : String) (reps : Nat) (f : Unit → IO UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let v ← f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {Float.ofNat (t1 - t0) / Float.ofNat reps} ns/op  (check {v})"

def main : IO UInt32 := do
  let n := 46000000
  let g := genome n
  let pos : Array UInt32 := Array.ofFn (n := n) fun i => (i.val * 2654435761 % n).toUInt32
  let posB : ByteArray := Id.run do
    let mut b := ByteArray.emptyWithCapacity (4 * n)
    for v in pos do
      b := b.push v.toUInt8; b := b.push (v >>> 8).toUInt8
      b := b.push (v >>> 16).toUInt8; b := b.push (v >>> 24).toUInt8
    return b
  let iters := 10000000
  time "random gather, Array UInt32 (boxed)" iters fun _ => pure (gatherArray pos iters)
  time "random gather, ByteArray u32 LE    " iters fun _ => pure (gatherBytes posB iters)
  let reads : Array ByteArray := (Array.range 1000).map fun k => g.extract (k * 40000) (k * 40000 + 100)
  let pk := pack g
  let packed : Array (Array UInt64) := (Array.range 1000).map fun k =>
    #[letters32 pk (k * 40000), letters32 pk (k * 40000 + 32), letters32 pk (k * 40000 + 64),
      letters32 pk (k * 40000 + 96) &&& 0xff]
  let packedB : Array ByteArray := packed.map fun ws => Id.run do
    let mut b := ByteArray.emptyWithCapacity 32
    for w in ws do
      for k in [0:8] do b := b.push (w >>> (8 * k).toUInt64).toUInt8
    return b
  let calls := 10000000
  time "Hamming 100 B, for/get!/Nat        " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + (hamNat reads[c % 1000]! g ((c * 7919) % (n - 200))).toUInt64
    return s
  time "Hamming 100 B, USize/uget recursion" calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + (hamUSizeLoop reads[c % 1000]! g ((c * 7919) % (n - 200)).toUSize 0 0 100).toUInt64
    return s
  time "Hamming 100 letters, 2-bit packed  " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + hamPacked packed[c % 1000]! pk ((c * 7919) % (n - 200))
    return s
  time "  hot cache: for/get!/Nat           " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + (hamNat reads[c % 1000]! g ((c * 7919) % 4000)).toUInt64
    return s
  time "  hot cache: USize/uget recursion   " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + (hamUSizeLoop reads[c % 1000]! g ((c * 7919) % 4000).toUSize 0 0 100).toUInt64
    return s
  time "  hot cache: 2-bit packed           " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + hamPacked packed[c % 1000]! pk ((c * 7919) % 4000)
    return s
  time "Hamming 100 letters, packed + uget  " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + hamPackedU packedB[c % 1000]! pk ((c * 7919) % (n - 200)).toUSize
    return s
  time "  hot cache: packed + uget         " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + hamPackedU packedB[c % 1000]! pk ((c * 7919) % 4000).toUSize
    return s
  time "empty loop (harness overhead)      " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do s := s + (packedB[c % 1000]!).size.toUInt64 + ((c * 7919) % 4000).toUInt64
    return s
  for c in [0:1000] do
    let s := (c * 7919) % (n - 200)
    assert! (hamNat reads[c]! g s).toUInt64 == hamPackedU packedB[c]! pk s.toUSize
  -- sanity: packed and byte Hamming agree
  for c in [0:1000] do
    let s := (c * 7919) % (n - 200)
    assert! (hamNat reads[c]! g s).toUInt64 == hamPacked packed[c]! pk s
  time "pair return (alloc)                " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do
      let (a, b) := pairRet c
      s := s + (a + b).toUInt64
    return s
  time "UInt64-packed return               " calls fun _ => do
    let mut s : UInt64 := 0
    for c in [0:calls] do
      let v := packRet c.toUInt64
      s := s + (v >>> 32) + (v &&& 0xffffffff)
    return s
  return 0
