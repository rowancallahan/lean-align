/-!
Speed prototype 2 (NOT proved, not part of the tool).  Same answer as
`mapSpec` with the default scoring (match 0, mismatch -4, gap 6 + 2L) and
T = -12, by a different method than bench/Proto.lean:

* No DP.  With these penalties a window scoring >= -12 is either the read's
  length with <= 3 mismatches (penalty 4h), or one gap of L <= 3 letters
  (6 + 2L) plus at most one mismatch when L = 1.  Each case is decided by
  forward/backward mismatch scans on at most 7 diagonals per anchor.
* Exact-match shortcut: every exact copy of the read contains every seed, so
  the hits of the rarest seed decide whether the read occurs exactly once
  (mapped, penalty 0) or more (unmapped) without looking at other seeds.
* Index words containing a non-ACGT letter are left out (reads are ACGT).

    lake exe proto2 <genome.fa> <reads.txt> <l0> [truth.tsv] [check|noext|noexact|check-noext|check-noexact|parN]

`noext` verifies seed hits against the genome instead of the index's stored
next letters (the cache-miss experiment); `noexact` skips the exact-match shortcut;
`parN` also maps the reads in N `Task.spawn` chunks and asserts the same answers.

`check` also runs bench/Proto.lean's banded Gotoh mapper on every read and
asserts both answers are equal.
-/

def code (b : UInt8) : UInt32 :=
  if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 0

def isACGT (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

def wordCode (a : ByteArray) (p l0 : Nat) : UInt32 := Id.run do
  let mut h : UInt32 := 0
  for i in [0:l0] do h := h * 4 + code (a.get! (p + i))
  return h

structure Idx where
  l0 : Nat
  offs : Array UInt32
  pos : Array UInt32
  /-- 2-bit code of the `25 - l0` letters after each indexed word (0xFFFFFFFF if any is
  non-ACGT or off the genome), so the full-seed check does not touch the genome. -/
  ext : Array UInt32 := #[]

/-- CSR index of every l0-mer made only of A/C/G/T. -/
def buildIdx (g : ByteArray) (l0 : Nat) : Idx := Id.run do
  let nb := 4 ^ l0
  let mask : UInt32 := (4 ^ l0 - 1).toUInt32
  let mut cnt : Array UInt32 := Array.replicate (nb + 1) 0
  let mut h : UInt32 := 0
  let mut run := 0
  for p in [0:g.size] do
    let b := g.get! p
    h := (h * 4 + code b) &&& mask
    run := if isACGT b then run + 1 else 0
    if run ≥ l0 then cnt := cnt.modify (h.toNat + 1) (· + 1)
  for b in [0:nb] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let offs := cnt
  let mut fill := cnt
  let mut pos : Array UInt32 := Array.replicate offs[nb]!.toNat 0
  h := 0; run := 0
  for p in [0:g.size] do
    let b := g.get! p
    h := (h * 4 + code b) &&& mask
    run := if isACGT b then run + 1 else 0
    if run ≥ l0 then
      let i := fill[h.toNat]!
      pos := pos.set! i.toNat (p + 1 - l0).toUInt32
      fill := fill.set! h.toNat (i + 1)
  let el := 25 - l0
  let ext := pos.map fun p =>
    let p := p.toNat + l0
    if p + el ≤ g.size && (List.range el).all (fun u => isACGT (g.get! (p + u))) then wordCode g p el
    else 0xFFFFFFFF
  return { l0, offs, pos, ext }

/-- Genome letter at `s + r` compared with read letter `r`; off-genome = mismatch. -/
@[inline] def eqAt (r g : ByteArray) (s : Int) (i : Nat) : Bool :=
  let q := s + i
  q ≥ 0 && q.toNat < g.size && g.get! q.toNat == r.get! i

/-- Positions of the first `k` mismatches of the read on diagonal `s`,
scanning forward (`n` where there are fewer). -/
def fwd (r g : @& ByteArray) (s : Int) (k : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty k
  for i in [0:r.size] do
    if out.size == k then break
    if !eqAt r g s i then out := out.push i
  while out.size < k do out := out.push r.size
  return out

/-- Lengths of the read suffixes with 0 and with at most 1 mismatch on
diagonal `s`. -/
def bwd (r g : @& ByteArray) (s : Int) : Nat × Nat := Id.run do
  let n := r.size
  let mut b0 := n
  let mut found := false
  for t in [0:n] do
    let i := n - 1 - t
    if !eqAt r g s i then
      if found then return (b0, t)
      b0 := t; found := true
  return (b0, n)


/-! Packed scans: 2-bit genome, 32 letters per UInt64, mismatches by XOR. -/

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

/-- Little-endian UInt64 words, 32 letters each, two words of padding. -/
def packWith (f : UInt8 → UInt32) (g : ByteArray) : ByteArray := Id.run do
  let nw := g.size / 32 + 3
  let mut out := ByteArray.emptyWithCapacity (8 * nw)
  for w in [0:nw] do
    let mut x : UInt64 := 0
    for k in [0:32] do
      let p := 32 * w + k
      if p < g.size then x := x ||| (f (g.get! p)).toUInt64 <<< (2 * k).toUInt64
    for b in [0:8] do out := out.push (x >>> (8 * b).toUInt64).toUInt8
  return out

@[inline] def popcnt (x : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0f0f0f0f0f0f0f0f
  let h1 : UInt64 := 0x0101010101010101
  let x := x - ((x >>> 1) &&& m1)
  let x := (x &&& m2) + ((x >>> 2) &&& m2)
  let x := (x + (x >>> 4)) &&& m4
  (x * h1) >>> 56

/-- Index of the lowest set bit (x ≠ 0).  Not `UInt64.log2`: lean.h implements that as a loop. -/
@[inline] def ctz (x : UInt64) : UInt64 := popcnt ((x &&& (0 - x)) - 1)

/-- Index of the highest set bit (x ≠ 0). -/
@[inline] def msb (x : UInt64) : UInt64 :=
  let x := x ||| (x >>> 1)
  let x := x ||| (x >>> 2)
  let x := x ||| (x >>> 4)
  let x := x ||| (x >>> 8)
  let x := x ||| (x >>> 16)
  let x := x ||| (x >>> 32)
  popcnt x - 1

def pack := packWith code
/-- Lane value 1 at every non-ACGT letter (always a mismatch: reads are ACGT). -/
def packN := packWith fun b => if isACGT b then 0 else 1

/-- Bit 2i set iff letter i differs, for the 32 letters of chunk `c` (chunk 3 keeps 4 letters). -/
@[inline] def mmMask (rd pk nm : ByteArray) (su : USize) (c : Nat) : UInt64 :=
  let x := letters32U rd (USize.ofNat (32 * c)) ^^^ letters32U pk (su + USize.ofNat (32 * c))
  let m := ((x ||| (x >>> 1)) &&& 0x5555555555555555) ||| letters32U nm (su + USize.ofNat (32 * c))
  if c == 3 then m &&& 0xff else m

/-- Append the lane positions of `m` (lowest first, offset `base`) to `acc`, which holds
up to 4 positions of 8 bits and their count in the top byte; stop at `k`.  Tail recursion
with UInt64 arguments: a `while` loop would carry its state boxed (allocating). -/
def drainF (m base acc k : UInt64) : Nat → UInt64
  | 0 => acc
  | f + 1 =>
    let c := acc >>> 56
    if m == 0 || c ≥ k then acc
    else drainF (m &&& (m - 1)) base ((acc ||| ((base + ctz m / 2) <<< (8 * c))) + ((1 : UInt64) <<< 56)) k f

/-- Same, highest lane first, position counted from the read's end (99 - p). -/
def drainB (m base acc : UInt64) : Nat → UInt64
  | 0 => acc
  | f + 1 =>
    let c := acc >>> 56
    if m == 0 || c ≥ 2 then acc
    else
      let hb := msb m
      drainB (m ^^^ ((1 : UInt64) <<< hb)) base
        ((acc ||| ((99 - (base + hb / 2)) <<< (8 * c))) + ((1 : UInt64) <<< 56)) f

@[inline] def lane (acc : UInt64) (i : UInt64) (n : Nat) : Nat :=
  if i < acc >>> 56 then ((acc >>> (8 * i)) &&& 0xff).toNat else n

/-- Packed `fwd`; byte version near the genome ends. -/
def fwdP (r rd pk nm g : @& ByteArray) (s : Int) (k : Nat) : Array Nat :=
  if s < 0 || s.toNat + 200 > g.size then fwd r g s k else
    let su := USize.ofNat s.toNat
    let kk := k.toUInt64
    let acc := drainF (mmMask rd pk nm su 0) 0 0 kk 32
    let acc := drainF (mmMask rd pk nm su 1) 32 acc kk 32
    let acc := drainF (mmMask rd pk nm su 2) 64 acc kk 32
    let acc := drainF (mmMask rd pk nm su 3) 96 acc kk 32
    (Array.range k).map fun i => lane acc i.toUInt64 r.size

def bwdP (r rd pk nm g : @& ByteArray) (s : Int) : Nat × Nat :=
  if s < 0 || s.toNat + 200 > g.size then bwd r g s else
    let su := USize.ofNat s.toNat
    let acc := drainB (mmMask rd pk nm su 3) 96 0 32
    let acc := drainB (mmMask rd pk nm su 2) 64 acc 32
    let acc := drainB (mmMask rd pk nm su 1) 32 acc 32
    let acc := drainB (mmMask rd pk nm su 0) 0 acc 32
    (lane acc 0 r.size, lane acc 1 r.size)

/-- (start, len, penalty) of every window with penalty <= 12 around
anchor diagonal `d`. -/
def closedForm (r rd pk nm g : @& ByteArray) (d : Int) (acc : Array (Nat × Nat × Nat)) :
    Array (Nat × Nat × Nat) := Id.run do
  let n := r.size
  let mut acc := acc
  let push (acc : Array (Nat × Nat × Nat)) (s : Int) (len pen : Nat) :=
    if s ≥ 0 && s.toNat + len ≤ g.size && pen ≤ 12 then acc.push (s.toNat, len, pen) else acc
  -- forward scans on d-3 .. d+3 (4 mismatches on d, 2 elsewhere)
  let mut F : Array (Array Nat) := #[]
  let mut Bk : Array (Nat × Nat) := #[]
  for o in [0:7] do
    let s := d + o - 3
    F := F.push (fwdP r rd pk nm g s (if o == 3 then 4 else 2))
    Bk := Bk.push (bwdP r rd pk nm g s)
  -- same length: Hamming on d
  let f := F[3]!
  let h := if f[3]! < n then 4 else if f[2]! < n then 3 else if f[1]! < n then 2 else if f[0]! < n then 1 else 0
  acc := push acc d n (4 * h)
  for L in [1:4] do
    let gp := 6 + 2 * L
    -- deletion (window n + L): prefix on s, suffix on s + L;  s ∈ {d, d - L}
    for s in [d, d - L] do
      let a := F[(s - d + 3).toNat]!
      let b := Bk[(s + L - d + 3).toNat]!
      if a[0]! + b.1 ≥ n then acc := push acc s (n + L) gp
      else if L == 1 && (a[1]! + b.1 ≥ n || a[0]! + b.2 ≥ n) then acc := push acc s (n + L) (gp + 4)
    -- insertion (window n - L): prefix on s, suffix on s - L;  s ∈ {d, d + L}
    for s in [d, d + L] do
      let a := F[(s - d + 3).toNat]!
      let b := Bk[(s - L - d + 3).toNat]!
      if a[0]! + b.1 + L ≥ n then acc := push acc s (n - L) gp
      else if L == 1 && (a[1]! + b.1 + L ≥ n || a[0]! + b.2 + L ≥ n) then acc := push acc s (n - L) (gp + 4)
  return acc

def uniqueBest (hits : Array (Nat × Nat × Nat)) : Option (Nat × Nat × Nat) := Id.run do
  let mut best : Option (Nat × Nat × Nat) := none
  for h in hits do
    match best with
    | none => best := some h
    | some b => if h.2.2 < b.2.2 then best := some h
  match best with
  | none => return none
  | some b =>
    if hits.any (fun h => h.2.2 == b.2.2 && (h.1 != b.1 || h.2.1 != b.2.1)) then return none
    return some b

structure Stats where
  exact1 : Nat := 0     -- decided by the exact shortcut: unique copy
  exactN : Nat := 0     -- decided by the exact shortcut: several copies
  general : Nat := 0
  anchors : Nat := 0
  seedHits : Nat := 0

def seedRange (idx : @& Idx) (r : @& ByteArray) (o : Nat) : Nat × Nat :=
  let h := wordCode r o idx.l0
  (idx.offs[h.toNat]!.toNat, idx.offs[h.toNat + 1]!.toNat)

def mapRead (useExt useExact : Bool) (idx : @& Idx) (pk nm g r : @& ByteArray) (st : Stats) : Option (Nat × Nat × Nat) × Stats := Id.run do
  let n := r.size
  let q := n / 4
  let mut st := st
  -- exact shortcut on the rarest seed
  let mut bj := 0
  let mut bsz := idx.pos.size + 1
  for j in [0:4] do
    let (lo, hi) := seedRange idx r (j * q)
    if hi - lo < bsz then bj := j; bsz := hi - lo
  let (lo, hi) := if useExact then seedRange idx r (bj * q) else (0, 0)
  let mut copies : Array Nat := #[]
  for t in [lo:hi] do
    if copies.size ≥ 2 then break   -- two exact copies tie at the best possible score
    let s : Int := (idx.pos[t]!.toNat : Int) - (bj * q : Nat)
    if s ≥ 0 && s.toNat + n ≤ g.size then
      let mut ok := true
      for i in [0:n] do
        if g.get! (s.toNat + i) != r.get! i then ok := false; break
      if ok then copies := copies.push s.toNat
  if useExact && copies.size == 1 then
    return (some (copies[0]!, n, 0), { st with exact1 := st.exact1 + 1 })
  if useExact && copies.size > 1 then
    return (none, { st with exactN := st.exactN + 1 })
  -- general path: all seeds, full-seed check, closed form per anchor
  let useExt := useExt && q == 25
  let mut anchors : Array Int := #[]
  for j in [0:4] do
    let (lo, hi) := seedRange idx r (j * q)
    let rext := wordCode r (j * q + idx.l0) (q - idx.l0)
    st := { st with seedHits := st.seedHits + (hi - lo) }
    for t in [lo:hi] do
      if useExt && idx.ext[t]! != rext then continue
      let p := idx.pos[t]!.toNat
      let mut ok := decide (p + q ≤ g.size)
      if ok then
        for u in [idx.l0:q] do
          if g.get! (p + u) != r.get! (j * q + u) then ok := false; break
      if ok then
        let a : Int := (p : Int) - (j * q : Nat)
        if !(anchors.contains a) then anchors := anchors.push a
  let mut hits : Array (Nat × Nat × Nat) := #[]
  let rd := (pack r).extract 0 48
  for a in anchors do hits := closedForm r rd pk nm g a hits
  -- one entry per window (the closed form gives one penalty per window per anchor)
  let mut uniq : Array (Nat × Nat × Nat) := #[]
  for h in hits do
    if !(uniq.any fun u => u.1 == h.1 && u.2.1 == h.2.1) then uniq := uniq.push h
  return (uniqueBest uniq, { st with general := st.general + 1, anchors := st.anchors + anchors.size })

/-! bench/Proto.lean's mapper, for `check`. -/
namespace Old

def INF : Nat := 1000

def bandScores (r g : ByteArray) (s : Nat) (B cap : Nat) : Array Nat := Id.run do
  let n := r.size
  let W := 2 * B + 1
  let mut H : Array Nat := Array.replicate W INF
  let mut E : Array Nat := Array.replicate W INF
  let mut F : Array Nat := Array.replicate W INF
  for k in [B:W] do
    let j := k - B
    if j == 0 then H := H.set! k 0
    else
      let e := 6 + 2 * j
      E := E.set! k e; H := H.set! k e
  for i in [1:n+1] do
    let ri := r.get! (i - 1)
    let mut nH : Array Nat := Array.replicate W INF
    let mut nE : Array Nat := Array.replicate W INF
    let mut nF : Array Nat := Array.replicate W INF
    let mut rowMin := INF
    for k in [0:W] do
      if i + k ≥ B then
        let j := i + k - B
        let f := if k + 1 < W then min (H[k+1]! + 8) (F[k+1]! + 2) else INF
        let e := if k ≥ 1 && j ≥ 1 then min (nH[k-1]! + 8) (nE[k-1]! + 2) else INF
        let d := if j ≥ 1 && s + j - 1 < g.size then
            H[k]! + (if g.get! (s + j - 1) == ri then 0 else 4) else INF
        let h := min d (min e f)
        let h := if h > cap then INF else h
        nH := nH.set! k h; nE := nE.set! k (min e INF); nF := nF.set! k (min f INF)
        rowMin := min rowMin h
    H := nH; E := nE; F := nF
    if rowMin ≥ INF then return Array.replicate W INF
  return H

def scoreLocus (r g : ByteArray) (a : Int) (B cap : Nat) (acc : Array (Nat × Nat × Nat)) :
    Array (Nat × Nat × Nat) := Id.run do
  let mut acc := acc
  for ds in [0:2*B+1] do
    let s := a + ds - B
    if s ≥ 0 then
      let res := bandScores r g s.toNat B cap
      for k in [0:2*B+1] do
        let pen := res[k]!
        let len := r.size + k - B
        if pen ≤ cap && s.toNat + len ≤ g.size then acc := acc.push (s.toNat, len, pen)
  return acc

def mapRead (idx : Idx) (g r : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let n := r.size
  let q := n / 4
  let mut anchors : Array Int := #[]
  for j in [0:4] do
    let (lo, hi) := seedRange idx r (j * q)
    for t in [lo:hi] do
      let p := idx.pos[t]!.toNat
      let mut ok := decide (p + q ≤ g.size)
      if ok then
        for u in [idx.l0:q] do
          if g.get! (p + u) != r.get! (j * q + u) then ok := false; break
      if ok then
        let a : Int := (p : Int) - (j * q : Nat)
        if !(anchors.contains a) then anchors := anchors.push a
  let mut hits : Array (Nat × Nat × Nat) := #[]
  for a in anchors do hits := scoreLocus r g a 3 12 hits
  return uniqueBest hits

end Old

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: l0s :: rest := args | return 2
  let l0 := l0s.toNat!
  let glines := (← IO.FS.readFile gpath).splitOn "\n"
  let g := glines[1]!.toUTF8
  let rlines := ((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")
  -- reads with a non-ACGT letter are dropped (and their truth lines with them)
  let mut reads : Array ByteArray := #[]
  let mut keep : Array Bool := #[]
  for i in [0:rlines.length / 2] do
    let r := rlines[2*i+1]!.toUTF8
    assert! r.size == 100
    keep := keep.push (r.toList.all isACGT)
    if r.toList.all isACGT then reads := reads.push r
  IO.println s!"reads: {reads.size}  dropped (non-ACGT): {keep.size - reads.size}"
  let t0 ← IO.monoNanosNow
  let idx := buildIdx g l0
  let pk := pack g
  let nm := packN g
  IO.println s!"index entries: {idx.pos.size}"
  -- packed scans agree with byte scans (random positions and windows holding non-ACGT letters)
  let probe := (Array.range 2000).map (fun k => ((k * 2654435761) % (g.size - 300) : Nat)) ++
    ((Array.range (g.size - 300)).filter (fun p => !isACGT (g.get! (p + 50))) |>.extract 0 2000)
  for k in [0:probe.size] do
    let r := reads[k % reads.size]!
    let rd := (pack r).extract 0 48
    let s : Int := (probe[k]! : Nat)
    do
      for o in [0:3] do
        let s' := s + o
        assert! fwdP r rd pk nm g s' 4 == fwd r g s' 4
        assert! bwdP r rd pk nm g s' == bwd r g s'
  let t1 ← IO.monoNanosNow
  let mut res : Array (Option (Nat × Nat × Nat)) := #[]
  let mut st : Stats := {}
  let mode := (rest.drop 1).headD ""
  let useExt := !(mode.endsWith "noext")
  let useExact := !(mode.endsWith "noexact")
  for r in reads do
    let (o, st') := mapRead useExt useExact idx pk nm g r st
    res := res.push o; st := st'
  let t2 ← IO.monoNanosNow
  let mapped := (res.filter (·.isSome)).size
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"mapped: {mapped}"
  IO.println s!"exact unique: {st.exact1}  exact repeated: {st.exactN}  general: {st.general}  anchors/general read: {Float.ofNat st.anchors / Float.ofNat st.general}  seed hits/general read: {Float.ofNat st.seedHits / Float.ofNat st.general}"
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}  map_seconds: {secs}  reads/s: {Float.ofNat reads.size / secs}"
  let tl ← match rest with
    | tp :: _ => pure ((((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1).zip keep.toList
        |>.filter (·.2) |>.map (·.1))
    | [] => pure []
  let mut right := 0
  for (line, r) in tl.zip res.toList do
    match line.splitOn "\t", r with
    | [_, _, pos, _], some (s, _, _) => if pos.toNat! == s + 1 then right := right + 1
    | _, _ => pure ()
  IO.println s!"at_true_position: {right}"
  if mode.startsWith "par" then
    let nt := (mode.drop 3).toNat!
    let chunk := (reads.size + nt - 1) / nt
    let t5 ← IO.monoNanosNow
    -- `z` (always 0) ties the work to the clock read; pure code is otherwise hoisted above it
    let z := if t5 == 0 then 1 else 0
    let tasks := (List.range nt).map fun c => Task.spawn fun _ =>
      (reads.extract (c * chunk + z) ((c + 1) * chunk + z)).map fun r => (mapRead true true idx pk nm g r {}).1
    let parts ← tasks.mapM (fun t => (IO.wait t : IO _))   -- an IO action, so it stays between the two clock reads
    let out := parts.foldl (· ++ ·) #[]
    let t6 ← IO.monoNanosNow
    IO.println s!"{nt} tasks: reads/s {Float.ofNat reads.size / (Float.ofNat (t6 - t5) / 1e9)}  same answers: {out == res}"
    assert! out == res
  if mode.startsWith "check" then
    let t3 ← IO.monoNanosNow
    let mut diff := 0
    for (r, o) in reads.toList.zip res.toList do
      if Old.mapRead idx g r != o then diff := diff + 1
    let t4 ← IO.monoNanosNow
    IO.println s!"old mapper reads/s: {Float.ofNat reads.size / (Float.ofNat (t4 - t3) / 1e9)}  disagreements: {diff}"
    assert! diff == 0
  return 0
