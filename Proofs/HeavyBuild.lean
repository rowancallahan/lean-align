import Std.Data.HashMap
import MzIndex

/-! # Builder of the heavy 25-mer table (NOT proved: `Proofs/Heavy.lean`'s check `heavyOk`, run at build time in
`indexOk`, is what the proofs use; a wrong table only costs speed)

Windows: 25 letters, all `A`/`C`/`G`/`T` (uppercase), inside one chromosome. Canonical code of a window: the smaller
of its 2-bit code and its reverse complement's. Two passes over the chromosomes:
1. saturating byte counters indexed by a 28-bit hash of the canonical code (256 MB);
2. exact counts (a hash map) of the canonical codes whose counter reached `gaveUpRepeats`.
Codes with at least `gaveUpRepeats` windows (both strands) are kept, each with its reverse complement, sorted, and
written as 25 letters each. -/

namespace Spec.HeavyBuild

def thr : Nat := 200   -- `gaveUpRepeats` (Proofs/Answer.lean); only the table size depends on it

def hbits : Nat := 28

@[inline] def code (b : UInt8) : UInt64 :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

@[inline] def hidx (c : UInt64) : Nat := ((c * 0x9E3779B97F4A7C15) >>> (64 - hbits.toUInt64)).toNat

def mask50 : UInt64 := 0x3FFFFFFFFFFFF

-- one chromosome, pass 1: bump the counter of every window's canonical code
def pass1 (g : ByteArray) (i : Nat) (f r : UInt64) (len : Nat) (cnt : ByteArray) : ByteArray :=
  if h : i < g.size then
    let b := code g[i]
    if b == 4 then pass1 g (i + 1) 0 0 0 cnt
    else
      let f := ((f <<< 2) ||| b) &&& mask50
      let r := (r >>> 2) ||| ((3 - b) <<< 48)
      if len + 1 ≥ 25 then
        let j := hidx (min f r)
        let v := cnt.get! j
        pass1 g (i + 1) f r (len + 1) (if v < 255 then cnt.set! j (v + 1) else cnt)
      else pass1 g (i + 1) f r (len + 1) cnt
  else cnt
termination_by g.size - i

-- pass 2: exact counts of the codes whose counter is full enough
def pass2 (cnt : ByteArray) (g : ByteArray) (i : Nat) (f r : UInt64) (len : Nat)
    (m : Std.HashMap UInt64 Nat) : Std.HashMap UInt64 Nat :=
  if h : i < g.size then
    let b := code g[i]
    if b == 4 then pass2 cnt g (i + 1) 0 0 0 m
    else
      let f := ((f <<< 2) ||| b) &&& mask50
      let r := (r >>> 2) ||| ((3 - b) <<< 48)
      if len + 1 ≥ 25 then
        let c := min f r
        if thr ≤ (cnt.get! (hidx c)).toNat then
          pass2 cnt g (i + 1) f r (len + 1) (m.alter c fun o => some (o.getD 0 + 1))
        else pass2 cnt g (i + 1) f r (len + 1) m
      else pass2 cnt g (i + 1) f r (len + 1) m
  else m
termination_by g.size - i

-- reverse complement of a 25-letter code
def rcCode (c : UInt64) : UInt64 := Id.run do
  let mut x := c
  let mut y : UInt64 := 0
  for _ in [0:25] do
    y := (y <<< 2) ||| (3 - (x &&& 3))
    x := x >>> 2
  return y

def letter (v : UInt64) : UInt8 := if v == 0 then 65 else if v == 1 then 67 else if v == 2 then 71 else 84

def emit (b : ByteArray) (c : UInt64) : ByteArray := Id.run do
  let mut b := b
  for j in [0:25] do
    b := b.push (letter ((c >>> (2 * (24 - j)).toUInt64) &&& 3))
  return b

-- the table: 25 letters per entry, sorted
def table (gbs : Array ByteArray) : ByteArray :=
  let cnt := gbs.foldl (fun cnt g => pass1 g 0 0 0 0 cnt) (MapSpec.Mz.zeros (2 ^ hbits))
  let m := gbs.foldl (fun m g => pass2 cnt g 0 0 0 0 m) {}
  let codes := m.fold (fun acc c n => if thr ≤ n then (acc.push c).push (rcCode c) else acc) #[]
  let codes := codes.qsort (· < ·)
  codes.foldl emit (ByteArray.emptyWithCapacity (25 * codes.size))

end Spec.HeavyBuild
