import CsrIndex

/-!
CSR index benchmark (IO, unproved).

    lake exe csr_bench <genome.fa> <l0> <index.csr>

Reads the FASTA into a `ByteGenome`, builds the index, saves it, loads it
back, compares, runs the proved checker (`checkIndex`), and checks that a
corrupted index is rejected.  Prints times, file size and peak RSS.
-/

open MapSpec

def readFasta (path : String) : IO ByteGenome := do
  let raw ← IO.FS.readBinFile path
  let mut gb : ByteGenome := #[]
  let mut name := ""
  let mut cur := ByteArray.emptyWithCapacity raw.size
  let mut i := 0
  while i < raw.size do
    let b := raw.get! i
    if b == 62 then  -- '>'
      if name != "" then gb := gb.push { name, bytes := cur }
      let mut j := i + 1
      while raw.get! j != 10 do j := j + 1
      name := String.fromUTF8! (raw.extract (i + 1) j)
      cur := ByteArray.emptyWithCapacity (raw.size - j)
      i := j + 1
    else
      if b != 10 then cur := cur.push b
      i := i + 1
  assert! name != ""
  return gb.push { name, bytes := cur }

def u64 (v : Nat) : ByteArray := Id.run do
  let mut B := ByteArray.empty
  for k in [0:8] do B := B.push (v >>> (8 * k)).toUInt8
  return B

def rd64 (B : ByteArray) (o : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:8] do v := v + (B.get! (o + k)).toNat <<< (8 * k)
  return v

/-- Layout: "CSR1", l0, #chromosomes, starts…, |offs|, |pos| (all LE u64), offs, pos. -/
def saveIndex (path : String) (idx : CsrIndex) : IO Unit := do
  IO.FS.withFile path .write fun h => do
    h.write "CSR1".toUTF8
    h.write (u64 idx.l0)
    h.write (u64 idx.starts.size)
    for s in idx.starts do h.write (u64 s)
    h.write (u64 idx.offs.size)
    h.write (u64 idx.pos.size)
    h.write idx.offs
    h.write idx.pos

def loadIndex (path : String) : IO CsrIndex := do
  let B ← IO.FS.readBinFile path
  assert! B.extract 0 4 == "CSR1".toUTF8
  let l0 := rd64 B 4
  let n := rd64 B 12
  let starts := (Array.range n).map fun c => rd64 B (20 + 8 * c)
  let o := 20 + 8 * n
  let no := rd64 B o
  let np := rd64 B (o + 8)
  let o := o + 16
  assert! B.size == o + no + np
  return { l0, starts, offs := B.extract o (o + no), pos := B.extract (o + no) (o + no + np) }

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

def peakRssMb : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  let l := (s.splitOn "\n").filter (·.startsWith "VmHWM") |>.head!
  return l

/-- Runs `f` after reading the clock; `f` gets the time so it cannot be hoisted. -/
def timed (label : String) (f : Nat → α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← IO.mkRef (f t0)   -- the value is computed before this call
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}_s: {secs t0 t1}"
  r.get

def main (args : List String) : IO UInt32 := do
  let [gpath, l0s, ipath] := args | throw (IO.userError "usage: csr_bench <genome.fa> <l0> <index.csr>")
  let l0 := l0s.toNat!
  let t0 ← IO.monoNanosNow
  let gb ← readFasta gpath
  let t1 ← IO.monoNanosNow
  IO.println s!"chromosomes: {gb.size}  letters: {gb.foldl (· + ·.bytes.size) 0}  read_s: {secs t0 t1}"
  let idx ← timed "build" fun t => buildCsr (if t == 1 then 0 else l0) gb
  IO.println s!"entries: {idx.pos.size / 4}"
  let t2 ← IO.monoNanosNow
  saveIndex ipath idx
  let t3 ← IO.monoNanosNow
  let fsize := (← System.FilePath.metadata ipath).byteSize
  IO.println s!"save_s: {secs t2 t3}  file_bytes: {fsize}"
  let idx2 ← loadIndex ipath
  let t4 ← IO.monoNanosNow
  IO.println s!"load_s: {secs t3 t4}"
  let same ← timed "compare" fun t => idx2.l0 == idx.l0 + (if t == 1 then 1 else 0) &&
    idx2.starts == idx.starts && idx2.offs == idx.offs && idx2.pos == idx.pos
  assert! same
  let ok ← timed "check" fun t => checkIndex (if t == 1 then idx else idx2) gb
  IO.println s!"check: {ok}"
  assert! ok
  -- a corrupted index must be rejected: entry 0 overwritten by entry 1
  let bad := { idx2 with pos := setU32 idx2.pos 0 (getU32 idx2.pos 1) }
  let okBad ← timed "check_corrupted" fun t => checkIndex (if t == 1 then idx else bad) gb
  IO.println s!"corrupted check: {okBad}"
  assert! !okBad
  IO.println (← peakRssMb)
  return 0
