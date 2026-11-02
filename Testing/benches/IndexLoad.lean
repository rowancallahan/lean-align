import Proofs.Aligner

/-! Benchmark only (unproved IO): ways to read the index file into one `ByteArray`.
   index_load whole INDEX            IO.FS.readBinFile (what Spec/Shim.lean does)
   index_load chunks INDEX MB        Handle.read in MB-sized pieces appended into a presized array
   index_load parts INDEX P          INDEX.part0 .. part{P-1} read by P tasks, then appended
   index_load split INDEX P          writes INDEX.part0 .. part{P-1}
   index_load sizes INDEX            the parts of the loaded index and their sizes
Each mode prints the load time and a checksum (one byte per 4 KB page, so every page is touched). -/

def ms (t0 t1 : Nat) : Float := (t1 - t0).toFloat / 1e6

def touch (b : ByteArray) : Nat := Id.run do
  let mut s := 0
  let mut i := 0
  while i < b.size do
    s := s + b[i]!.toNat
    i := i + 4096
  return s

def readParts (path : String) (p : Nat) : IO ByteArray := do
  let tasks ← (List.range p).mapM fun i => IO.asTask (IO.FS.readBinFile s!"{path}.part{i}")
  let parts ← tasks.mapM fun t => IO.ofExcept t.get
  let total := parts.foldl (· + ·.size) 0
  return parts.foldl (· ++ ·) (ByteArray.emptyWithCapacity total)

def main (args : List String) : IO Unit := do
  match args with
  | ["whole", path] =>
    let t0 ← IO.monoNanosNow
    let b ← IO.FS.readBinFile path
    let t1 ← IO.monoNanosNow
    IO.println s!"whole: read {ms t0 t1} ms, size {b.size}, touch {touch b}, total {ms t0 (← IO.monoNanosNow)} ms"
  | ["chunks", path, mb] =>
    let t0 ← IO.monoNanosNow
    let size := (← System.FilePath.metadata path).byteSize.toNat
    let h ← IO.FS.Handle.mk path .read
    let c := mb.toNat! * 1024 * 1024
    let mut acc := ByteArray.emptyWithCapacity size
    repeat
      let piece ← h.read c.toUSize
      if piece.isEmpty then break
      acc := acc ++ piece
    let t1 ← IO.monoNanosNow
    IO.println s!"chunks {mb} MB: read {ms t0 t1} ms, size {acc.size}, touch {touch acc}, total {ms t0 (← IO.monoNanosNow)} ms"
  | ["parts", path, p] =>
    let t0 ← IO.monoNanosNow
    let b ← readParts path p.toNat!
    let t1 ← IO.monoNanosNow
    IO.println s!"parts {p}: read {ms t0 t1} ms, size {b.size}, touch {touch b}, total {ms t0 (← IO.monoNanosNow)} ms"
  | ["split", path, p] =>
    let b ← IO.FS.readBinFile path
    let n := p.toNat!
    let q := (b.size + n - 1) / n
    for i in [0:n] do
      IO.FS.writeBinFile s!"{path}.part{i}" (b.extract (i * q) (min b.size ((i + 1) * q)))
  | ["sizes", path] =>
    let b ← IO.FS.readBinFile path
    match Spec.loadIndex b with
    | none => IO.println "not a router index"
    | some (ix, G, offs, ns) =>
      IO.println s!"file {b.size}; genome G.w {G.w.size} (n {G.n}), G.ex {G.ex.size}; slots ix.sl {ix.sl.size} (sw {ix.sw}, {ix.sl.size / ix.sw} slots), bucket offsets {4 * (2 ^ ix.B + 1)} (B {ix.B}); k {ix.k} w {ix.w} c {ix.c} T {ix.T}; runs {ix.runs.size}; chromosomes {offs.size} {ns.size}"
      let nSlots := (MapSpec.Mz.rd4 ix.offs (4 * (ix.ob + 2 ^ ix.B))).toNat
      IO.println s!"genome bytes from {G.o}: {(G.n + 3) / 4}; slots {nSlots} x {ix.sw} B = {nSlots * ix.sw}; bucket offsets from byte {4 * ix.ob}: {4 * (2 ^ ix.B + 1)}"
  | _ => IO.println "usage: see the module comment"
