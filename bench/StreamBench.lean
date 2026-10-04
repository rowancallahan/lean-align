import ParStream

/-!
Benchmark only (prints to stdout; not part of the tool).  Writer overlapped
with mapping (`ParMap.streamTasks`) against map-everything-then-write
(`ParMap.parMap`).

    lake exe stream_bench <stream|whole> <workers> <items> <steps> <batch> <out-file>

Per item: `steps` xorshift rounds (CPU only), then one ~100-byte line.
`stream`: tasks in input order, writer waits for each and writes its text.
`whole`: map + format every item with `parMap`, join, write once.
-/

open ParMap

def peakRssMB : IO Nat := do
  let st ← IO.FS.readFile "/proc/self/status"
  let line := ((st.splitOn "\n").find? (·.startsWith "VmHWM:")).get!
  return ((line.splitOn " ").filter (· ≠ "")).getD 1 "0" |>.toNat! |> (· / 1024)

def cpu (steps : Nat) (i : Nat) : Nat × UInt64 := Id.run do
  let mut h : UInt64 := i.toUInt64 * 0x9E3779B97F4A7C15 + 1
  for _ in [0:steps] do
    h := h ^^^ (h <<< 13); h := h ^^^ (h >>> 7); h := h ^^^ (h <<< 17)
  return (i, h)

def fmt (r : Nat × UInt64) : String :=
  let v := r.2
  s!"{r.1}\t{v}\t{v * 3}\t{v * 7}\t{v * 11}\t{v * 13}\n"

/-- Write the texts in order; each task is dropped once written. -/
def writeAll (h : IO.FS.Handle) : List (Task String) → Nat → IO Nat
  | [], n => pure n
  | t :: ts, n => do
    let s := t.get
    h.putStr s
    writeAll h ts (n + s.utf8ByteSize)

def main (args : List String) : IO UInt32 := do
  let [mode, ws, ns, ss, bs, out] := args | IO.eprintln "usage: see bench/StreamBench.lean"; return 2
  let w := ws.toNat!; let steps := ss.toNat!; let b := bs.toNat!
  let xs := Array.range ns.toNat!
  let t0 ← IO.monoNanosNow
  let h ← IO.FS.Handle.mk out .write
  let mut bytes := 0
  if mode == "stream" then
    bytes ← writeAll h (streamTasks w b (cpu steps) fmt xs).toList 0
  else
    assert! mode == "whole"
    let s := String.join (parMap w (fun x => fmt (cpu steps x)) xs).toList
    h.putStr s
    bytes := s.utf8ByteSize
  h.flush
  let t1 ← IO.monoNanosNow
  IO.println s!"{mode} workers {w} items {xs.size} batch {b}: seconds {Float.ofNat (t1 - t0) / 1.0e9}  bytes {bytes}  peak_rss_MB {← peakRssMB}"
  return 0
