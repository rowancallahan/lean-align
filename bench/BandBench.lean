import WfaU3
import BandScore

/-!
Benchmark only (unproved IO).  Times the proved banded kernel against the
proved `wfaAlignU3` on windows a seed mapper would score.

    lake exe band_bench [genomeLen] [reads]

Random genome, 100-base reads (3 substitutions; every third read also has a
1-base deletion).  Window sets per read: the true window, the 48 windows
around it (start ±3, length ±3), and 49 random windows.  Every band score is
checked against `wfaAlignU3` (equal when either is ≥ T); a disagreement panics.
-/

open MapSpec AlignmentSpec

def sc0 : Scoring := ⟨0, -4, -6, -2⟩
def T0 : Int := -12
def B0 : Nat := bandOf sc0 T0

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def randGenome (n seed : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut g := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    s := lcg s
    g := g.push (#[65, 67, 71, 84] : Array UInt8)[(s >>> 33) % 4]!
  return g

def slice (g : ByteArray) (a len : Nat) : ByteArray := g.extract a (a + len)

def mutateRead (g : ByteArray) (start seed : Nat) : ByteArray := Id.run do
  let del := seed % 3 == 0
  let mut r := slice g start (if del then 101 else 100)
  let mut s := seed
  if del then
    s := lcg s
    let p := 10 + (s >>> 33) % 80
    r := (r.extract 0 p) ++ (r.extract (p + 1) 101)
  for _ in [0:3] do
    s := lcg s
    let p := (s >>> 33) % 100
    r := r.set! p (if r.get! p == 65 then 67 else 65)
  assert! r.size == 100
  return r

def chars (b : ByteArray) : Array Char := b.toList.toArray.map (fun x => Char.ofNat x.toNat)

def wfaScore (r : Array Char) (g : ByteArray) (w : Window) : Option Int :=
  match wfaAlignU3 sc0 r (chars (slice g w.start w.len)) with
  | some res => some res.2
  | none => none

def timeIt (label : String) (count : Nat) (act : IO Int) : IO Float := do
  let t0 ← IO.monoNanosNow
  let chk ← act
  let t1 ← IO.monoNanosNow
  let secs := Float.ofNat (t1 - t0) / 1e9
  let rate := Float.ofNat count / secs
  IO.println s!"{label}: {count} windows in {secs} s = {rate} windows/s (checksum {chk})"
  return rate

def main (args : List String) : IO UInt32 := do
  let glen := (args[0]?.bind String.toNat?).getD 100000
  let nreads := (args[1]?.bind String.toNat?).getD 200
  assert! B0 == 3
  let g := randGenome glen 42
  let gbs : Array ByteArray := #[g]
  let mut reads : Array (ByteArray × Nat) := #[]
  let mut s := 7
  for i in [0:nreads] do
    s := lcg s
    let st := 10 + (s >>> 33) % (glen - 200)
    reads := reads.push (mutateRead g st (i + 1), st)
  -- window sets
  let mut trueW : Array (Nat × Window) := #[]
  let mut nearW : Array (Nat × Window) := #[]
  let mut randW : Array (Nat × Window) := #[]
  for h : j in [0:reads.size] do
    let (_, st) := reads[j]
    let len := if (j + 1) % 3 == 0 then 101 else 100
    trueW := trueW.push (j, ⟨0, st, len⟩)
    for ds in [0:7] do
      for dl in [0:7] do
        if !(ds == 3 && dl == 3) then nearW := nearW.push (j, ⟨0, st + ds - 3, len + dl - 3⟩)
    for _ in [0:49] do
      s := lcg s
      randW := randW.push (j, ⟨0, (s >>> 33) % (glen - 110), 100⟩)
  let rc := reads.map (fun r => chars r.1)
  let all := trueW ++ nearW ++ randW
  -- correctness: faithful at T on every window
  let mut hitsW := 0
  for (j, w) in all do
    let a := wfaScore rc[j]! g w
    let b := bandScore sc0 T0 B0 reads[j]!.1 gbs w
    let ok := match a, b with
      | some x, some y => (decide (T0 ≤ x) || decide (T0 ≤ y)) → x == y
      | some x, none => x < T0
      | _, _ => false
    if !ok then panic! s!"disagree at read {j} window {repr w}: wfa {a} band {b}"
    if (a.map (fun x => decide (T0 ≤ x))).getD false then hitsW := hitsW + 1
  IO.println s!"checked {all.size} windows, {hitsW} score ≥ T: band = wfa on all"
  -- timing
  for (name, ws) in [("true", trueW), ("near", nearW), ("random", randW)] do
    let wr ← timeIt s!"wfaAlignU3 {name}" ws.size do
      let mut acc : Int := 0
      for (j, w) in ws do
        acc := acc + (wfaScore rc[j]! g w).getD 0
      return acc
    let br ← timeIt s!"bandScore  {name}" ws.size do
      let mut acc : Int := 0
      for (j, w) in ws do
        acc := acc + (bandScore sc0 T0 B0 reads[j]!.1 gbs w).getD 0
      return acc
    IO.println s!"  speedup {br / wr}"
  -- one pass per end: all 7 lengths of each end, for the 49 near/true windows of each read
  let mut ends : Array (Nat × Nat) := #[]
  for h : j in [0:reads.size] do
    let (_, st) := reads[j]
    let len := if (j + 1) % 3 == 0 then 101 else 100
    for de in [0:7] do ends := ends.push (j, st + len + de - 3)
  let er ← timeIt "bandEnd (7 windows per pass)" (7 * ends.size) do
    let mut acc : Int := 0
    for (j, e) in ends do
      match bandEnd sc0 T0 B0 reads[j]!.1 g e with
      | some A => acc := acc + A.foldl (· + ·) 0
      | none => pure ()
    return acc
  IO.println s!"bandEnd window rate {er}"
  return 0
