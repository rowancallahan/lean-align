import MzIndex

/-!
Randomized test of the proved minimizer index (NOT a proof; the theorems are
in `codecs/MzIndex.lean`): genomes with N runs and IUPAC letters, every seed
of the genome and mutated seeds, `lookupSeed` against a naive scan, and
`check` = true on the builder's output.

    lake exe mz_test [rounds]
-/

open MapSpec.Mz

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def letters : ByteArray := "ACGTACGTACGTACGTNRM".toUTF8

/-- Random genome: mostly ACGT (small alphabet runs so repeats occur), runs of N, odd letters. -/
def genome (seed n : Nat) : ByteArray := Id.run do
  let mut g := ByteArray.emptyWithCapacity n
  let mut x := seed
  while g.size < n do
    x := lcg x
    let r := (x >>> 33) % 1000
    if r < 3 then
      for _ in [0:(x >>> 20) % 60 + 1] do g := g.push 78       -- N run
    else if r < 6 then g := g.push (if r == 3 then 82 else 77) -- R / M
    else if r < 40 then
      -- copy an earlier stretch (repeat)
      let len := (x >>> 12) % 80 + 25
      if g.size > len then
        let st := (x >>> 40) % (g.size - len)
        for i in [0:len] do g := g.push (g.get! (st + i))
    else g := g.push (letters.get! ((x >>> 50) % 4))
  return g.extract 0 n

def naive (G R : ByteArray) (s : Nat) : Array Nat :=
  (Array.range (G.size + 1 - q)).filter fun p => p + q ≤ G.size && eqRun G R p s q

def main (args : List String) : IO UInt32 := do
  let rounds := (args.headD "20").toNat!
  let mut seeds := 0
  let mut hits := 0
  for r in [0:rounds] do
    let n := 2000 + 997 * r
    let G := genome (r + 1) n
    let k := [19, 21, 22, 23][r % 4]!
    let B := [16, 17, 18][r % 3]!
    -- context letters per side: all of w - 1 = 25 - k, or fewer (genome-checked offsets)
    let c := (25 - k) - (r / 4) % (26 - k)
    -- bytes per slot: the key is cut to what fits (`kf < kb`: k-word checked in the genome)
    let sw := [8, 4, 5, 6, 8][r % 5]!
    let c := if 8 * sw < 15 + 4 * c + 1 then 0 else c
    -- mod-minimizer t-words (t = k: plain minimizer)
    let t := k - (26 - k) * (r % (k / (26 - k)))
    let ix := buildW G k B c sw t
    if !check ix G then
      IO.eprintln s!"round {r}: check failed (k {k}, B {B}, c {c}, sw {sw}, t {t}, kf {ix.kf}): params {checkParams ix} sound {checkSound ix G (2 ^ ix.B) 0} comp {checkComp ix G ix.offs 0 (G.size + 1 - q) 0} runs {checkRuns ix G ix.nr 0} cover {checkCover ix G 0 G.size 0} nr {ix.nr} runs {ix.runs.toList.take 12}"
      return 1
    let mut x := r + 7
    for p in [0:G.size + 1 - q] do
      -- the genome's own seed at p, and a mutated copy
      let R0 := G.extract p (p + q)
      x := lcg x
      let R1 := R0.set! ((x >>> 30) % q) (letters.get! ((x >>> 40) % letters.size))
      let R2 := (ByteArray.mk #[65, 67]) ++ R0  -- seed at offset 2
      for (R, s) in [(R0, 0), (R1, 0), (R2, 2)] do
        let got := lookupSeed ix G R s
        let want := naive G R s
        seeds := seeds + 1
        hits := hits + got.size
        if got != want then
          IO.eprintln s!"round {r} p {p}: lookup {got.toList.take 10} naive {want.toList.take 10}"
          return 1
  IO.println s!"ok: {rounds} genomes, {seeds} seeds, {hits} hits, lookupSeed = naive scan, check = true"
  return 0
