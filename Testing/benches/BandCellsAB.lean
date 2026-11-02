import TierHeur
/-! `bandDPg true` (`bandCellsJ`, skipped cells jumped over) = `bandDPg false` (`bandCells`,
every diagonal of every row visited) on random cases; exits 1 on the first difference.
  lake build bandcells_ab && .lake/build/bin/bandcells_ab [cases=200000] -/
open TierHeur

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def pick (s : UInt64) (n : Nat) : Nat := ((s >>> 33).toNat) % n

def letters : ByteArray := ⟨#[65, 67, 71, 84, 78]⟩

-- a random read, and a window: the read with substitutions / insertions / deletions, random flanks
def gen (s0 : UInt64) : UInt64 × ByteArray × ByteArray × Int × Nat × Nat := Id.run do
  let mut s := lcg s0
  let n := pick s 180
  s := lcg s
  let mut X := ByteArray.empty
  for _ in [0:n] do
    s := lcg s
    X := X.push (letters.get! (if pick s 100 == 0 then 4 else pick s 4))
  s := lcg s
  let fl := pick s 30
  s := lcg s
  let rate := pick s 30
  let mut W := ByteArray.empty
  for _ in [0:fl] do
    s := lcg s
    W := W.push (letters.get! (pick s 4))
  for i in [0:n] do
    s := lcg s
    let r := pick s 1000
    if r < rate then W := W.push (letters.get! (pick (lcg s) 4))            -- substitution
    else if r < rate + rate / 4 then pure ()                               -- deletion
    else if r < rate + rate / 2 then W := (W.push X[i]!).push (letters.get! (pick (lcg s) 4))  -- insertion
    else W := W.push X[i]!
  s := lcg s
  for _ in [0:pick s 30] do
    s := lcg s
    W := W.push (letters.get! (pick s 4))
  s := lcg s
  let off : Int := (fl : Int) + ((pick s 21 : Nat) : Int) - 10
  s := lcg s
  let w := pick s 20
  s := lcg s
  let lim := match pick s 4 with
    | 0 => pick (lcg s) 40
    | 1 => pick (lcg s) 200
    | 2 => 1000000
    | _ => pick (lcg s) 9000000
  return (lcg s, X, W, off, w, lim)

def main (args : List String) : IO UInt32 := do
  let N := (args.headD "200000").toNat!
  let mut s : UInt64 := 12345
  let mut some_ := 0
  for c in [0:N] do
    let (s', X, W, off, w, lim) := gen s
    s := s'
    let a := bandDPg false X W off w lim
    let b := bandDPg true X W off w lim
    if a.isSome then some_ := some_ + 1
    if a != b then
      IO.println s!"DIFF case {c}: n {X.size} m {W.size} s0 {off} w {w} lim {lim}"
      return 1
  IO.println s!"bandDPg true = bandDPg false on {N} cases ({some_} with an alignment)"
  return 0
