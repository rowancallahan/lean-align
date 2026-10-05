import FastGenK250
import ParMap

/-!
Microbenchmark (unproved IO): word kernels (pool/mapper/MapperK250.lean) vs the byte
kernels they equal, on candidate windows of simulated reads.

    lake exe k250_bench <genome.fa (one chromosome)> <mate.reads.txt> <truth.tsv> [mate column 1|2]
    lake exe k250_bench pair <genome.fa> <mate1.reads.txt> <mate2.reads.txt> [dump.tsv]
      env K_T=P (16), K_OLD=1 (also run pairFastGB and compare), K_TASKS (1)

Windows per read: `true` = at the read's true place (strand from the truth), `rand` =
at a random place; each with the same length and the one-gap shapes `(a, b)`,
`|a|, |b| ≤ 5`.  Every word result is asserted equal to the byte result.
-/

open MapSpec MapSpec.Fast

def readLines (p : String) : IO (Array String) := do
  return ((← IO.FS.readFile p).splitOn "\n").toArray.filter (· ≠ "")

def readFa (p : String) : IO ByteArray := do
  let ls ← readLines p
  return ls.foldl (fun b l => if l.startsWith ">" then b else b ++ l.toUTF8) ByteArray.empty

@[inline] def rnd (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13); let x := x ^^^ (x >>> 7); x ^^^ (x <<< 17)

structure Job where
  R : ByteArray
  K : RP
  st : Nat
  len : Nat
deriving Inhabited

def timeIt (label : String) (n : Nat) (f : Nat → Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let r ← (← IO.mkRef (f t0)).get
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {Float.ofNat (t1 - t0) / Float.ofNat n} ns/window  (sum {r})"
  return r

def run (name : String) (G : ByteArray) (P : PGen) (js : Array Job) (lim : Nat) : IO Unit := do
  IO.println s!"{name}: {js.size} windows, lim {lim}"
  let a ← timeIt "kerG  (bytes)" js.size fun t => js.foldl (fun s j => s + kerG j.R G j.st j.len (if t == 1 then 0 else lim)) 0
  let b ← timeIt "kerGK (words)" js.size fun t => js.foldl (fun s j => s + kerGK j.R j.K G P j.st j.len (if t == 1 then 0 else lim)) 0
  for j in js do
    let x := kerG j.R G j.st j.len lim
    let y := kerGK j.R j.K G P j.st j.len lim
    if x != y then
      throw (IO.userError s!"MISMATCH st {j.st} len {j.len} n {j.R.size} lim {lim}: bytes {x} words {y}")
  assert! a == b

def showHit (h : Placement × Int) : String :=
  s!"{h.1.1.chr}\t{h.1.1.start}\t{h.1.1.len}\t{h.2}\t{if h.1.2 == Strand.rev then "-" else "+"}"

def secs (t0 t1 : Nat) : Float := Float.ofNat (t1 - t0) / 1e9

/-- End to end: `pairFastGBK` (and `pairFastGB` with `K_OLD=1`), hashed index over the
concatenated genome. -/
def pairMain (gpath p1 p2 : String) (dump : Option String) : IO UInt32 := do
  let gbs := ((← readLines gpath).foldl (fun (acc : Array ByteArray) l =>
    if l.startsWith ">" then acc.push ByteArray.empty else acc.modify (acc.size - 1) (· ++ l.toUTF8)) #[])
  let pvs := gbs.map pack
  assert! (pvs.zip gbs).all fun (P, g) => checkPG P g
  let rd (p : String) : IO (Array String × Array ByteArray) := do
    let ls ← readLines p
    return ((Array.range (ls.size / 2)).map (fun i => ls[2 * i]!.drop 1 |>.toString),
            (Array.range (ls.size / 2)).map fun i => ls[2 * i + 1]!.toUTF8)
  let (names, r1) ← rd p1
  let (_, r2) ← rd p2
  assert! r1.size == r2.size
  let P := ((← IO.getEnv "K_T").getD "16").toNat!
  let tasks := ((← IO.getEnv "K_TASKS").getD "1").toNat!
  let G := gbs.foldl (· ++ ·) ByteArray.empty
  let offs := (gbs.foldl (fun (o, n) g => (o.push n, n + g.size)) ((#[] : Array Nat), 0)).1
  assert! catOk G offs gbs
  let ix := buildIdx G
  assert! checkAll #[ix] #[G]
  IO.println s!"genome: {gbs.size} chromosomes, {G.size} letters; packed copy checked (checkPG); index checked; T = -{P}"
  let ps := (Array.range r1.size).map fun i => (r1[i]!, r2[i]!)
  let go (name : String) (f : ByteArray × ByteArray → Option ((Placement × Int) × (Placement × Int))) :
      IO (Array (Option ((Placement × Int) × (Placement × Int)))) := do
    let t0 ← IO.monoNanosNow
    let out ← (← IO.mkRef (if t0 == 1 then #[] else if tasks ≤ 1 then ps.map f else ParMap.parMap tasks f ps)).get
    let t1 ← IO.monoNanosNow
    IO.println s!"{name}: pairs {ps.size}  kept {(out.filter (·.isSome)).size}  map_seconds {secs t0 t1}  pairs/s {Float.ofNat ps.size / secs t0 t1}"
    return out
  let outK ← go "pairFastGBK (word kernels)" fun p => pairFastGBK P 100 1000 ix G offs gbs pvs p.1 p.2
  if (← IO.getEnv "K_F").isSome then
    -- the parameterized search with the byte kernel (closure overhead only)
    let mF (R : ByteArray) : Option (Placement × Int) :=
      if fastT P R then decodeP gbs.size P (mapChromsGBF (kerH R (gbs ++ gbs)) (kerH (revCompB R) (gbs ++ gbs)) P ix G offs gbs R (revCompB R))
      else none
    let _ ← go "mapChromsGBF + kerH (bytes)" fun p => match mF p.1, mF p.2 with
      | some a, some b => if properPair 100 1000 a.1 b.1 then some (a, b) else none
      | _, _ => none
  if (← IO.getEnv "K_OLD").isSome then
    let outO ← go "pairFastGB  (byte kernels)" fun p => pairFastGB P 100 1000 ix G offs gbs p.1 p.2
    assert! outO == outK
    IO.println "outputs identical"
  if let some dp := dump then
    IO.FS.writeFile dp (String.join ((names.zip outK).toList.map fun (nm, x) => match x with
      | some (a, b) => s!"{nm}\t{showHit a}\t{showHit b}\n"
      | none => s!"{nm}\tnone\n"))
  return 0

/-- Per-read preparation costs. -/
def prepMain (p1 : String) : IO UInt32 := do
  let ls ← readLines p1
  let rs := (Array.range (ls.size / 2)).map fun i => ls[2 * i + 1]!.toUTF8
  let _ ← timeIt "revCompB" rs.size fun t => rs.foldl (fun s R => s + (revCompB (if t == 1 then ByteArray.empty else R)).size) 0
  let _ ← timeIt "revCompK" rs.size fun t => rs.foldl (fun s R => s + (revCompK (if t == 1 then ByteArray.empty else R)).size) 0
  let _ ← timeIt "packRP" rs.size fun t => rs.foldl (fun s R => s + (packRP (if t == 1 then ByteArray.empty else R)).w.size) 0
  let _ ← timeIt "seed hashes (prepG-like)" rs.size fun t => rs.foldl (fun s R =>
    let m := R.size / 25
    s + ((Array.range m).map fun j => seedHashAt (if t == 1 then ByteArray.empty else R) (j * (R.size / m))).size) 0
  for R in rs do
    assert! revCompK R == revCompB R
  return 0

def main (args : List String) : IO UInt32 := do
  if let "prep" :: p1 :: _ := args then
    return ← prepMain p1
  if let "pair" :: gpath :: p1 :: p2 :: rest := args then
    return ← pairMain gpath p1 p2 rest.head?
  let gpath :: rpath :: tpath :: rest := args | throw (IO.userError "usage: k250_bench <genome.fa> <reads> <truth> [1|2]")
  let col := match rest with | "2" :: _ => 2 | _ => 1
  let G ← readFa gpath
  let P := pack G
  assert! checkPG P G
  let rl ← readLines rpath
  let tl := (← readLines tpath).extract 1 1000000000
  let n := rl.size / 2
  assert! tl.size == n
  let mut sameT := #[]
  let mut shapeT := #[]
  let mut sameR := #[]
  let mut shapeR := #[]
  let mut x : UInt64 := 88172645463325252
  for i in [0:n] do
    let R0 := rl[2 * i + 1]!.toUTF8
    let f := (tl[i]!.splitOn "\t").toArray
    let pos := f[if col == 1 then 2 else 4]!.toNat! - 1
    let R := if f[if col == 1 then 3 else 5]! == "-" then revCompB R0 else R0
    let K := packRP R
    let m := R.size
    x := rnd x
    let pr := (x >>> 11).toNat % (G.size - m - 20) + 10
    for _ in [0:5] do
      sameT := sameT.push ⟨R, K, pos, m⟩
    sameR := sameR.push ⟨R, K, pr, m⟩
    for a in [0:11] do
      for b in [0:11] do
        if a != 5 || b != 5 then
          shapeT := shapeT.push ⟨R, K, pos + 5 - a, m + a + b - 10⟩
          shapeR := shapeR.push ⟨R, K, pr + 5 - a, m + a + b - 10⟩
  -- one window, many times (hot cache)
  let j := sameT[0]!
  let reps := 200000
  let _ ← timeIt "hot kerG  same length" reps fun t => (List.range reps).foldl (fun s i => s + kerG j.R G j.st j.len (if t == 1 then i else 15)) 0
  let _ ← timeIt "hot kerGK same length" reps fun t => (List.range reps).foldl (fun s i => s + kerGK j.R j.K G P j.st j.len (if t == 1 then i else 15)) 0
  let _ ← timeIt "hot hamming bytes" reps fun t => (List.range reps).foldl (fun s i => s + hamming j.R G j.st (if t == 1 then i else 3) 0 j.R.size 0) 0
  let _ ← timeIt "hot hamA words" reps fun t => (List.range reps).foldl (fun s i => s + hamA j.K.w P.w (P.o + j.st) (if t == 1 then i else 3) j.R.size) 0
  let gbs := #[G]
  let pvs := #[P]
  for (nm, js) in [("true, same length (5x per read, warm)", sameT), ("random, same length", sameR),
      ("true, one-gap shapes", shapeT), ("random, one-gap shapes", shapeR)] do
    IO.println s!"{nm}: {js.size} windows, penalty 16"
    let a ← timeIt "ker16  (bytes, band)" js.size fun t => js.foldl (fun s j => s + ker16 j.R gbs (if t == 1 then 1 else 0) j.st j.len) 0
    let b ← timeIt "ker16K (words, closed form)" js.size fun t => js.foldl (fun s j => s + ker16K j.R j.K gbs pvs (if t == 1 then 1 else 0) j.st j.len) 0
    assert! a == b
  for lim in [15, 12] do
    run "true, same length (5x per read, warm)" G P sameT lim
    run "random, same length" G P sameR lim
    run "true, one-gap shapes" G P shapeT lim
    run "random, one-gap shapes" G P shapeR lim
  IO.println "all word results equal the byte results"
  return 0
