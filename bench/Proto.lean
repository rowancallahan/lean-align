/-!
Speed prototype only (NOT proved, not part of the tool).  Measures how fast
the planned fast mapper can go before the proofs are written.

    lake exe proto <genome.fa> <reads.txt> <l0> [truth.tsv]

Same answer shape as `mapSpec` with the default scoring and T = -12:
4 seeds of n/4 letters, l0-letter CSR index, full-seed check, banded capped
Gotoh per window start (all ends of one start in one pass), unique best.
-/

def code (b : UInt8) : UInt32 :=
  if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 0

def wordCode (a : ByteArray) (p l0 : Nat) : UInt32 := Id.run do
  let mut h : UInt32 := 0
  for i in [0:l0] do h := h * 4 + code (a.get! (p + i))
  return h

structure Idx where
  l0 : Nat
  offs : Array UInt32
  pos : Array UInt32

def buildIdx (g : ByteArray) (l0 : Nat) : Idx := Id.run do
  let nb := 4 ^ l0
  let nw := g.size + 1 - l0
  let mut cnt : Array UInt32 := Array.replicate (nb + 1) 0
  let mask : UInt32 := (4 ^ l0 - 1).toUInt32
  let mut h : UInt32 := wordCode g 0 (l0 - 1)
  for p in [0:nw] do
    h := (h * 4 + code (g.get! (p + l0 - 1))) &&& mask
    cnt := cnt.modify (h.toNat + 1) (· + 1)
  for b in [0:nb] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let offs := cnt
  let mut fill := cnt
  let mut pos : Array UInt32 := Array.replicate nw 0
  h := wordCode g 0 (l0 - 1)
  for p in [0:nw] do
    h := (h * 4 + code (g.get! (p + l0 - 1))) &&& mask
    let i := fill[h.toNat]!
    pos := pos.set! i.toNat p.toUInt32
    fill := fill.set! h.toNat (i + 1)
  return { l0, offs, pos }

def INF : Nat := 1000

/-- Banded capped Gotoh, penalties (mismatch 4, open 6, extend 2), band ±B
around the main diagonal; read `r` against `g[s ..]`.  Returns the penalty of
ending the window at each length n-B .. n+B (INF when > cap or off genome). -/
def bandScores (r g : ByteArray) (s : Nat) (B cap : Nat) : Array Nat := Id.run do
  let n := r.size
  let W := 2 * B + 1
  -- cell index k ↔ column j = i + k - B
  let mut H : Array Nat := Array.replicate W INF   -- best
  let mut E : Array Nat := Array.replicate W INF   -- gap in read (consume genome)
  let mut F : Array Nat := Array.replicate W INF   -- gap in genome (consume read)
  -- row 0
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
        -- F: from (i-1, j): same j → k+1 in previous row
        let f := if k + 1 < W then min (H[k+1]! + 8) (F[k+1]! + 2) else INF
        -- E: from (i, j-1): k-1 in this row
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

/-- Windows (start, len, penalty) with penalty ≤ cap near anchor `a`. -/
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
  let nseed := 4
  let q := n / nseed
  let B := 3
  let cap := 12
  let mut anchors : Array Int := #[]
  for j in [0:nseed] do
    let h := wordCode r (j * q) idx.l0
    let lo := idx.offs[h.toNat]!.toNat
    let hi := idx.offs[h.toNat + 1]!.toNat
    for t in [lo:hi] do
      let p := idx.pos[t]!.toNat
      -- full seed check
      let mut ok := decide (p + q ≤ g.size)
      if ok then
        for u in [idx.l0:q] do
          if g.get! (p + u) != r.get! (j * q + u) then ok := false; break
      if ok then
        let a : Int := (p : Int) - (j * q : Nat)
        if !(anchors.contains a) then anchors := anchors.push a
  let mut hits : Array (Nat × Nat × Nat) := #[]
  for a in anchors do hits := scoreLocus r g a B cap hits
  -- unique best (smallest penalty), duplicates of the same window allowed
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

def main (args : List String) : IO UInt32 := do
  let gpath :: rpath :: l0s :: rest := args | return 2
  let l0 := l0s.toNat!
  let glines := (← IO.FS.readFile gpath).splitOn "\n"
  let g := glines[1]!.toUTF8
  let rlines := ((← IO.FS.readFile rpath).splitOn "\n").filter (· ≠ "")
  let mut reads : Array ByteArray := #[]
  for i in [0:rlines.length / 2] do reads := reads.push rlines[2*i+1]!.toUTF8
  let t0 ← IO.monoNanosNow
  let idx := buildIdx g l0
  IO.println s!"index entries: {idx.pos.size}"
  let t1 ← IO.monoNanosNow
  let nt := (rest.find? (·.startsWith "-t")).map (·.drop 2 |>.toString.toNat!) |>.getD 1
  let chunk := (reads.size + nt - 1) / nt
  let tasks := (List.range nt).map fun t =>
    Task.spawn (prio := .dedicated) fun _ => (reads.extract (t * chunk) ((t + 1) * chunk)).map (mapRead idx g)
  let res := (tasks.map Task.get).foldl (· ++ ·) #[]
  assert! res.size == reads.size
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped: {mapped}"
  let t2 ← IO.monoNanosNow
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}  map_seconds: {secs}  reads/s: {Float.ofNat reads.size / secs}"
  match rest.filter (!·.startsWith "-t") with
  | tp :: _ =>
    let tl := ((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, r) in tl.zip res.toList do
      match line.splitOn "\t", r with
      | [_, _, pos, _], some (s, _, _) => if pos.toNat! == s + 1 then right := right + 1
      | _, _ => pure ()
    IO.println s!"at_true_position: {right}"
  | [] => pure ()
  return 0
