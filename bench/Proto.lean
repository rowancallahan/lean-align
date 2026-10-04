/-!
Speed prototype only (NOT proved, not part of the tool).  Measures how fast
the planned fast mapper can go before the proofs are written.

    lake exe proto <genome.fa> <reads.txt> <l0> [truth.tsv|-] [dump.tsv]

Same answer as `mapSpec` with scoring (0, -4, -6, -2) and T = -12, i.e.
penalty cap 12 (mismatch 4, gap of length L costs 6 + 2L).  Why each step is exact:

* Cap 12 < 16 = two gaps, so a hit window has at most one gap, of length
  L ≤ 3 (6 + 2·3 = 12), and L = |len - n|.
* Seeds: 4 seeds of q = n/4 letters; a hit window has ≤ 3 edits, so one seed
  is aligned without edits (proved: `exists_clean_seed`).  The index is
  `LookupComplete` for ACGT words (reads must be ACGT), the full q-letter
  seed is then checked, so every hit window has an anchor a = p - j·q.
* Shape: the one gap is before or after the clean seed, so a hit window is
  (a, n) (no gap), (a, n+e) (gap after the seed) or (a+s, n-s) (gap before),
  0 < |e|, |s| ≤ 3: 13 windows per anchor.
* Same-length window: any gapped alignment needs ≥ 2 gaps (≥ 16), so its
  penalty is 4·(mismatches) when ≤ 12.
* Other window, L = |len - n|: penalty = 6 + 2L + 4·m, m = fewest mismatches
  over the gap position, prefix on the start diagonal, suffix on the end one.
* Gapped windows cost ≥ 8, so when the best same-length window costs ≤ 4 they
  cannot tie or beat it and are not scored.
-/

def cap : Nat := 12

def code (b : UInt8) : UInt32 :=
  if b == 65 then 0 else if b == 67 then 1 else if b == 71 then 2 else if b == 84 then 3 else 4

def wordCode (a : ByteArray) (p l0 : Nat) : UInt32 := Id.run do
  let mut h : UInt32 := 0
  for i in [0:l0] do
    let c := code (a.get! (p + i))
    assert! c < 4
    h := h * 4 + c
  return h

structure Idx where
  l0 : Nat
  offs : Array UInt32
  pos : Array UInt32

/-- CSR index of every ACGT-only l0-word (words with other letters can never
equal an ACGT read word). -/
def buildIdx (g : ByteArray) (l0 : Nat) : Idx := Id.run do
  let nb := 4 ^ l0
  let mask : UInt32 := (4 ^ l0 - 1).toUInt32
  let mut cnt : Array UInt32 := Array.replicate (nb + 1) 0
  let mut h : UInt32 := 0
  let mut good := 0          -- ACGT letters in a row ending at p
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then h := (h * 4 + c) &&& mask; good := good + 1 else good := 0
    if good ≥ l0 then cnt := cnt.modify (h.toNat + 1) (· + 1)
  for b in [0:nb] do cnt := cnt.set! (b + 1) (cnt[b + 1]! + cnt[b]!)
  let mut fill := cnt
  let mut pos : Array UInt32 := Array.replicate cnt[nb]!.toNat 0
  h := 0; good := 0
  for p in [0:g.size] do
    let c := code (g.get! p)
    if c < 4 then h := (h * 4 + c) &&& mask; good := good + 1 else good := 0
    if good ≥ l0 then
      let i := fill[h.toNat]!
      pos := pos.set! i.toNat (p + 1 - l0).toUInt32
      fill := fill.set! h.toNat (i + 1)
  return { l0, offs := cnt, pos }

/-- Mismatches of `r` against `g[a ..]`, stopping once above `lim`. -/
def hamming (r g : ByteArray) (a lim : Nat) : Nat := Id.run do
  let mut m := 0
  for i in [0:r.size] do
    if r.get! i != g.get! (a + i) then
      m := m + 1
      if m > lim then return m
  return m

/-- Penalty of window (st, len), len ≠ n, |len - n| ≤ 3, if ≤ `lim`; else lim + 1. -/
def gappedPen (r g : ByteArray) (st len lim : Nat) : Nat := Id.run do
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then return lim + 1
  let mmax := (lim - 6 - 2 * L) / 4
  let skip := if len < n then L else 0
  -- read r < i ↔ g[st + r];  read r ≥ i + skip ↔ g[st + r + len - n]
  let mut suf := 0
  for k in [skip:n] do
    if r.get! k != g.get! (st + len + k - n) then suf := suf + 1
  let mut pre := 0
  let mut best := pre + suf
  for i in [0:n - skip] do
    if r.get! i != g.get! (st + i) then pre := pre + 1
    if pre > mmax then break
    if r.get! (i + skip) != g.get! (st + len + i + skip - n) then suf := suf - 1
    best := min best (pre + suf)
  if best > mmax then return lim + 1
  return 6 + 2 * L + 4 * best

structure Best where
  pen : Nat := cap + 1
  st : Nat := 0
  len : Nat := 0
  amb : Bool := false

@[inline] def Best.add (b : Best) (st len pen : Nat) : Best :=
  if pen < b.pen then { pen, st, len, amb := false }
  else if pen == b.pen && (st != b.st || len != b.len) then { b with amb := true }
  else b

def mapRead (idx : Idx) (g r : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  let n := r.size
  let q := n / 4
  assert! idx.l0 ≤ q
  let mut anchors : Array Int := #[]
  for j in [0:4] do
    let h := wordCode r (j * q) idx.l0
    for t in [idx.offs[h.toNat]!.toNat:idx.offs[h.toNat + 1]!.toNat] do
      let p := idx.pos[t]!.toNat
      if p + q ≤ g.size then
        let mut ok := true
        for u in [idx.l0:q] do
          if g.get! (p + u) != r.get! (j * q + u) then ok := false; break
        if ok then
          let a : Int := (p : Int) - (j * q : Nat)
          if !(anchors.contains a) then anchors := anchors.push a
  let mut b : Best := {}
  for a in anchors do
    if a ≥ 0 && a.toNat + n ≤ g.size then
      let m := hamming r g a.toNat 3
      if m ≤ 3 then b := b.add a.toNat n (4 * m)
  if b.pen ≥ 8 then
    for a in anchors do
      for L in [1:4] do
        -- (a, n ± L): gap after the seed; (a ∓ L, n ± L): gap before it
        for (s, len) in [((0 : Int), n + L), (0, n - L), (-(L : Int), n + L), ((L : Int), n - L)] do
          let st := a + s
          if st ≥ 0 && st.toNat + len ≤ g.size then
            let lim := min b.pen cap
            b := b.add st.toNat len (gappedPen r g st.toNat len lim)
  if b.pen ≤ cap && !b.amb then return some (b.st, b.len, b.pen)
  return none

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
  let mut res : Array (Option (Nat × Nat × Nat)) := #[]
  for r in reads do res := res.push (mapRead idx g r)
  let mapped := (res.filter (·.isSome)).size
  IO.println s!"mapped: {mapped}"
  let t2 ← IO.monoNanosNow
  let secs := Float.ofNat (t2 - t1) / 1e9
  IO.println s!"index_seconds: {Float.ofNat (t1 - t0) / 1e9}  map_seconds: {secs}  reads/s: {Float.ofNat reads.size / secs}"
  match rest with
  | [_, dp] =>
    let names := (List.range (rlines.length / 2)).map fun i => (rlines[2*i]!.drop 1).toString
    IO.FS.writeFile dp (String.join ((names.zip res.toList).map fun (nm, x) => match x with
      | some (s, l, p) => s!"{nm}\t{s}\t{l}\t{-(Int.ofNat p)}\n"
      | none => s!"{nm}\tnone\n"))
  | _ => pure ()
  match rest with
  | tp :: _ =>
    if tp == "-" then return 0
    let tl := ((← IO.FS.readFile tp).splitOn "\n").filter (· ≠ "") |>.drop 1
    let mut right := 0
    for (line, r) in tl.zip res.toList do
      match line.splitOn "\t", r with
      | [_, _, pos, _], some (s, _, _) => if pos.toNat! == s + 1 then right := right + 1
      | _, _ => pure ()
    IO.println s!"at_true_position: {right}"
  | [] => pure ()
  return 0
