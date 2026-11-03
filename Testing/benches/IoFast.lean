import Proofs.Sam

/-! # PROTOTYPE, UNPROVED (benchmark module; not wired into `Main.lean`): ByteArray-only FASTQ reading and SAM writing.

Reading (`readChunkFast`): the serial part only scans for record boundaries (counts newlines, remembers where each of `parts`
equal groups of records starts); the groups are then parsed, validated and trimmed in parallel tasks straight from the big
ByteArray blocks (no per-line `extract`, no String for letters/qualities, the QNAME is the only copied header piece).
Writing (`samChunkFast`): every SAM line is appended to one ByteArray per part (numbers written digit by digit, no String,
no `++` of Strings); parts are joined in order. Same checks and same output bytes as `Spec.readChunk` / `Spec.samChunk`
(checked by `io_bench compare`). -/

namespace IoFast
open Spec

structure FRec where
  qname   : ByteArray   -- the FASTQ name up to the first space, without a trailing /1 or /2 (`Spec.mateName`)
  letters : ByteArray   -- after adapter cut, quality window and minimum length
  quality : ByteArray

structure Reader where
  handle : IO.FS.Handle
  buf    : IO.Ref ByteArray
  pos    : IO.Ref Nat
  eof    : IO.Ref Bool

def Reader.ofHandle (h : IO.FS.Handle) : IO Reader :=
  return { handle := h, buf := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef 0, eof := ← IO.mkRef false }

/-- index of the next "\n" at or after `i` (or the buffer size) -/
@[inline] def findNl (b : ByteArray) (i : Nat) : Nat := (findNewlineU b i.toUSize).toNat

/-- Scan from `i`: the position after the `want`-th newline, and how many newlines were found (fewer than `want` at the end of the buffer). -/
partial def scanLines (b : ByteArray) (i : Nat) (want seen : Nat) : Nat × Nat :=
  if seen ≥ want then (i, seen) else
  let j := findNl b i
  if j < b.size then scanLines b (j + 1) want (seen + 1) else (b.size, seen)

/-- The byte offsets (in `r.buf`) at which each of `parts` groups of records starts (plus the end), and the record count of
each group; reads more blocks until `records` records are in the buffer. A last line without "\n" at the end of the file gets one. -/
def Reader.boundaries (r : Reader) (records parts : Nat) : IO (Array Nat × Array Nat) := do
  let mut starts : Array Nat := #[← r.pos.get]
  let mut counts : Array Nat := #[]
  let per := (records + parts - 1) / parts
  let mut got := 0
  repeat
    if got ≥ records then break
    let take := min per (records - got)
    let buf ← r.buf.get
    let (j, seen) := scanLines buf starts.back! (4 * take) 0
    if seen == 4 * take then
      starts := starts.push j; counts := counts.push take; got := got + take
    else if ← r.eof.get then
      if seen % 4 != 0 then throw (IO.userError "FASTQ: file ends inside a record")
      if seen > 0 then
        starts := starts.push j; counts := counts.push (seen / 4)
      break
    else
      let block ← r.handle.read (16 * 1024 * 1024)
      if block.isEmpty then
        r.eof.set true
        if buf.size > 0 && buf.get! (buf.size - 1) != 10 then r.buf.set (buf.push 10)
      else
        let pos ← r.pos.get
        r.buf.set ((buf.extract pos buf.size) ++ block)
        starts := starts.map (· - pos)
        r.pos.set 0
  return (starts, counts)

/-- one line `[i, stop)` with "\r" before the "\n" dropped, and the position after the line -/
@[inline] def nextLine (b : ByteArray) (i : Nat) : Nat × Nat × Nat :=
  let nl := findNl b i
  let stop := if i < nl && b.get! (nl - 1) == 13 then nl - 1 else nl
  (i, stop, nl + 1)

-- every byte of `b` in `[i, hi)` satisfies `p` (specialized tail loop: no closure call per byte)
@[specialize] def allInGo (p : UInt8 → Bool) (b : ByteArray) (hi i : Nat) : Bool :=
  if i < hi then (p (b.get! i) && allInGo p b hi (i + 1)) else true
termination_by hi - i

@[inline] def allIn (b : ByteArray) (lo hi : Nat) (p : UInt8 → Bool) : Bool := allInGo p b hi lo

def trimBytes (letters qual : ByteArray) : ByteArray × ByteArray :=
  let (letters, qual) := AdapterTrim.cutTruSeq letters qual
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  AdapterTrim.dropShort minLength letters qual

def qnameEnd (b : ByteArray) (h0 h1 : Nat) : Nat := Id.run do
  let mut e := h0 + 1
  while e < h1 && b.get! e != 32 do e := e + 1
  if e ≥ h0 + 3 && b.get! (e - 2) == 47 && (b.get! (e - 1) == 49 || b.get! (e - 1) == 50) then e := e - 2
  return e

/-- parse one record at `i`: header, letters, plus, quality lines (all checks of `Spec.parseRecord` and `readChunk`) -/
def parseOne (b : ByteArray) (i : Nat) : Except String (FRec × Nat) :=
  let (h0, h1, p1) := nextLine b i
  let (l0, l1, p2) := nextLine b p1
  let (c0, c1, p3) := nextLine b p2
  let (q0, q1, p4) := nextLine b p3
  if !(h0 < h1 && b.get! h0 == 64 && allIn b h0 h1 fun x => 32 ≤ x && x ≤ 126) then .error "header line is not '@' + printable ASCII"
  else if !(c0 < c1 && b.get! c0 == 43) then .error "third line of a record does not start with '+'"
  else if !allIn b l0 l1 isDnaByte then .error "letters other than A C G T N"
  else if !allIn b q0 q1 fun x => 33 ≤ x && x ≤ 126 then .error "quality outside '!'..'~'"
  else if l1 - l0 != q1 - q0 then .error "sequence and quality lengths differ"
  else
    -- QNAME: header without '@', up to the first space, without a trailing /1 or /2
    let e := qnameEnd b h0 h1
    let nameLen := e - (h0 + 1)
    if !(0 < nameLen && nameLen ≤ 254 && allIn b (h0 + 1) e fun x => (33 ≤ x && x ≤ 63) || (65 ≤ x && x ≤ 126)) then
      .error "read name is not a SAM QNAME"
    else
      let letters := b.extract l0 l1; let qual := b.extract q0 q1
      let (letters, qual) := trimBytes letters qual
      .ok ({ qname := b.extract (h0 + 1) e, letters, quality := qual }, p4)

def parsePart (b1 b2 : ByteArray) (s1 s2 count : Nat) : Except String (Array (FRec × FRec)) := Id.run do
  let mut out := Array.mkEmpty count
  let mut p1 := s1; let mut p2 := s2
  for _ in [0:count] do
    match parseOne b1 p1, parseOne b2 p2 with
    | .ok (r1, n1), .ok (r2, n2) =>
      if r1.qname != r2.qname then return .error "FASTQ files out of step: mate names differ"
      out := out.push (r1, r2); p1 := n1; p2 := n2
    | .error e, _ => return .error e
    | _, .error e => return .error e
  return .ok out

/-- up to `size` pairs; the boundary scan is serial, the parse/validate/trim runs in `parts` tasks -/
def readChunkFast (r1 r2 : Reader) (size parts : Nat) : IO (Array (FRec × FRec)) := do
  let (st1, c1) ← r1.boundaries size parts
  let (st2, c2) ← r2.boundaries size parts
  if c1 != c2 then throw (IO.userError "FASTQ files out of step: one file has more reads than the other")
  let b1 ← r1.buf.get; let b2 ← r2.buf.get
  let tasks := (List.range c1.size).map fun k => Task.spawn fun _ => parsePart b1 b2 st1[k]! st2[k]! c1[k]!
  let mut out : Array (FRec × FRec) := #[]
  for t in tasks do
    match t.get with
    | .ok a => out := out ++ a
    | .error e => throw (IO.userError s!"FASTQ: {e}")
  r1.pos.set st1.back!; r2.pos.set st2.back!
  return out

/-! ## SAM writer -/

def pushNat (b : ByteArray) (n : Nat) : ByteArray :=
  if n < 10 then b.push (48 + n.toUInt8) else (pushNat b (n / 10)).push (48 + (n % 10).toUInt8)

def pushInt (b : ByteArray) (i : Int) : ByteArray :=
  if i < 0 then pushNat (b.push 45) i.natAbs else pushNat b i.toNat

@[inline] def pushStr (b : ByteArray) (s : String) : ByteArray := b ++ s.toUTF8

def pushRevComp (b : ByteArray) (src : ByteArray) (comp : Bool) : ByteArray := Id.run do
  let mut out := b
  for i in [0:src.size] do
    let c := src.get! (src.size - 1 - i)
    out := out.push (if comp then complementByte c else c)
  return out

def tab (b : ByteArray) : ByteArray := b.push 9

def pushSeqQual (b : ByteArray) (r : FRec) (strand : Strand) : ByteArray :=
  if r.letters.isEmpty then (((b.push 42).push 9).push 42) else
  match strand with
  | .forward => (b ++ r.letters).push 9 |> (· ++ r.quality)
  | .reverse => (pushRevComp b r.letters true).push 9 |> (pushRevComp · r.quality false)

def pushTags (b : ByteArray) (answer : PairAnswer) : ByteArray :=
  let b := pushInt (pushStr b "XB:i:") answer.bestPossibleScore
  let b := pushStr (pushStr (b.push 9) "XU:Z:") (uniquenessText answer.uniqueness)
  pushStr (pushStr (b.push 9) "XT:Z:") (tierText answer.tier)

def pushCigar (b : ByteArray) (cigar : Array (Step × Nat)) : ByteArray :=
  cigar.foldl (fun b (s, n) => pushStr (pushNat b n) (stepLetter s)) b

def mappedLineB (b : ByteArray) (names : Array ByteArray) (r : FRec) (which : Mate) (mate other : MateReport)
    (answer : PairAnswer) : ByteArray :=
  let flag := flagPaired + flagProperPair + mateFlag which +
    reverseFlag mate.placement.strand flagReverse + reverseFlag other.placement.strand flagMateReverse
  let rname := names.getD mate.placement.chromosome "*".toUTF8
  let rnext := if mate.placement.chromosome = other.placement.chromosome then "=".toUTF8 else names.getD other.placement.chromosome "*".toUTF8
  let left := min mate.placement.start other.placement.start
  let right := max mate.placement.stop other.placement.stop
  let leftmost := mate.placement.start < other.placement.start ||
    (mate.placement.start = other.placement.start && which = .one)
  let tlen : Int := if leftmost then right - left else -((right - left : Nat) : Int)
  let b := tab (pushNat (tab (b ++ r.qname)) flag) -- qname \t flag \t
  let b := tab (b ++ rname)
  let b := tab (pushNat b (mate.placement.start + 1))
  let b := tab (pushNat b (mapq answer))
  let b := tab (pushCigar b mate.cigar)
  let b := tab (b ++ rnext)
  let b := tab (pushNat b (other.placement.start + 1))
  let b := tab (pushInt b tlen)
  let b := tab (pushSeqQual b r mate.placement.strand)
  let b := tab (pushInt (pushStr b "AS:i:") mate.score)
  (pushTags b answer).push 10

def unmappedLineB (b : ByteArray) (r : FRec) (which : Mate) (tags : ByteArray → ByteArray) : ByteArray :=
  let flag := flagPaired + flagUnmapped + flagMateUnmapped + mateFlag which
  let b := tab (pushNat (tab (b ++ r.qname)) flag)
  let b := pushStr b "*\t0\t0\t*\t*\t0\t0\t"
  let b := tab (pushSeqQual b r .forward)
  (tags b).push 10

def samLinesB (b : ByteArray) (names : Array ByteArray) (r1 r2 : FRec) (result : PairResult) : ByteArray :=
  match result with
  | .trimmedAway mate =>
      let tags := fun b => pushStr b s!"XT:Z:trimmedAway{if mate = .one then 1 else 2}"
      unmappedLineB (unmappedLineB b r1 .one tags) r2 .two tags
  | .aligned answer =>
      match answer.found with
      | some pair =>
          mappedLineB (mappedLineB b names r1 .one pair.mate1 pair.mate2 answer) names r2 .two pair.mate2 pair.mate1 answer
      | none =>
          unmappedLineB (unmappedLineB b r1 .one (pushTags · answer)) r2 .two (pushTags · answer)

def samChunkFast (chromosomes : ChromosomeList) (chunk : Array (FRec × FRec)) (results : List PairResult) (parts : Nat) : ByteArray :=
  let names := chromosomes.map (·.1.toUTF8)
  let pairs := chunk.zip results.toArray
  let size := (pairs.size + parts - 1) / parts
  let tasks := (List.range parts).map fun part => Task.spawn fun _ =>
    (pairs.extract (part * size) ((part + 1) * size)).foldl (init := ByteArray.emptyWithCapacity (size * 800))
      fun b ((r1, r2), result) => samLinesB b names r1 r2 result
  tasks.foldl (fun bytes task => bytes ++ task.get) ByteArray.empty

end IoFast
