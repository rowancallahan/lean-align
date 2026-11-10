import Proofs.Draft.Sam
import FastqIO
import ReadTrim
import AdapterTrim

/-! # The streaming mapper behind `mapStart` / `mapStep` / `mapEnd` (Spec/Draft/MapFiles.lean)

The two files arrive as blocks. Each file's bytes are kept in a carry and cut after every `4 · jobPairs`-th
newline, without parsing (a record of a valid file is exactly four newline-terminated lines, `FQ.toBytes`). Slice k
of file 1 and slice k of file 2 make job k. A job is mapped by `job` (parse both slices, pair the mates by QNAME, cut
and trim them, align, write the SAM lines) in its own pure `Task.spawn`. The state keeps the jobs' tasks in order;
a step hands back the results of the oldest jobs while more than `inFlight` are pending, and `finish` maps what is
left over (the carries, as one last job) and hands back every result. Any job that fails makes the run fail.

Everything executed works on `ByteArray`s; the list-based spec is reached by proofs (`parseFastqB_eq`, and the
equalities of `job` with one job of `mapFiles`). -/

namespace Spec.MapFast
open Spec

/-! ## One job: a slice of each file → its SAM lines -/

-- the adapter cut, the quality window, the minimum length (the proved trimmer pieces)
def trimB (letters qual : ByteArray) : ByteArray × ByteArray :=
  let (letters, qual) := AdapterTrim.cutTruSeq letters qual
  let (letters, qual) := match ReadTrim.trimRead letters qual with
    | some (s, e) => (letters.extract s e, qual.extract s e)
    | none => (ByteArray.empty, ByteArray.empty)
  AdapterTrim.dropShort 25 letters qual

def trimReadB (r : ReadB) : ReadB :=
  let t := trimB r.seq r.qual
  { r with seq := t.1, qual := t.2 }

-- the first space at or after `i` (or the end)
def spaceAt (b : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | f + 1, i => if i < b.size && b[i]! != 32 then spaceAt b f (i + 1) else i

-- `SamSpec.qname` on bytes: the name up to the first space, without a trailing "/1" or "/2"
def qnameB (name : ByteArray) : ByteArray :=
  let e := spaceAt name name.size 0
  if 2 ≤ e && name[e - 2]! == 47 && (name[e - 1]! == 49 || name[e - 1]! == 50) then name.extract 0 (e - 2)
  else name.extract 0 e

-- `SamSpec.qnameOk` on bytes
def qnameOkB (q : ByteArray) : Bool :=
  0 < q.size && q.size ≤ 254 && allBytes (fun c => (33 ≤ c && c ≤ 63) || (65 ≤ c && c ≤ 126)) q

-- `prepPairs` on bytes: the same number of reads, the same valid QNAME for both mates, then cut and trimmed
def prepPairsB (r1 r2 : Array ReadB) : Option (Array (ReadB × ReadB)) :=
  if r1.size == r2.size && (r1.zip r2).all (fun (a, b) => let q := qnameB a.name; q == qnameB b.name && qnameOkB q) then
    some ((r1.zip r2).map fun (a, b) => (trimReadB a, trimReadB b))
  else none

-- `mateLetters` on bytes
def mateLettersB (pair : ReadB × ReadB) : Option ByteArray × Option ByteArray :=
  (if pair.1.seq.isEmpty then none else some pair.1.seq, if pair.2.seq.isEmpty then none else some pair.2.seq)

/-! ### The SAM lines as bytes (`SamSpec.mateLine` field by field) -/

-- the decimal digits of `n`, appended to `b`
def pushNat (b : ByteArray) (n : Nat) : ByteArray :=
  if h : n < 10 then b.push (48 + n.toUInt8) else (pushNat b (n / 10)).push (48 + (n % 10).toUInt8)
termination_by n
decreasing_by omega

-- `toString i` appended to `b`
def pushInt (b : ByteArray) (i : Int) : ByteArray :=
  if i < 0 then pushNat (b.push 45) i.natAbs else pushNat b i.toNat

-- `complement` on one byte: A <-> T, C <-> G, everything else unchanged
def complementByte (b : UInt8) : UInt8 :=
  if b == 65 then 84 else if b == 84 then 65 else if b == 67 then 71 else if b == 71 then 67 else b

-- the bytes of `src` in reverse order, each through `f`, appended to `out` (by `uget`)
def pushRevMap (f : UInt8 → UInt8) (src out : ByteArray) (i : USize) (h : i.toNat ≤ src.size) : ByteArray :=
  if h0 : i = 0 then out
  else
    have hj : (i - 1).toNat = i.toNat - 1 := toNat_sub1 i h0
    have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
    pushRevMap f src (out.push (f (src.uget (i - 1) (by omega)))) (i - 1) (by omega)
termination_by i.toNat
decreasing_by
  have hi : i.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [toNat_sub1 i h0]; omega

-- `src` reversed, each byte through `f`, appended to `b`
def pushRev (f : UInt8 → UInt8) (b src : ByteArray) : ByteArray :=
  if h : src.size < 4294967296 then pushRevMap f src b src.usize (usize_le src)
  else b ++ ⟨(src.data.toList.map f).reverse.toArray⟩

def chrNameB (chrs : ChromosomeList) (i : Nat) : ByteArray :=
  match chrs[i]? with
  | some (name, _) => name.toUTF8
  | none => "*".toUTF8

def letterOf : Step → UInt8
  | .diag => 77
  | .gapY => 73
  | .gapX => 68

def pushCigar (b : ByteArray) (cigar : Array (Step × Nat)) : ByteArray :=
  cigar.foldl (fun b (step, n) => (pushInt b n).push (letterOf step)) b

def uniquenessText : Uniqueness → String
  | .unique            => "unique"
  | .multimapper       => "multimapper"
  | .unknown           => "unknown"
  | .repetitiveUnknown => "repetitiveUnknown"

-- `SamSpec.tags`, each preceded by a tab
def pushTags (b : ByteArray) (result : PairResult) (p : Option (MateReport × MateReport)) : ByteArray :=
  let b := match p with
    | none => b
    | some (me, _) => (b.push 9) ++ s!"AS:i:{me.score}".toUTF8
  match result with
  | .trimmedAway .one => (b.push 9) ++ "XT:Z:trimmedAway1".toUTF8
  | .trimmedAway .two => (b.push 9) ++ "XT:Z:trimmedAway2".toUTF8
  | .aligned a =>
    ((b.push 9) ++ s!"XB:i:{a.bestPossibleScore}".toUTF8).push 9 ++ s!"XU:Z:{uniquenessText a.uniqueness}".toUTF8

-- `SamSpec.mateLine` appended to `b`
def mateLineB (b : ByteArray) (chrs : ChromosomeList) (r : ReadB) (which : Mate) (result : PairResult) : ByteArray :=
  let p := SamSpec.placed which result
  let b := pushNat ((b ++ qnameB r.name).push 9) (SamSpec.flag which p)
  let b := (b.push 9) ++ (match p with | none => "*".toUTF8 | some (me, _) => chrNameB chrs me.placement.chromosome)
  let b := pushNat (b.push 9) (SamSpec.pos p)
  let b := pushNat (b.push 9) (SamSpec.mapq result p)
  let b := match p with
    | none => (b.push 9).push 42
    | some (me, _) => pushCigar (b.push 9) me.cigar
  let b := (b.push 9) ++ (match p with
    | none => "*".toUTF8
    | some (me, other) =>
      if me.placement.chromosome = other.placement.chromosome then "=".toUTF8
      else chrNameB chrs other.placement.chromosome)
  let b := pushNat (b.push 9) (SamSpec.pnext p)
  let b := pushInt (b.push 9) (SamSpec.tlen which p)
  let b := b.push 9
  let b :=
    if r.seq.isEmpty then ((b.push 42).push 9).push 42
    else match SamSpec.strand p with
      | .forward => ((b ++ r.seq).push 9) ++ r.qual
      | .reverse => pushRev id ((pushRev complementByte b r.seq).push 9) r.qual
  (pushTags b result p).push 10

-- `SamSpec.body` for one job, appended to `b`
def bodyB (chrs : ChromosomeList) (pairs : Array (ReadB × ReadB)) (results : List PairResult) : ByteArray :=
  (pairs.zip results.toArray).foldl (init := ByteArray.empty)
    fun b ((r1, r2), result) => mateLineB (mateLineB b chrs r1 .one result) chrs r2 .two result

-- one job: a slice of each file → the SAM lines of its pairs, or none if the slices are not valid, matching FASTQ
def job (settings : InsertSettings) (setup : AlignSetup) (chrs : ChromosomeList) (s1 s2 : ByteArray) :
    Option ByteArray :=
  match parseFastqB s1, parseFastqB s2 with
  | .ok r1, .ok r2 =>
    (prepPairsB r1 r2).map fun pairs =>
      bodyB chrs pairs (alignPairsP settings setup (pairs.toList.map mateLettersB))
  | _, _ => none

/-! ## The stream -/

-- the pairs per job, and the jobs kept running at once
def jobPairs : Nat := 16000
def inFlight : Nat := 8

-- one past the first `n` newlines at or after `i`, and how many were found (fewer than `n`: up to the end)
def advance (b : ByteArray) : (n i : Nat) → Nat × Nat
  | 0, i => (i, 0)
  | n + 1, i =>
    let j := findNewline b i
    if j < b.size then let (p, k) := advance b n (j + 1); (p, k + 1) else (b.size, 0)

-- one file's bytes not yet in a job: `carry`, of which `scan` bytes hold `lines` newlines
structure Carry where
  carry : ByteArray
  scan  : Nat
  lines : Nat

-- the complete slices (each `4 · jobPairs` lines) in `c.carry ++ block`, and what is left
def cutSlices (c : Carry) (block : ByteArray) : Carry × Array ByteArray :=
  let need := 4 * jobPairs
  let rec go (fuel : Nat) (carry : ByteArray) (scan lines : Nat) (out : Array ByteArray) : Carry × Array ByteArray :=
    match fuel with
    | 0 => (⟨carry, scan, lines⟩, out)
    | fuel + 1 =>
      let (p, k) := advance carry (need - lines) scan
      if lines + k = need then
        go fuel (carry.extract p carry.size) 0 0 (out.push (carry.extract 0 p))
      else (⟨carry, carry.size, lines + k⟩, out)
  let ⟨carry, scan, lines⟩ := c
  let carry := carry ++ block
  go (carry.size + 1) carry scan lines #[]

structure State where
  job     : ByteArray → ByteArray → Option ByteArray
  file1   : Carry
  file2   : Carry
  -- complete slices of one file waiting for the other file's
  queue1  : Array ByteArray
  queue2  : Array ByteArray
  pending : Array (Task (Option ByteArray))

-- the results of the oldest pending jobs while more than `keep` are pending, appended to `out`
def collect (keep : Nat) (pending : Array (Task (Option ByteArray))) (out : ByteArray) :
    Option (Array (Task (Option ByteArray)) × ByteArray) :=
  let rec go (fuel : Nat) (i : Nat) (out : ByteArray) : Option (Nat × ByteArray) :=
    match fuel with
    | 0 => some (i, out)
    | fuel + 1 =>
      if keep < pending.size - i then
        match (pending[i]!).get with
        | some piece => go fuel (i + 1) (out ++ piece)
        | none => none
      else some (i, out)
  (go pending.size 0 out).map fun (i, out) => (pending.extract i pending.size, out)

def start (job : ByteArray → ByteArray → Option ByteArray) (header : ByteArray) : State × ByteArray :=
  (⟨job, ⟨ByteArray.empty, 0, 0⟩, ⟨ByteArray.empty, 0, 0⟩, #[], #[], #[]⟩, header)

def step (st : State) (block1 block2 : ByteArray) : Option (State × ByteArray) :=
  let ⟨job, file1, file2, queue1, queue2, pending⟩ := st
  let (file1, s1) := cutSlices file1 block1
  let (file2, s2) := cutSlices file2 block2
  let queue1 := queue1 ++ s1
  let queue2 := queue2 ++ s2
  let n := min queue1.size queue2.size
  let spawned := (List.range n).foldl (fun pending k =>
    let a := queue1[k]!
    let b := queue2[k]!
    pending.push (Task.spawn fun _ => job a b)) pending
  (collect inFlight spawned ByteArray.empty).map fun (pending, out) =>
    (⟨job, file1, file2, queue1.extract n queue1.size, queue2.extract n queue2.size, pending⟩, out)

def finish (st : State) : Option ByteArray :=
  let n := min st.queue1.size st.queue2.size
  let job := st.job
  let paired := (List.range n).foldl (fun pending k =>
    let a := st.queue1[k]!
    let b := st.queue2[k]!
    pending.push (Task.spawn fun _ => job a b)) st.pending
  -- what is left over: the unpaired slices and the carries, as one last job
  let rest1 := (st.queue1.extract n st.queue1.size).foldl (· ++ ·) ByteArray.empty ++ st.file1.carry
  let rest2 := (st.queue2.extract n st.queue2.size).foldl (· ++ ·) ByteArray.empty ++ st.file2.carry
  let all := if rest1.isEmpty && rest2.isEmpty then paired else paired.push (Task.spawn fun _ => job rest1 rest2)
  (collect 0 all ByteArray.empty).map (·.2)

end Spec.MapFast
