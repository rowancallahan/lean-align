import Proofs.SamFused
import Proofs.TrimCore
import FastqIO

/-! # The streaming mapper behind `mapInit` / `mapStep` (Spec/MapFiles.lean)

The two files arrive in chunks. Each file's bytes are kept in a carry and cut after every `4 · jobPairs`-th newline,
without parsing (a record of a valid file is exactly four newline-terminated lines, `FQ.toBytes`). Slice k of file 1
and slice k of file 2 make job k. A job is mapped by `job` (parse both slices, pair the mates by QNAME, cut and trim
them, align, write the SAM lines) in its own pure `Task.spawn`. The state keeps the jobs' tasks in order; a step hands
back the lines of the oldest jobs while more than `inFlight` are pending, so the cores keep working while the next
chunks are read. The end (`none`) maps what is left over (the carries, as one last job) and hands back every job's
lines. Any job that fails makes the run fail.

Everything executed works on `ByteArray`s; the list-based spec is reached by proofs: `parseFastqB_eq` (parsing),
`qnameB_eq` / `qnameOf_eq` (QNAME), `Spec.Trim.trimB_eq` (cut and trim), `samChunkS_eq` (SAM lines),
`alignPairsP_eq` (the aligner's setup made once per job). -/

namespace Spec.MapFast
open Spec

/-! ## One job: a slice of each file → its SAM lines -/

-- `prepPairs` on bytes: the same number of reads, the same valid QNAME for both mates, then cut and trimmed
def prepPairsB (r1 r2 : Array ReadB) : Option (Array (ReadB × ReadB)) :=
  if r1.size == r2.size && (r1.zip r2).all (fun (a, b) => let q := qnameB a.name; q == qnameB b.name && qnameOkB q) then
    some ((r1.zip r2).map fun (a, b) =>
      let t1 := TrimCore.trimB a.seq a.qual
      let t2 := TrimCore.trimB b.seq b.qual
      ({ a with seq := t1.1, qual := t1.2 }, { b with seq := t2.1, qual := t2.2 }))
  else none

-- `mateLetters` on bytes
def mateLettersB (pair : ReadB × ReadB) : Option ByteArray × Option ByteArray :=
  (if pair.1.seq.isEmpty then none else some pair.1.seq, if pair.2.seq.isEmpty then none else some pair.2.seq)

-- one job: a slice of each file → the SAM lines of its pairs, or none if the slices are not valid, matching FASTQ.
-- The aligner's setup is made inside the job, by the thread that runs it (shared across threads, every reference
-- count on it would be atomic: +6% CPU); once per job of `jobPairs` pairs it costs under 1%.
def job (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) (s1 s2 : ByteArray) :
    Option ByteArray :=
  match parseFastqB s1, parseFastqB s2 with
  | .ok r1, .ok r2 =>
    (prepPairsB r1 r2).map fun pairs =>
      samChunkS chrs pairs (alignPairsP settings (chunkSetup settings index) (pairs.toList.map mateLettersB))
  | _, _ => none

/-! ## The stream -/

-- the pairs per job, and the jobs kept pending at once. Small jobs and a deep window: the loop blocks on the oldest job
-- only while more than `inFlight` are pending, so the oldest may run ~(inFlight - cores) median job times before the
-- workers run dry (head-of-line); 32 jobs of 4000 pairs hold about as much as 8 of 16000
def jobPairs : Nat := 4000
def inFlight : Nat := 32

-- one past the first `n` newlines at or after `i`, and how many were found (fewer than `n`: up to the end)
def advance (b : ByteArray) : (n i : Nat) → Nat × Nat
  | 0, i => (i, 0)
  | n + 1, i =>
    let j := findNewline b i
    if j < b.size then let (p, k) := advance b n (j + 1); (p, k + 1) else (b.size, 0)

-- one file's bytes not yet in a job: `carry`, of which the first `scan` bytes hold `lines` newlines
structure Carry where
  carry : ByteArray
  scan  : Nat
  lines : Nat

-- the complete slices (each `4 · jobPairs` lines) of `carry ++ chunk`, and what is left
def cutSlices (c : Carry) (chunk : ByteArray) : Carry × Array ByteArray :=
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
  let carry := carry ++ chunk
  go (carry.size + 1) carry scan lines #[]

-- the bytes buffered per file before they are cut in a background task
def flushBytes : Nat := 8 * 1024 * 1024

-- buffered chunks, joined (one copy)
def join (b : Array ByteArray) : ByteArray := b.foldl (· ++ ·) ByteArray.empty

-- the newline cutting runs off the loop thread: per file, the last cut (a task: its carry, and the slices it cut),
-- and the chunks received since it was started; the loop thread only buffers chunks, starts a cut every
-- `flushBytes`, pairs the slices of finished cuts and spawns the jobs
structure State where
  job     : ByteArray → ByteArray → Option ByteArray
  cut1    : Task (Carry × Array ByteArray)
  cut2    : Task (Carry × Array ByteArray)
  buf1    : Array ByteArray
  buf2    : Array ByteArray
  size1   : Nat
  size2   : Nat
  -- slices of finished cuts of one file waiting for the other file's
  queue1  : Array ByteArray
  queue2  : Array ByteArray
  pending : Array (Task (Option ByteArray))

-- the lines of the oldest pending jobs while more than `keep` are pending, appended to `out`
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

-- a job for each slice of `queue1` that has its slice in `queue2`, in order
def spawnPaired (job : ByteArray → ByteArray → Option ByteArray) (queue1 queue2 : Array ByteArray)
    (pending : Array (Task (Option ByteArray))) : Array (Task (Option ByteArray)) :=
  (List.range (min queue1.size queue2.size)).foldl (fun pending k =>
    let a := queue1[k]!
    let b := queue2[k]!
    pending.push (Task.spawn fun _ => job a b)) pending

def init (job : ByteArray → ByteArray → Option ByteArray) : State :=
  ⟨job, Task.pure (⟨ByteArray.empty, 0, 0⟩, #[]), Task.pure (⟨ByteArray.empty, 0, 0⟩, #[]), #[], #[], 0, 0, #[], #[], #[]⟩

-- one file's chunk: buffered; once `flushBytes` are buffered, the previous cut's slices go to the queue and the
-- buffered bytes are cut after the previous cut's carry, in a task of their own
def feed (cut : Task (Carry × Array ByteArray)) (buf : Array ByteArray) (size : Nat) (queue : Array ByteArray)
    (chunk : ByteArray) : Task (Carry × Array ByteArray) × Array ByteArray × Nat × Array ByteArray :=
  let buf := buf.push chunk
  let size := size + chunk.size
  if flushBytes ≤ size then
    (cut.map (prio := .dedicated) (fun (c, _) => cutSlices c (join buf)), #[], 0, queue ++ cut.get.2)
  else (cut, buf, size, queue)

-- the next chunk of each file: buffer it (and start a cut), start the jobs of the paired slices, hand back the
-- oldest jobs' lines; `none` (both files ended): cut what is left, map the leftover as one last job and hand back
-- every job's lines
def step (st : State) : Option (ByteArray × ByteArray) → Option (State × ByteArray)
  | some (chunk1, chunk2) =>
    let ⟨job, cut1, cut2, buf1, buf2, size1, size2, queue1, queue2, pending⟩ := st
    let (cut1, buf1, size1, queue1) := feed cut1 buf1 size1 queue1 chunk1
    let (cut2, buf2, size2, queue2) := feed cut2 buf2 size2 queue2 chunk2
    let n := min queue1.size queue2.size
    (collect inFlight (spawnPaired job queue1 queue2 pending) ByteArray.empty).map fun (pending, out) =>
      (⟨job, cut1, cut2, buf1, buf2, size1, size2, queue1.extract n queue1.size, queue2.extract n queue2.size,
        pending⟩, out)
  | none =>
    let ⟨job, cut1, cut2, buf1, buf2, _, _, queue1, queue2, pending⟩ := st
    let last1 := cutSlices cut1.get.1 (join buf1)
    let last2 := cutSlices cut2.get.1 (join buf2)
    let queue1 := queue1 ++ cut1.get.2 ++ last1.2
    let queue2 := queue2 ++ cut2.get.2 ++ last2.2
    let n := min queue1.size queue2.size
    let paired := spawnPaired job queue1 queue2 pending
    -- what is left over: the unpaired slices and the carries, as one last job
    let rest1 := (queue1.extract n queue1.size).foldl (· ++ ·) ByteArray.empty ++ last1.1.carry
    let rest2 := (queue2.extract n queue2.size).foldl (· ++ ·) ByteArray.empty ++ last2.1.carry
    let all := if rest1.isEmpty && rest2.isEmpty then paired else paired.push (Task.spawn fun _ => job rest1 rest2)
    (collect 0 all ByteArray.empty).map fun (_, out) => (init job, out)

end Spec.MapFast
