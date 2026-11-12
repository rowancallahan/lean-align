# The shim, line by line (for Rowan)

`Spec/Shim.lean` is the only unproved code between the files and the proved aligner. It does three things:
read FASTQ bytes, call `alignPairs`, write SAM bytes. Everything clever (alignment, trimming) is proved elsewhere;
the shim's job is plumbing, and the risks in plumbing are **order**, **completeness**, **errors** and **memory**.

## Five Lean IO ideas you need

| Lean | Meaning | Analogy |
|---|---|---|
| `IO α` | a program that, when run, touches the outside world and returns an `α` | a recipe, not the meal |
| `let x ← act` | run `act` now, call its result `x` | cook the recipe, keep the meal |
| `let x := e` | a pure value (no outside world); computed when needed | arithmetic |
| `IO.asTask act` | start `act` on another thread NOW; give back a ticket (`Task (Except IO.Error α)`) | order food, get a receipt |
| `t.get` | wait until the ticket's task has finished and take its result (`.ok v` or `.error e`) | wait at the counter |
| `IO.ofExcept r` | turn `.ok v` into `v`, or rethrow `.error e` (stop the program with that error) | open the bag; complain if wrong |

Two consequences:
- A task's error does not stop the program by itself. It is stored in the ticket and only surfaces at
  `IO.ofExcept ticket.get`. So **every ticket must be cashed in** somewhere, or an error is silently lost.
- `Task.spawn` (used inside `trimChunk`, `samChunk`, `alignPairs`) is the pure version: same idea, no IO, cannot fail.
  In proofs `(Task.spawn f).get = f ()`, which is why the parallel helpers are proved equal to plain maps.

## The current `map` loop (festive), step by step

```lean
let index ← IO.FS.readBinFile indexPath                 -- whole index into memory (TRUSTED: it is buildIndex of the genome)
let chromosomes ← Spec.readChromosomeList (...)          -- names + lengths for the SAM header
let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk reads1Path .read)
let reads2 ← ...                                         -- two buffered readers (4 MB blocks)
let out ← IO.FS.Handle.mk outPath .write
for line in Spec.samHeader chromosomes do out.putStrLn line
let mut next ← IO.asTask (do                             -- ticket: read + trim chunk 1 in the background
  let raw ← Spec.readChunk reads1 reads2 20000
  return Spec.trimChunk raw 16)
let mut writing : Task ... := .pure (.ok ())             -- ticket of the last write; starts as "already done"
repeat
  let chunk ← IO.ofExcept next.get                       -- wait for the read; a FASTQ error stops here
  if chunk.isEmpty then break                            -- end of input
  next ← IO.asTask (do ... readChunk ... trimChunk ...)  -- start reading chunk k+1 NOW (overlaps alignment)
  let results := Spec.alignPairs insertSettings index (Spec.chunkPairs chunk)   -- THE PROVED PART
  let text := Spec.samChunk chromosomes chunk results 16 -- SAM bytes of this chunk (16 pure tasks)
  let previous := writing
  writing ← IO.asTask (do IO.ofExcept previous.get; out.write text)  -- write after the previous write
IO.ofExcept writing.get                                  -- wait for the last write; a write error stops here
```

Why each guarantee holds:
- **Order.** Chunks are read in file order (one reader, one chunk at a time). Each write task first waits for
  the previous write (`previous.get`), so chunk k is written after chunk k-1. Inside a chunk, `alignPairs` and
  `samChunk` keep pair order (proved for `alignPairs`; `samChunk` joins its parts in order).
- **Completeness.** The loop stops only when `readChunk` returns an empty chunk (end of both files). The final
  `writing.get` makes the program wait for the last write before exiting.
- **Errors.** Read errors surface at `IO.ofExcept next.get`; write errors are passed down the chain
  (`IO.ofExcept previous.get` rethrows inside the next write task) and surface at the final `IO.ofExcept writing.get`.
- **Memory.** At most: the chunk being aligned, the next chunk being read, and the text being written.

Where cores sit idle: the main thread itself computes `results` (waits for all 16 align tasks) and `text`
(waits for all 16 format tasks) before it can start aligning the next chunk. Two waits per chunk.

## The proposed overlap change (tested in a scratch copy, not applied)

```lean
let mut writing : Task ... := .pure (.ok ())
let mut older   : Task ... := .pure (.ok ())             -- NEW: ticket of the write before the last one
repeat
  let chunk ← IO.ofExcept next.get
  if chunk.isEmpty then break
  next ← IO.asTask (do ... readChunk ... trimChunk ...)
  IO.ofExcept older.get                                  -- NEW: at most 2 chunks in flight (memory bound)
  older := writing
  let previous := writing
  writing ← IO.asTask (prio := .dedicated) (do           -- align + format + write, all in one background task
    let results := Spec.alignPairs insertSettings index (Spec.chunkPairs chunk)   -- THE PROVED PART (unchanged)
    let text := Spec.samChunk chromosomes chunk results 16
    IO.ofExcept previous.get                             -- still: write only after the previous chunk's write
    out.write text)
IO.ofExcept writing.get
```

What changes: the main thread no longer waits for alignment or formatting. It immediately goes on to the next
chunk, so chunk k+1 aligns while chunk k finishes. The guarantees:
- **Order:** unchanged argument (each write waits for the previous write).
- **Completeness and errors:** unchanged; additionally `older.get` rethrows an earlier write error sooner.
- **Memory:** bounded by `older`: before starting chunk k, chunk k-2 must be fully written, so at most two
  chunks are aligned/formatted at once (plus one being read).
- **`prio := .dedicated`:** the task waits on its own sub-tasks; a dedicated thread means it never occupies a
  slot of Lean's shared worker pool while waiting.

## What is trusted (not proved) today
1. `readBinFile` returns the file's bytes; the index file is `buildIndex` of the genome (`hIndex`).
2. `readChunk` returns the next records of both files in order (the byte-spec drafts in `byte_specs/` are the plan).
3. The ticket chain preserves order and propagates errors (the argument above; provable later as an ordered-merge lemma).
4. `out.write` writes the given bytes.
