# Why CPU utilization is low, and what fixes it (S-G, 2026-11-03)

Box: 4 cores, 15 GB. Index: heavy.idx (new format). Builds: festive-fermi b85bbf7, plus local experiments that
are not pushed. Utilization = (user + sys − load CPU) / (map wall × 4). Index load is measured inside the run
(`timed_load.py`). SAM goes to /dev/null, except for the comparison runs.

## 1. Plain files vs zcat → FIFO (festive b85bbf7)
| set | plain: map wall, util | FIFO: map wall, util | zcat CPU (both streams) |
|---|---|---|---|
| NovaSeq 200k ×5 (nova1M) | 33.7–34.0 s, 0.88–0.89 | 35.2–36.4 s, 0.83–0.84 | 4.8 s |
| hg002_1M (HiSeq 2×250) | 36.9–37.2 s, 0.88 | 44.0–44.1 s, 0.75 | 9.8 s |
Our own CPU is the same either way. The FIFO only adds idle time. minibwa could not be built here (permission policy).
shim_overlap.patch: no gain (map wall within noise; util 0.88–0.90 in both builds; SAM identical).

## 2. Cause (per-chunk timestamps, local instrumented Main.lean; 50 chunks of 20k pairs, hg002_1M)
The shim pipelines two stages: one reader task (`readChunk` + `trimChunk`) and the main loop (`alignPairs` then
`samChunk`). A round lasts max(reader, main).
| input | read | trim | align | samChunk | main waits for reader (median) | main idle total | span |
|---|---|---|---|---|---|---|---|
| plain | 552 ms | 116 | 515 | 139 | 33 ms | 1.9 s | 36.0 s |
| FIFO | 758 ms | 85 | 515 | 133 | 165 ms | 9.3 s | 43.5 s |
- `readChunk` is single-threaded and costs about as much as aligning the chunk on the other cores, so the stages are
  balanced, and every hiccup idles the cores. That is the ~0.89 on plain files.
- With two FIFOs the reader alternates between mates. While it drains one pipe, the other pipe fills (64 KB) and
  its zcat stops, so the two decompressors run in turn and the reader waits on each one. strace: 13,786 `read`
  calls, ~25 s blocked, against 78 on plain files. sys CPU doubles (12 → 30 s). That is the 0.75 (S-D: 0.60–0.73
  at 5M).

## 3. Fixes measured (1 rep each, SAM byte-identical to festive on both sets)
| build | nova1M plain | nova1M FIFO | hg002_1M plain | hg002_1M FIFO |
|---|---|---|---|---|
| festive b85bbf7 | 33.3–35.8 s, 0.89 | 34.6–37.2 s, 0.83–0.84 | 37.2–39.2 s, 0.87–0.89 | 43.9–44.3 s, 0.75 |
| + reader read-ahead (reader_readahead.patch) | 33.4 s, 0.89 | 34.7 s, 0.86 | 35.1 s, 0.90 | **38.6 s, 0.84** |
| + read-ahead + shim_speed.patch | 32.3 s, 0.89 | 31.2 s, 0.85 | 33.1 s, 0.90 | **39.3 s, 0.83** |
- Read-ahead: each `FastqReader` reads its next 4 MB block in a dedicated task while the current one is parsed,
  and a short pipe read is topped up to 4 MB. Both decompressors keep flowing. With the instrumented build on
  hg002_1M FIFO, read per chunk fell 684 → 528 ms and main idle 6.4 → 0.9 s.
- shim_speed.patch lowers the reader's (and SAM's) CPU: read 552 → 478 ms per chunk on plain files.
- Tried and not enough on its own: topping up short reads without read-ahead (FIFO main idle 6.4 → 5.2 s).
- The box is noisy (±2 s between series), so these are single reps.

## 4. What is left, and how to keep all cores busy
- After read-ahead, the main loop is serial: `alignPairs` (parallel), then `samChunk` (parallel inside, but main
  waits for it), then hand-off. The reader is still one task, roughly equal to `alignPairs`, so the balance is tight.
- Next structural steps (not done):
  (a) Parse in parallel. Split the 4 MB blocks into record ranges, parse + validate + trim per range in tasks. The
      reader then only does I/O and finds the record boundaries.
  (b) Overlap `samChunk` of chunk k with `alignPairs` of chunk k+1 (format in a task, like the writer).
  (c) A deeper read-ahead (2 chunks) only absorbs jitter.
- Lean pool facts (step 2 of the plan) and parTasks / persistent-pool experiments (step 3) were not reached.
  The data above points at the reader and the serial main loop, not the pool size: align alone runs at ~4 cores.

## 5. Pipeline prototype (Testing/notes/pipeline_proto.patch, NOT applied; local code branch, not pushed)
Structure (Main.lean, mirrored in Spec/Shim.lean):
- Two dedicated reader tasks, one per mate file. Each reads 8 MB blocks (short pipe reads are topped up) and cuts slices of
  exactly 4000 records at every 16000th newline (`cutAfter`). No parsing.
- A dedicated dispatcher pairs slice k of R1 with slice k of R2 into job k.
- 4 dedicated workers, each with these steps per job:
  1. `parseSlice` (lines as `FastqReader.line` cuts them, `parseRecord` per 4 lines)
  2. `pairUp` (`readChunk`'s name / QNAME / length checks)
  3. `trimRecord`
  4. `alignPairs` on the job
  5. `samChunk` (parts 1)
- The writer (main thread) writes jobs in sequence order, holding out-of-order results in a map.
- Bounded `Std.CloseableChannel.Sync` queues (3 slices per mate, 8 jobs, 16 results). Memory stays flat. Any task error
  prints and exits 1.

Measured, 4 threads, 1 rep each, map wall / utilization. SAM is byte-identical to festive 89ef604 on both sets, in both
variants:
| set / input | festive 89ef604 | A: `alignPairs` per job (this patch) | B: per-worker setup + `alignOneP` |
|---|---|---|---|
| nova1M plain | 32.6 s, 0.89 | 29.9 s, 0.96 | 26.8 s, 0.96 |
| nova1M FIFO | 35.3 s, 0.83 | 31.7 s, 0.92 | 27.2 s, 0.92 |
| hg002_1M plain | 38.7 s, 0.89 | 34.8 s, 0.96 | 30.1 s, 0.96 |
| hg002_1M FIFO | 46.1 s, 0.76 | 37.8 s, 0.90 | 31.2 s, 0.89 |
- A reaches 0.96 on plain files and 0.90–0.92 through zcat FIFOs. Its total CPU is about the same as festive's.
- B also cuts CPU (nova1M plain 115 → 103 s user+sys). Each `alignPairs` call reloads the index view (`readIndex`:
  H/M copies, small fields) and builds the setup in each of its 16 internal tasks. B builds the setup once per worker.
  B needs a Spec-level interface (e.g. an `alignPairs` that takes a prepared index or setup, with its own correctness
  theorem). Spec/Shim cannot call `alignOneP`. So B is not in the patch.
- FIFO is still 4–6 points below plain files. The remaining cost is zcat itself (10 s CPU on hg002_1M) competing for
  the 4 cores.

### What the prototype relies on that is not proved
1. Slice cut = record boundary: a slice ending right after every 16000th newline holds whole records (4 lines each).
   Matches `cutLinesL_boundary` in Testing/notes/byte_specs/FastqBytes.lean.
2. Slices concatenate to the file: carry handling in `reader` (`extract 0 p` / `extract p size` of the buffer).
   Compare `parseSlices_eq` / `parseFastq_append`.
3. `parseSlice` = `FastqReader.line` + `readFastqRecord` on the same bytes: CR strip before a newline only, the last line
   without a newline, and the "file ends inside a record" cases. Shaped like `lines` / `parseLines` / `parseRecord`.
4. Parallel parse = serial parse: jobs are independent, and records of job k are records `4000k ..< 4000(k+1)` of each file.
5. `pairUp` = `readChunk`'s checks in the same order. On bad input the first error reported can differ, since jobs fail in
   parallel; the exit is still non-zero.
6. Pairing slice k with slice k gives the same mate pairs as reading the files in step (needs 1 + 4).
7. The writer emits in sequence order: the pending map, `nextSeq`, and all results arriving before `res` closes.
8. `samChunk` per job, concatenated in job order = `samChunk` of the whole run's chunks: SAM lines are per pair,
   independent of chunking.
9. Task / channel behaviour of the runtime (dedicated threads, channel close semantics). Errors exit the process.
`alignPairs` itself stays proved (`alignPairs_correct`) for each job's pairs.
