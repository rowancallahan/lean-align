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

## 6. Job size and queue depth (pipeline variant A; 1 rep each; map wall / user+sys / util)
| job pairs, depth | nova1M plain | nova1M FIFO | hg002_1M plain | hg002_1M FIFO |
|---|---|---|---|---|
| 4000, 2 | 30.4 / 115.3 / 0.95 | 32.9 / 119.3 / 0.91 | 36.7 / 140.3 / 0.95 | 41.6 / 142.1 / 0.85 |
| 8000, 2 | 31.0 / 120.3 / 0.97 | 30.9 / 114.6 / 0.93 | 34.9 / 135.2 / 0.97 | 37.5 / 135.6 / 0.90 |
| 16000, 2 | 31.2 / 120.6 / 0.97 | 31.7 / 118.0 / 0.93 | 33.8 / 130.7 / 0.97 | 35.8 / 128.7 / 0.90 |
| 20000, 2 | 30.4 / 116.9 / 0.96 | 30.3 / 112.1 / 0.93 | 36.9 / 141.8 / 0.96 | 36.0 / 129.8 / 0.90 |
| 8000, 4 | 29.9 / 115.2 / 0.96 | 31.9 / 119.1 / 0.93 | 34.2 / 132.4 / 0.97 | 35.5 / 128.2 / 0.90 |
| 16000, 4 | 30.3 / 116.4 / 0.96 | 31.2 / 116.2 / 0.93 | 33.8 / 130.6 / 0.97 | 34.9 / 125.7 / 0.90 |
- SAM is byte-identical to festive at 16000/2 on both sets.
- hg002_1M: larger jobs cut CPU 7–12% (140 → 126–131 s) and map wall about 3 s. This matches the per-job `alignPairs`
  setup cost (readIndex + 16 per-task setups per call).
- nova1M: no CPU trend; all within ±2 s noise.
- Depth 4 vs 2 makes no clear difference. Patch default is now 16000 pairs, depth 2.
- Above 16000 pairs nothing improves, and the 20000 plain run is worse (noise, or fewer jobs than 4 workers can
  balance near the end).
- The remaining per-job CPU goes away only with variant B (per-worker setup), which needs a Spec-level interface.

## 7. Byte pipeline (Testing/notes/byte_pipeline.patch, NOT applied; against festive a4d9f6f)

Pipeline v2 (§5, job 16000, depth 2) plus four steps, each measured. 1 rep each. Cells are map wall s / user+sys s / util.
SAM md5 is identical to festive in every cell.

Steps:
- 0. Pipeline plus shim_speed: quality becomes a `ByteArray`, and `findNewlineU` does the newline scan.
- 1. `samChunkB`, the byte SAM writer from research/io2 `sam_bytes.patch`.
- 2. Byte names in the workers.
  - The parser is a structural recursion (`parseFrom`, fuel = slice size, 4 lines per record, calling `parseRecord`).
  - `qnameBytes` finds the QNAME bytes with a structural `spaceAt` scan.
  - `pairUp` compares those bytes, then applies `qnameOk` and the length checks.
  - The reader appends `'\n'` at EOF, which matches the spec's `lines`.
- 3. Variant B (`PIPE_B=1`, Main only). Each worker runs `readIndex` + `chunkSetup` + `withMono` once, then `alignOneP` per pair.

1M:

| set / input | festive | 0 | 1+2 (A) | 3 (B) |
|---|---|---|---|---|
| nova1M plain | 58.1 / 117.7 / 0.51 | 30.3 / 115.0 / 0.95 | 27.7 / 106.5 / 0.96 | 24.0 / 91.1 / 0.95 |
| nova1M FIFO | 33.9 / 112.4 / 0.83 | 28.4 / 104.8 / 0.92 | 26.5 / 97.9 / 0.92 | 23.7 / 86.0 / 0.91 |
| hg002_1M plain | 74.3 / 130.7 / 0.44 | 29.6 / 113.9 / 0.96 | 26.9 / 104.2 / 0.97 | 27.7 / 106.4 / 0.96 |
| hg002_1M FIFO | 42.4 / 123.3 / 0.73 | 33.2 / 118.4 / 0.89 | 30.3 / 107.5 / 0.89 | 28.1 / 98.7 / 0.88 |

5M FIFO (each 1M gz concatenated 5×). md5: nova 025f8576cd71…, hg002 606e5fea16a6….

| set | festive | A | B |
|---|---|---|---|
| nova5M | 155.4 / 514.1 / 0.83 (zcat 23.4 s cpu) | 131.2 / 476.7 / 0.91 | 117.3 / 424.3 / 0.90 |
| hg002_5M | 206.7 / 608.7 / 0.74 (zcat 49.1 s cpu) | 150.0 / 525.1 / 0.88 | 139.6 / 487.2 / 0.87 |

- **B against festive.** nova: map wall −24.5%, CPU −17.5%. hg002: map wall −32%, CPU −20%.
- **A against festive.** CPU −7% (nova) and −14% (hg002).
- **FIFO utilization.** 0.87–0.91 on FIFO is limited by zcat's own CPU. Counting zcat, the 4 cores are about 95% busy. Plain files reach 0.95–0.97.
- **Serial stages (step 4).** Callgrind on 4000 pairs: the reader/dispatcher is about 31M Ir out of about 2216M total. The serial stages stay far under one core.
- **Ir per step (callgrind, 4000 HiSeq pairs).**
  - Byte SAM: −4.7%.
  - Byte names: −3.0%.
  - B: −0.9%. B's wall and CPU gain is native (cache and allocation), not instruction count.
- **Remaining hot spots.**
  - `trimRecord`, about 237M Ir. This is S-H's area and was not touched.
  - `parseRecord`'s `allBytes` loops, about 96M Ir. A USize structural loop is the next candidate.

### Patch layout
- **Shim-compatible part.**
  - Main.lean `Pipe`, mirrored in `Spec/Shim.lean`.
  - Spec/Fastq.lean: quality as ByteArray, `findNewlineU`.
  - Spec/Sam.lean + Proofs/Sam.lean: `samChunkB` + quality bytes.
  - New file Proofs/SamBytes.lean; lakefile.lean change.
  - The Spec/ edits are a prototype copy only.
- **Main-only part.** Variant B is the `vb` branch in the worker. `Spec/Shim.lean` cannot call `alignOneP`, so the Main/Shim mirror check is expected to differ there, at Shim line ~150.
- **FROZEN.sha256.** Not in the patch. It must be regenerated after applying.
- **Proofs broken by the patch.** `lake build` (full) fails in two places. Both come from quality changing from String to ByteArray:
  - `Proofs/SamBytes.lean`: `toUTF8`/`toByteArray` applied to a ByteArray quality.
  - `Proofs/TrimRecord.lean`: `toUTF8`, plus a heartbeat timeout.

  The shim build (`lake build lean-align`) succeeds, and these proofs need adapting before merge.
- **Not touched:** ReadTrim, AdapterTrim.

### Provisional spec changes (exactly which definitions change)
1. **`FastqRecord`.** Becomes S4's shape `{qname, letters, quality : ByteArray}`. `qname` holds the QNAME bytes: no '@', comment cut at the first space, trailing "/1" or "/2" dropped.
2. **`parseRecord header letters plus quality`.** Additionally computes `qname := qnameOf header` and absorbs both the QNAME check (size 1..254, bytes in `!`..`?` or `A`..`~`) and the letters/quality length check. On success it returns the record with `qname`.
3. **`qnameOf` (bytes).** Replaces `mateName` and the String `samName` path. The prototype is `qnameBytes` (structural `spaceAt`, fuel = header size).
4. **`lines`.** Splits on `'\n'`, with a `'\n'` appended at EOF when it is missing, and strips CR. The parser follows it as `parseFrom` (fuel = size, structural).
5. **`pairUp`.** Compares mates by `qname` bytes; the error says the files are out of step.
6. **`trimRecord`.** Uses `quality` directly, without `toUTF8` / `fromUTF8!`.
7. **`samChunk`.** Replaced by `samChunkB`, which builds a ByteArray from qname, letters and quality bytes. Its byte-equality theorem is in Proofs/SamBytes, which needs adapting (see above).
8. **New, for variant B.** `alignPairsP (setup : ChunkSetup) pairs := pairs.map (alignOneP ins chroms setup ·)`, with the theorem `alignPairsP (chunkSetup index) = alignPairs index`. The Shim worker would then do the setup once per worker and call `alignPairsP`. Until that theorem exists, B stays Main-only.

### Unproved assumptions in the prototype
- The `parseFrom` and `spaceAt` fuel is sufficient: fuel = size, and every step advances at least 1 byte.
- Slice cutting at every 4k-th newline is the same as `parseFastq` on the whole file.
- `qnameBytes` is equal to `qnameOf`.
- The B setup is equal to the per-job setup (point 8).
