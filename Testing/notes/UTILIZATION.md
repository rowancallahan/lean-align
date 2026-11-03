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
