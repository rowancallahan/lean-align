# Whole-genome hg38 speed: lean-align vs minibwa (2026-10-27/28)

Code `6d0d218` (tag `provisional`, local only), Lean 4.35.0. minibwa `lh3/minibwa` c07de5c (0.7-r427), default
Makefile and `-O3 -march=native`. Genome: hg38 with lowercase folded to upper (`hg38.upper.fa`, 3,099,925,829 letters).
Raw TIME/RESULT lines per box: `raw/`.

**Read this first: the shim's output is M1.** `answerOf` (Proofs/Bridge.lean) reports `found := none` for every pair,
so our SAM marks all pairs unmapped (1,000,000 / 1,000,000 at 1M; minibwa: 1,352 unmapped). We run the full tier
search but write no position or CIGAR. These timings are our search cost against minibwa's full mapping, not equal
output.

## Boxes

Three separate cloud boxes, one read set each, everything run one at a time on the box:
Intel Xeon @ 2.10 GHz, 4 cores (`nproc` 4), 15.7 GB RAM, ~40 GB disk allowance. Threads pinned with `taskset`.

## Map wall time, 200k pairs (s)

Ours = shim (`lean-align map`), median of 3. minibwa: one run each. Every wall includes that tool's index load.
Ratio = ours / theirs; above 1 means ours is slower.

| Set | t | ours | minibwa | native | ours/minibwa | ours/native |
|---|---|---|---|---|---|---|
| HiSeq 2×250 | 2 | 29.5 | 80.7 | 53.7 | 0.37 | 0.55 |
| HiSeq 2×250 | 4 | 18.4 | 54.7 | 29.8 | 0.34 | 0.62 |
| NovaSeq 2×151 | 2 | 40.3 | 45.7 | 31.4 | 0.88 | 1.28 |
| NovaSeq 2×151 | 4 | 25.6 | 42.4 | 17.2 | 0.60 | 1.49 |
| mason (sim) | 2 | 51.3 | 447.6* | 31.8 | — | 1.61 |
| mason (sim) | 4 | 37.3 | 47.1 | 18.7 | 0.79 | 1.99 |
| low (sim) | 2 | 34.4 | 55.6 | 25.7 | 0.62 | 1.34 |
| low (sim) | 4 | 24.2 | 36.8 | 14.6 | 0.66 | 1.66 |

\* cold page cache (first read of the 7 GB index after a container restart); not comparable.

minibwa default usually loaded its index cold (20–34 s) and native warm (5–8 s), so the **native column is the fair
one**. With load removed, minibwa default and native map at the same speed (HiSeq t4 24.3 / 23.7 s, NovaSeq t4
12.0 / 11.7 s).

## 1M HiSeq pairs, t4, warm cache (HiSeq box)

| | wall | without index load |
|---|---|---|
| ours | 79.0 | ≈76 (warm load 2.8–3.2 s) |
| minibwa native | 116.3 | ≈108 |
| minibwa default | 122.5 | ≈113 |

Ours / native 0.68 (0.70 without load). Our FASTQ/SAM I/O alone (tiny genome): 18.5 s, 23% of our wall.

## Index build

| | wall | peak |
|---|---|---|
| shim (`lean-align build`) | 1715–1968 s | 13.56 GB (kill limit ~13.96 GB) |
| bench (`whole_genome build`) | 843–993 s | 7.71 GB |
| minibwa `index -l -t 1` | 3875–4060 s | 8.40 GB |

## What this says

1. **The shim does ~2× the bench's work on the same reads.** Bench mapping only (RESULT lines, t4): HiSeq 7.0 s,
   NovaSeq 8.2 s, mason 15.3 s, low 7.4 s. Shim I/O alone is 3–4 s and warm load ~3 s, yet the shim takes
   18–37 s. Shim CPU at t4 is 59–127 s against bench 28–60 s plus I/O ~8–10 s. Not yet explained; suspects:
   insert range (shim is called with 100–1000), `cap1` for 151 bp, per-chunk overhead in the shim path.
2. We beat minibwa native only on HiSeq 2×250. On 151 bp and the simulated sets we are 1.3–2.0× slower.
3. The shim's index build needs 1.8× the bench's memory and 2× its time for the same index, and sits 0.4 GB
   under the box's kill limit.
4. I/O is 18 µs/pair; worth fixing after M2, since M2 changes what the SAM writer produces.

## Earlier results (chr21, 200k pairs, 4 cores, local box)

| Set | ours | minibwa | native |
|---|---|---|---|
| HiSeq 2×250 | 11–13 (14.7 in the packaging trial) | ~66 (69.1) | 54.5 |
| NovaSeq 2×151 | 19 | 29 | — |
| mason (heuristic off) | 8.3 | 8.5 | — |

On chr21 minibwa's run time is dominated by fixed costs, which hid the per-pair gap seen on hg38.

## Problems found during the run

- `Testing/data/downloads` is committed as a symlink to itself; `fetch.sh` fails on a fresh checkout ("Too many
  levels of symbolic links"). Each box replaced it with a directory locally.
- `compare.sh` sends the "bench check index (once)" step's stdout to `/dev/null`, which also drops its TIME line.
- Cloud containers are reclaimed when their session is idle; detached processes don't count. Two boxes lost runs
  this way (NovaSeq once, sims twice) and resumed from the saved indexes. Keep a harness-tracked wait running, or
  use prebuilt indexes so a run fits well under 2 h.
- The bench reads hg38 as one sequence ("1 chromosomes"); timing is unaffected.

## Rerun

On a 4-core box with ≥16 GB RAM and ≥40 GB disk, from the repo root at `6d0d218`:

```
rm Testing/data/downloads && mkdir Testing/data/downloads      # until the symlink is fixed
sh Testing/data/fetch.sh full                                  # chr21, hg38, hg38.upper.fa, HG002 reads
lake build lean-align whole_genome
# minibwa: git clone https://github.com/lh3/minibwa; make            (default)
#          make CFLAGS="-std=c99 -g -Wall -O3 -march=native"            (native, in a second clone)
OUT=~/cmp MB_INDEX_FLAGS=-l MB_ONCE=<set> SETS="<set>:<prefix>" \
  MINIBWA=<default>/minibwa MINIBWA_NATIVE=<native>/minibwa \
  sh Testing/scripts/compare.sh Testing/data/downloads/hg38.upper.fa
```

Sets used: `hiseq250:hg002_200k`, `novaseq151:novaseq_200k`, `mason:sim_mason`, `low:sim_low` (the sims box ran
the last two together, `MB_ONCE="mason low"`).
