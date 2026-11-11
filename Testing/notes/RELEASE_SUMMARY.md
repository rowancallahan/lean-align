# Release summary (2026-11-11)

Branch to merge into main: `claude/festive-fermi-mf9mo6`. This file lists what is in it, every claim with the
command that checks it, and what is not done. Numbers are from 4-core cloud boxes (Xeon 2.1 GHz, 15 GB) unless said.

## 1. What is in the branch
- Spec, locked: `Spec/` (Alignment, Mapping, Aligner, Fasta, Fastq, Trim, Sam, MapFiles) and `Main.lean`.
  All 8 hashed files match `Spec/FROZEN.sha256`. Not changed since you locked them.
- Proofs: 472 theorems, standard axioms only, no `sorry`. The end-to-end statement is `process_correct`
  (`Spec/MapFiles.lean`), proved in `Proofs/MapFiles.lean`.
- Since the lock, below the Spec only (`Aligner/mapper/PairNear.lean`, `Aligner/io/FastqIO.lean`, `Proofs/MapFast.lean`):
  - partner filter by binary search (`keepQ_eq`);
  - chromosome gate as a table lookup (`keepHas_eq`);
  - pair search limited to second-mate hits that can be in range (`properPairsF_eqW`);
  - jobs of 4000 pairs, 32 in flight; faster newline scan.
  All are exact-equality swaps. SAM is byte-identical before and after (md5 on 5M gz both sets and streamed 10M).
- Test and benchmark material: `Testing/verify.sh`, `Testing/ec2/`, `Testing/results/blog/` (figures, tables, zip),
  `Testing/results/stream/` (per-run files of the streamed runs), `Testing/results/ec2_check/` (raw timing.tsv, compare.txt and verify logs).

## 2. Checks you can rerun
| claim | command | expected | last run |
|---|---|---|---|
| builds, all proofs, axioms, Spec mirrors, frozen hashes, tiny-genome fuzz | `FUZZ=1 sh Testing/scripts/CI_check.sh` | `ALL CHECKS PASSED`, `472 theorems, standard axioms only`, `VIOLATIONS: none` | timing box, festive 79af844 (code identical to head) |
| all five verify steps | `bash Testing/verify.sh OUT` (see its header for the env vars) | `ALL REQUESTED STEPS PASSED` | timing box, 79af844: all 5 pass |
| step 3: no false claim vs minibwa on hg38 | inside verify | HARD A-D = 0 in 9 cells | pass |
| step 4: unique genome, columns 1-11 identical to minibwa | inside verify | identical, flagstat equal | pass (170 and 369 adapter-like pairs left out, see below) |
| laptop check | `bash Testing/ec2/setup.sh tiny DIR && bash Testing/ec2/run.sh tiny DIR` | `IDENTICAL: columns 1-11 of every record` | lead box (Linux), head |
| timing and agreement vs minibwa | `bash Testing/ec2/run.sh full DIR` | `timing.tsv`, `compare.txt` | timing box, 4 threads, 5M pairs, both data sets |

Not run by me: CI on GitHub for the head commit; anything on macOS; anything above 4 cores.

## 3. Speed, 4 threads, hg38 (sources: `Testing/results/blog/data/runs.tsv`)
| data | ours | minibwa c07de5c | wall ratio | core-hour ratio |
|---|---|---|---|---|
| NovaSeq 5M gz (EC2 script) | 83.6 s, 17.6 Gbp/core-hr, 5.7 GB | 264.7 s, 5.4, 8.8 GB | 3.2x | 3.3x |
| HiSeq 2x250 5M gz (EC2 script) | 83.2 s, 28.3, 5.9 GB | 461.7 s, 5.0, 8.5 GB | 5.5x | 5.7x |
| NovaSeq streamed 20M | 389.0 s, 16.1 | 1086.7 s, 5.3 | 2.8x | 3.1x |
| NovaSeq streamed 40M | 778.5 s, 16.1 | 2192.6 s, 5.2 | 2.8x | 3.1x |
| HiSeq lane 33.9M | 686.3 s, 26.3 | 3494.7 s, 4.5 | 5.1x | 5.8x |

- Throughput is flat with run size: 55.4 / 55.9 / 55.9 Gbp/hr at 10 / 20 / 40M NovaSeq pairs.
- Before the slow-pair fixes: 25 (HiSeq 34M) and 40 (NovaSeq 40M) jobs over 5 s, 50% / 39% of the wall with idle
  workers. After: 0 jobs over 5 s, 8.5% / 0.3%. Slowest single pair now 0.70 s.
- Caveats: one run each for the streamed and lane rows; the lane rows for the two tools are from two boxes of the
  same type; our lane run was the traced build (about 2% or less).

## 4. Accuracy (sources: `data/accuracy.tsv`, `data/ec2_compare.tsv`, `data/roc.tsv`)
- Real reads, 1M pairs: we map 93.7% (NovaSeq) / 94.0% (HiSeq), minibwa 99.1% / 99.4%. We call 81.9% / 84.9% unique,
  minibwa gives MAPQ 60 to 85.0% / 87.5%.
- Pairs we call unique and minibwa gives MAPQ 60: 781,588 of 781,588 (NovaSeq) and 818,320 of 818,322 (HiSeq) in the
  same place. The 2 HiSeq disagreements were not examined by hand.
- Simulated (mason-style, 100k pairs, on the merged build): pairs we call unique are 100.00% at the true place.
  Overall 93.9% correct vs minibwa 98.0%: the gap is pairs we leave unmapped or `unknown`.
- The Spec allows reporting more of those pairs; not doing so is an implementation choice (see open items).

## 5. Things that behave differently from what you might expect
- Adapter cutting is in the Spec, so our output differs from minibwa on reads that contain adapter-like text by
  chance (about 1 pair in 1,200 on random reads). The unique-genome checks leave those pairs out
  (`Testing/ec2/drop_adapter_pairs.py`).
- The `XT` tier tag is gone from the SAM (per the locked `Spec/Sam.lean`); `XT:Z:trimmedAwayN` remains.
- Never pass `/dev/null` as OUT: Main renames OUT.tmp over it.
- If one read file ends early or the two files have very different record sizes, memory grows without limit
  (seen: 13.9 GB, killed). See open items.

## Standing goal for speed work (Rowan, 2026-11-11)
Speed work must keep paying off as cores go up (16, 32 and beyond). Every change is checked for scaling, not only
for single-thread instructions: CPU per pair at 1, 2 and 4 threads, shared reference counts, cross-thread frees,
the single reader loop, decompression. Nothing above 4 cores has been measured yet.

## 6. Open items (yours)
1. `Main.lean`: refuse a non-regular OUT and OUT equal to an input; cap on how far one file may run past the other.
2. EC2 run at 16 and 32 threads (`Testing/ec2/README.md`). Expect gunzip and the reader loop to cap near 400-450
   Gbp/hr (estimate). Then try `rapidgzip`, bigger pipes, and branch `fix/cut-tasks` (proved, SAM identical, unmerged).
3. Mapped-`unknown` accuracy: branch `exp/unknown-walkbest` recovers about 35-40% of the gap for 5-8% CPU. Parked.
4. Trim: threshold stays 25 (softer loses mapped pairs: `exp/trim-threshold`, `Testing/notes/TRIM_THRESHOLD.md`).
   Tie rule (longest, then leftmost) and best-window-among->=25 still to decide.
5. Index build checks: chromosome names, letters (lowercase FASTA and genomes over about 4.07 Gbp fail silently:
   `Testing/notes/GENOME_AUDIT.md`), `toNat!` fail-fast, error-message holes, Phred+64 check.
6. Your own review: SAM spec, the monad part of `process`, and a rerun of the comparator and `verify.sh`.
7. `Testing/notes/FINISH_CHECKLIST.md` sections 1-4 are done (they describe the byte-spec work); the rest is still open.
8. After the release: `Testing/notes/ROADMAP.md` (settings record, RNA-seq, HiFi, nanopore).

## 7. Branches kept for reference (not merged)
`fix/cut-tasks`, `exp/unknown-walkbest`, `exp/trim-threshold`, `exp/hol-trace` (never merge), `exp/util-scripts`,
`bench/slow-pairs` (13 slow test pairs), `bench/timing-2026-11-10`, `notes/minibwa-paper`.
