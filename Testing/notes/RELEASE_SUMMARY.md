# Release summary (2026-11-11)

Branch to merge into main: `claude/festive-fermi-mf9mo6`. This file lists what is in it, every claim with the
command that checks it, and what is not done. Numbers are from 4-core cloud boxes (Xeon 2.1 GHz, 15 GB) unless said.

## 1. What is in the branch
- Spec, locked: `Spec/` (Alignment, Mapping, Aligner, Fasta, Fastq, Trim, Sam, MapFiles) and `Main.lean`.
  All 8 hashed files match `Spec/FROZEN.sha256`. Not changed since you locked them.
- Proofs: 472 theorems, standard axioms only, no `sorry`. The end-to-end statement is `process_correct`
  (`Spec/MapFiles.lean`), proved in `Proofs/MapFiles.lean`.
- Code = integrated build `cc26db2` (merged 2026-11-11). Below the Spec only, all exact-equality swaps, SAM
  byte-identical to the previous build `f465a57`:
  - round 1 (slow pairs): partner filter by binary search, chromosome gate as a table lookup, pair search limited
    to second-mate hits in range, jobs of 4000 pairs with 32 in flight;
  - round 2 (instructions, 14 commits): minimizer scan as one machine-word loop, walk anchors deduplicated,
    gap-free re-check as a byte compare, sizes sorted once per strand, layout check without a list, no tuple in
    the proper-pair check, traceback that allocates only on a step change, reverse-strand SAM write in place,
    no copy for a read kept whole, trim and adapter loops without run-time checks, number formatting on words.
- Test and benchmark material: `Testing/verify.sh`, `Testing/ec2/`, `Testing/results/blog/` (figures, tables, zip),
  `Testing/results/stream/` (streamed runs), `Testing/results/ec2_check/` (raw timing.tsv, compare.txt, verify logs;
  `instr_all/` is the integrated build).

## 2. Checks you can rerun
| claim | command | expected | last run |
|---|---|---|---|
| builds, all proofs, axioms, Spec mirrors, frozen hashes, tiny-genome fuzz | `FUZZ=1 sh Testing/scripts/CI_check.sh` | `ALL CHECKS PASSED`, `472 theorems, standard axioms only`, `VIOLATIONS: none` | Opus box and timing box, cc26db2 |
| all five verify steps | `bash Testing/verify.sh OUT` (see its header for the env vars) | `ALL REQUESTED STEPS PASSED` | timing box, cc26db2: all 5 pass |
| step 3: no false claim vs minibwa on hg38 | inside verify | HARD A-D = 0 in 9 cells | pass |
| step 4: unique genome, columns 1-11 identical to minibwa | inside verify | identical, flagstat equal | pass (adapter-like pairs left out, see section 5) |
| output unchanged by the speed work | full-run SAM md5, 5M gz, both sets, cc26db2 vs f465a57 | equal | timing box: equal on both |
| laptop check | `bash Testing/ec2/setup.sh tiny DIR && bash Testing/ec2/run.sh tiny DIR` | `IDENTICAL: columns 1-11 of every record` | lead box (Linux), on f465a57 code; not rerun on cc26db2 |
| timing and agreement vs minibwa | `bash Testing/ec2/run.sh full DIR` | `timing.tsv`, `compare.txt` | timing box, 4 threads, 5M pairs, both sets, cc26db2 |

Not run by me: CI on GitHub for the head commit; anything on macOS; anything above 4 cores.

## 3. Speed, 4 threads, hg38 (sources: `Testing/results/blog/data/reps.tsv`, `runs.tsv`)
New build cc26db2 vs minibwa c07de5c, three alternating runs per tool in one session, medians:
| data | ours | minibwa | wall ratio | core-hour ratio |
|---|---|---|---|---|
| NovaSeq 5M gz | 85.5 s, 63.5 Gbp/hr, 16.9 Gbp/core-hr, 5.7 GB | 276.8 s, 19.6, 5.1, 8.8 GB | 3.2x | 3.3x |
| HiSeq 2x250 5M gz | 93.9 s, 95.1, 25.6, 5.9 GB | 525.3 s, 17.0, 4.4, 8.5 GB | 5.6x | 5.9x |
| NovaSeq streamed 10M | 191.5 s, 56.8, 16.7 | 596.0 s, 18.2, 4.8 | 3.1x | 3.4x |
| HiSeq streamed 10M | 226.5 s, 78.9, 24.8 | 1123.6 s, 15.9, 4.2 | 5.0x | 5.9x |

- The boxes were slower in this session than the night before (the old build measured 57.5 Gbp/hr on NovaSeq gz
  here, 65.0 the night before). Compare within a session; the ratios are the stable part.
- gz rows: wall includes index load, CPU includes both gunzips. Streamed rows: aligner CPU only.
- Larger runs on the previous build f465a57 (one run each): NovaSeq streamed 40M 778.5 s vs minibwa 2192.6 s (2.8x);
  HiSeq lane 33.9M 686.3 s vs 3494.7 s (5.1x); throughput flat at 55.4 / 55.9 / 55.9 Gbp/hr for 10 / 20 / 40M pairs.
  Not rerun on cc26db2.
- Slow pairs (round 1): before, 25 (HiSeq 34M) and 40 (NovaSeq 40M) jobs over 5 s; after, none; slowest pair 0.70 s.

This round, cc26db2 vs f465a57 (same session each):
| measure | NovaSeq | HiSeq |
|---|---|---|
| instructions (callgrind, 50k pairs) | -12.0% | -7.4% |
| 5M gz wall / CPU (3 runs each) | -9.5% / -8.4% | -7.5% / -7.7% (one run only -2%) |
| 5M gz, second series (1 MiB pipes) wall | -7.8% | -4.8% (runs overlap) |
| streamed 10M wall | -8.0% | no measurable difference, within about +/-3% (A/B of 6 pairs: -2.5% mean, not separable from drift) |
| peak memory | equal | equal |

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
Cache behaviour is part of this (Rowan, 2026-11-11): target large server CPUs first, laptops second, phones last.
Look for batched index lookups so misses overlap, data layout, huge pages for the index, and run-time parameters
(for example a batch size from the cache size) only when every value is proved to give identical output.

## Index build memory (measured 2026-11-11, f465a57)
`lean-align build` on hg38 (multi-line FASTA): 1,557 s wall on 4 cores, peak 13.84 GB. A one-line-per-chromosome
FASTA needs a few hundred MB more (killed at a 14.0 GB limit, twice). The peak is during the save: about 8.9 GB of
built tables plus the 5.3 GB index being written. Allow 16 GB. An older note records 9.85-10.76 GB; the builder code
has not changed since, so that figure was probably measured differently. Not investigated further.

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
