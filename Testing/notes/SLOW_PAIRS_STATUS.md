# Slow pairs: status (2026-11-10 20:20 UTC). TOP PRIORITY before release. Spec stays unchanged.

## Problem
Single read pairs that take seconds to a minute (normal: ~1 ms). They are low-complexity reads (e.g. 26 A's then other letters; poly-T) trimmed to ~25–30 letters. requiredMapBound = 0; one grid seed, so the repetitive witness cannot apply; the last-resort search (`lookAt` → `pairsAtS`) enumerates hits(mate 1) × hits(mate 2).
The streaming build writes jobs in order, so one slow job idles the other workers:
- HiSeq 5M gz (one test box): one 55 s pair; wall 138 s vs old shim 110 s, cores 0.65.
- NovaSeq streamed 10M: 6 of 625 jobs take 10–30 s; 98 of 297 s with < 4 jobs running. 20M: 19 of 1250 jobs, up to 47 s; 270 of 712 s with < 4 running.
The old shim has the same slow pairs (55 s alone) but hid them (independent workers, out-of-order buffering, 8.6 GB RSS).
Repro files: branch bench/slow-pairs (Testing/notes/slow_pairs/: slow1 55–61 s, slow2 5.5–7.5 s, slow3 3–4 s; NovaSeq examples to come under nova/).

## Fix (proved, SAM identical): branch fix/slow-pairs 351301d
`keepTab`/`keepQ`: the partner filter in `hitsKPFN` uses a sorted table + binary search instead of scanning the whole hit list (`keepQ_eq`, via the existing `@[csimp] hitsKPFN_eqG`). FUZZ=1 CI passes. slow1 61.6 → ~2.6 s; slow2, slow3 → ~0 s; SAM byte-identical.

## In progress
- S-G: stop at the first score-0 proper pair in the same order (identical output if `topW` keeps the first maximum; separate proved commit). Combined branch `fix/fast` = fix/slow-pairs + jobs of 4000 pairs + in-flight window 32.
- S-T: time fix/slow-pairs on its 5M HiSeq / NovaSeq gz (where the stall showed) and on the 3 slow pairs.
- S-P: slow NovaSeq pairs (trace build 4ced426), then fix/slow-pairs on the streamed 10M / 20M / 40M vs minibwa.
- If pairs are still slow afterwards: more ideas (no Spec change): an index part for exact low-complexity seeds; budgeted early stop with a pair in hand (allowed by the Spec, changes SAM for those pairs).

## Other candidates (all proved, fuzzed, SAM identical; not merged)
fix/small-chunks 15365bf (faster newline scan, window 16); fix/small-jobs d4ab3d3 (4000-pair jobs, window 32); fix/cut-tasks b5bd3ca (cutting off the main thread, for 16–32 cores). Dropped: fix/parallel-read (Main change, no gain), fix/dedicated (no gain).
Trace build for measuring: exp/hol-trace 4ced426 (NEVER MERGE).
