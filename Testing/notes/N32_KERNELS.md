# n32: short-read kernel / compiler work (branch `speed/n32-kernels`, 2026-11-02)

Base: `claude/festive-fermi-mf9mo6` ce7ea1d, then merged 12d1016 (mates quality-trimmed as read). hg38 release
(`bench-release`), 4 cores, 15.7 GB. Ir = callgrind instructions of the shim (`lean-align map … 100 1000`) on the first
2000 pairs, index load included. Every fix: SAM byte-identical to the base binary on 2000-pair subsets of mason,
NovaSeq, HiSeq (hg002) and low; `CI_check.sh` passes; no Spec/ or Main.lean edits; all rewrites are `@[csimp]` with
proofs or changes to unproved, re-checked code (f1).

## 1. Profile (base ce7ea1d, inclusive Ir, `--toggle-collect`)
| | mason | NovaSeq |
|---|---|---|
| total | 3468.9M | 1701.8M |
| `tierPair` (the router) | 2938.8M (84.7%) | 1002.2M (58.9%) |
| `answerOfPair` (placement: CIGAR, `chkCandD`, fallback) | 252.1M (7.3%) | 408.5M (24.0%) |
| `samLines` (SAM text, frozen `Proofs/Sam.lean` = `Spec/Sam.lean`) | 150.4M (4.3%) | 153.6M (9.0%) |
| `readFastqRecord` (frozen) | 58.5M | 60.9M |
Inside `answerOfPair` on NovaSeq: `TierHeur.bandCells` 118.6M (DP of `alignAt` with bound 10^6 and of `nearY`),
`diagPen` 58.6M, `chromOf`'s `List.range`/`filter` + allocation ≈ 50M.
Self Ir, mason: `kerGKG` 8.4%, `stageKSPN` 6.4%, `lanesAnyV` 4.9%, `svAnyU` 4.8%, `ker16KWG` 4.3%, `bwdMisU`/`fwdMisU`
8.1%, `slotW` 3.8%, `scanAWF` 3.2%, `fineE` 3.0%, `sweepA` 2.9%, `unlookV` 2.7%.

## 2. Fixes (Ir, 2000 pairs; f1–f6 measured on ce7ea1d, f7 on 12d1016)
| commit | change | mason | NovaSeq |
|---|---|---|---|
| 00bf9a2 | f1 `alignAt`: banded DP bound = router penalty + 1 (runs of a higher penalty never pass `checkMove`'s re-check) | −0.5% | −2.7% |
| c0af948 | f2 `chromOf`: one scan of the chromosomes, no list (`chromOf_eqL`) | −1.4% | −2.9% |
| e25d77a | f3 `diagPen` = −4 × `hamming` (machine-word loop; `diagPen_eqH`) | −0.6% | −1.4% |
| eaa9a78 | f4 `slotW`: `USize` offset, merged byte reads; guard `numBits = 64 ∧ sw < 16 ∧ t < 2^40`, 2^40 hoisted (`slotW_eq_slotWF`) | −2.1% | −2.3% |
| 4d31bb0 | f5 `GRead.getW` / `GRead.ok`: unboxed `PGen` letter reads in `hammingU` / `fwdMisU` / `bwdMisU`, `ok` checked once per loop | −0.6% | −0.6% |
| 9c88a20 | f6 `chromGo` on `USize` with `uget` (`chromGoU_eq`) | −0.3% | −0.7% |
| a3287a1 | f7 `ReadTrim.wl`: trimmer scores in `Int64` (reads ≤ 10 000; `wl_eq_wlF`) | −1.3% | −1.9% |
Totals: ce7ea1d → f6: mason 3468.9M → 3278.4M (−5.5%), NovaSeq 1701.8M → 1530.2M (−10.1%).
12d1016 (trimming) → a3287a1: mason 3208.0M → 2984.8M (−7.0%), NovaSeq 2349.4M → 2066.6M (−12.0%).

Pitfalls met: `t < 2^27` as `slotW`'s guard never held on hg38 (≈ 1.3G slots), so the first version ran the slow path;
the literal 2^40 in a body was rebuilt by `__gmpz_set_str` at every call (+24% Ir) until hoisted into a `@[noinline]`
constant; a per-letter platform guard inside `PGen.getU` cost more (+2.9%) than it saved — the guard belongs in the
loop's dispatcher (`GRead.ok`).

Tried and dropped: `advP` on `USize` (+0.3%: the per-call guard costs more than the 1–2 step loop saves);
`cnt64U`'s `% 255` → multiply-shift (needs a bit-vector proof; `bv_decide` is not allowed); literal hoisting in
`diagMisFast3` / `checkRunsFast3Go` / `pscanD` (their GMP calls are < 0.01% of Ir now).

## 3. What is left (NovaSeq after trimming, self Ir of a3287a1)
`scanAWF` 10.2% + `nextK` 3.9% (≈ 900k matching index entries per 2000 pairs, already machine-word code: ~240 Ir per
entry, of which ~20 reload `MzIdx` fields and the rest is the key test, flag check and genome word), `wlI` 3.1%,
`bandCells` 3.3% (~100 Ir per computed cell, compiled tightly), `stageKSPN` 4.5%, `kerGKG` 4.4%. The kernels'
remaining cost is `Nat` glue spread over large functions (`kerGKG`'s gapped path ≈ 550 Ir per call, `stageKSPN`
≈ 715 Ir per diagonal) — no single hot spot; a full `USize` rewrite of `gappedLG`/`fwdLG`/`bwdLG` composing the existing
`fwdMisU_eq` / `fwdWU_eq` / `bwdWU_eq` / `flagsOkU_eq` is the next step there. SAM text and FASTQ parsing are in
frozen files.

## 4. Timing (4 threads `taskset -c 0-3`, FASTQ + SAM included, median of 3)
minibwa c07de5c (default build, `map -t 4`, release index `mb`), base = 12d1016, head = a3287a1. Per tool and set: one
warm-up empty-FASTQ run, then 3 × (empty-FASTQ run, full run); map = wall(full) − wall(empty right before),
CPU = (user + sys)(full) − (user + sys)(empty). Full-set SAM of head = base on all 4 sets (byte-identical).
| set | minibwa map / CPU s | base map / CPU s | head map / CPU s | minibwa / head (wall, CPU) |
|---|---|---|---|---|
| NovaSeq 200k | 17.12 / 63.5 | 11.38 / 43.4 | 5.68 / 32.8 | 3.01x, 1.94x |
| sim mason 200k | 16.53 / 68.0 | 15.51 / 54.9 | 15.18 / 53.5 | 1.09x, 1.27x |
| sim low 200k | 12.46 / 46.0 | 7.77 / 28.1 | 7.84 / 28.2 | 1.59x, 1.63x |
| HiSeq 200k | 29.55 / 133.1 | 16.12 / 45.5 | 19.61 / 47.6 | 1.51x, 2.80x |
The wall numbers are NOT reliable on this box: the empty-run (index load) wall varies 1.7–17 s run to run even with
the tool's runs grouped (the shim's 5.3 GB index allocation makes the kernel reclaim page cache, minibwa's index is 7 GB,
RAM 15.7 GB), so map = full − empty swings by ±5–8 s (NovaSeq head runs: 21.9 / 5.7 / 4.6 s). A first pass with the
tools interleaved was worse (empty runs up to 500 s, negative differences) and is discarded. User CPU of the map part
(full − empty) is the steadier measure (±10%), medians of 6 runs (both passes):
| set | minibwa user s | base user s | head user s | head / base |
|---|---|---|---|---|
| NovaSeq | 57.4 | 41.4 | 36.8 | 0.89 |
| mason | 63.6 | 54.8 | 50.4 | 0.92 |
| low | 43.7 | 27.5 | 25.3 | 0.92 |
| HiSeq | 121.2 | 42.6 | 38.0 | 0.89 |
head / base user CPU matches the Ir changes (−12% NovaSeq, −7% mason). For a wall A/B on this box, run the index load
outside the timed region (e.g. a bench that loads once) rather than subtracting an empty run.
