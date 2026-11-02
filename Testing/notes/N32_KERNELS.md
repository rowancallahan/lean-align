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

## 4. Timing
See §4 table (filled from the timing run).
