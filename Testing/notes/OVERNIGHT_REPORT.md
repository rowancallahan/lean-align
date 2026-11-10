# Overnight report (2026-11-10)

## Summary for Rowan
- TEST THIS: festive `claude/festive-fermi-mf9mo6` at 10629b1 or later (code = spec/mapfiles 64ae73f). Run: `FUZZ=1 sh Testing/scripts/CI_check.sh` (expect ALL CHECKS PASSED), then `MINIBWA=… bash Testing/verify.sh OUT`.
- Proofs: end to end, no sorry outside Spec/. `Spec.Total.process_correct` and `job_eq` proved, standard axioms only; 470 theorems. All 8 locked files (Spec/{Alignment,Mapping,Aligner,Fastq,Trim,Sam,MapFiles} + Main.lean) match FROZEN.sha256. Trusted: index = buildIndex genome; read/write/rename do what they say; Main's IO = `process` with nextChunks/out.write.
- Fuzz: 210/210 pass (chunk sizes 1/7/4096/8 MB, 41 invalid-input cases, random pairs, uneven read lengths). SAM = festive with the tier tag removed (200k, 1M, 5M; NovaSeq and HiSeq).
- Speed (corrected, see below): CPU −4 to −8% vs the old build; Gbp per core-hour ~3× minibwa (NovaSeq) and ~5× (HiSeq). BUT on piped .gz input (5M) the new build is slower in wall time (+12% / +27%) because Main reads the two files on one thread; fix is in the locked Main (your call), being confirmed now.
- BUG found: `lean-align map … /dev/null` destroys /dev/null (Main renames OUT.tmp onto OUT). verify.sh fixed; Main fix is your call (locked).
- Decisions for you: Main /dev/null fix; trim tie rule + best window ≥ 25 (your list); bandCellsJ kernel (~2%, a day of proofs); mapped-unknown experiment (exp/unknown-walkbest: +0.5% pairs at the true position, small NovaSeq time cost); spec review items (Testing/notes/SPEC_REVIEW.md).


> **WARNING (found overnight): do not run `lean-align map … /dev/null`.** Main writes OUT.tmp and renames it onto OUT, so with OUT = /dev/null (as root) it creates /dev/null.tmp and renames it over /dev/null, turning /dev/null into a regular file. `Testing/verify.sh` step 5 is fixed to use a drained FIFO instead. Fixing Main itself (e.g. refuse an OUT that exists and is not a regular file, fail fast) is a change to the locked Main.lean: Rowan's decision.

## CORRECTED speed (S-T, branch bench/timing-2026-11-10 d9cf10e): both builds with a FIFO sink (festive e96862d = fsk, new 64ae73f = mfk)
1M plain, map-only s | Gbp per core-hour | core use:
| set | T | old | new |
|---|---|---|---|
| NovaSeq | 1 | 71.9 / 15.5 / .97 | 68.7 / 16.3 / .97 |
| | 4 | 17.7 / 16.0 / .96 | 17.2 / 16.8 / .94 |
| HiSeq | 1 | 77.8 / 23.6 / .97 | 71.2 / 25.7 / .98 |
| | 4 | 19.1 / 25.9 / .90 | 18.8 / 28.1 / .84 |
(The FIFO sink adds ~1.5–2 s on 1M; minibwa wrote to /dev/null: NovaSeq 44.3 s, HiSeq 84.4 s at 4 threads.)
5M through zcat pipes, 4 threads, map s / CPU s / core use: NovaSeq old 98.3 / 370.8 / .94, new 109.9 / 344.2 / .78, minibwa 255.6 / 993.8 / .97; HiSeq old 109.1 / 387.7 / .89, new 138.3 / 357.8 / .65, minibwa 474.0 / 1842.7 / .97.
=> The new build uses 4–8% less CPU, but on piped (zcat) input it is SLOWER in wall time (+12% NovaSeq, +27% HiSeq): cores idle. Likely cause: Main's nextChunks reads the two pipes one after the other on one thread, so the two decompressors no longer run in parallel (the old shim had one reader thread per file). Being tested (plain-file subset; big pipe buffers). If confirmed, the fix is in Main's nextChunks (read both files concurrently / read ahead) — locked Main, your decision. Still far ahead of minibwa on CPU (Gbp per core-hour ~16–28 vs ~5–6).

## Correctness: new streaming build (spec/mapfiles 53c1ab2) vs festive, 4 threads (S-T)
SAM md5 identical after removing XT:Z:<tier> (trimmedAway kept): n1m bcd41c6e…, h1m 89fb1ec8….

## Mapped `unknown` pairs (festive output; S-T)
| set | mapped unknown | AS1+AS2 = XB | below XB by 1–8 | below XB by > 8 | XB ≥ bound | XB < bound |
|---|---|---|---|---|---|---|
| NovaSeq 1M | 117,837 (11.8%) | 20,952 | 25,014 | 71,871 | 112,082 (11.2%) | 5,755 (0.6%) |
| HiSeq 1M | 90,837 (9.1%) | 15,095 | 21,685 | 54,057 | 83,795 (8.4%) | 7,042 (0.7%) |
Mostly tiers boundsOnly and stoppedEarly. Not a tiny number: about 1 pair in 9 is mapped with XU unknown and a gap to XB.
Other XU (NovaSeq): unique 819,296; unknown (all) 165,772; repetitiveUnknown 8,503; none 6,429.
Consequence for the stricter rule (mapped unknown only if XB < bound): ~11% of pairs would need more search. Expect a real speed cost; the morning experiment measures it.

## Fuzzing the new build (S-F, harness fuzz/harness 8873367): 190 pass / 0 fail
- Chunk sizes 1, 7, 4096 and 8 MB: SAM byte-identical across all four and equal to festive (tier tags removed).
- 41 validity cases × 5 builds, one per rule of Record.valid / prepPairs: every reject exits 1 with no OUT and no OUT.tmp; every accept exits 0.
- Random valid pairs (seeds 2–9, ~800 pairs each; adapters, N, low quality, trimmed away, long reads): equal to festive.
- Next: random seeds at chunk 7 / 4096, and files with very different read lengths.
- Chunk stress (fuzz/harness 156ae6e, Testing/fuzz/fuzz_chunks.py): 20 pass / 0 fail. Random sets at chunk 1/7/4096 byte-identical to the default build; uneven mate lengths (250×50, 50×250, 101×101, 1000×25) identical across chunk sizes and equal to festive (with 80–564 mapped records each).

## Fused SAM writer (S-H, fused/writer 61e998c)
`samChunkF` writes each job's SAM in one pass into one pre-sized buffer; `samChunkF_eq : samChunkF = samChunkS` with `@[csimp]`, standard axioms. SAM identical.
callgrind, 4000 pairs: NovaSeq 1,831.0M → 1,747.3M instructions (−4.6%); HiSeq 2,049.0M → 1,934.1M (−5.6%). The writer itself: 149M → 70M.
Next: fused cut+trim (trimming is ~6% of NovaSeq instructions; ~1–2% to gain).

## Where the time goes (S-P, callgrind on festive 027ef1e, 4000 pairs; notes/profile-027ef1e, Testing/notes/PROFILE.md)
NovaSeq / HiSeq, % of instructions: alignment 75.9 / 72.4; SAM formatting 8.2 / 9.7 (before the fused writer); trimming 5.7 / 7.6; FASTQ parsing 4.5 / 4.9; slice cutting 2.0 / 2.2; pairing 1.2 / 1.1. Allocation + reference counting 14% (inside the stages); memcpy 3–4%.
Cheap wins found: big-number literals parsed at runtime (gmpz_init_set_str, 13 calls per pair) 2.4–2.7%; the FASTQ error record built for every valid read 2.0–2.3%. Then allocation/closures in the aligner (~5–7%), one newline scan (~3–4%).
After S-H's fused writer and trimB csimp (fused/writer): NovaSeq 1,831.0M → 1,742.3M instructions (−4.8%), HiSeq 2,049.0M → 1,929.4M (−5.8%), SAM identical.
- fe54e60 (S-H): `size < 4294967296` guards made Lean parse "4294967296" from a string on every call (lean_cstr_to_nat, ~630 instructions, 88k calls per 4000 pairs). Rewritten as `size ≤ 4294967295`, same proofs. NovaSeq −4.2%, HiSeq −3.8%.
- Cumulative on fused/writer vs the new build 53c1ab2: NovaSeq 1,831.0M → 1,668.8M instructions (−8.9%), HiSeq 2,049.0M → 1,855.8M (−9.4%), SAM identical. Wall time pending (S-T).
- Rule: never compare against a Nat literal ≥ 2^32 in compiled code.

## Core use (S-U, festive 027ef1e on a 4-core box; SAM md5 identical across all 42 runs per set)
- No heavy tail: job time max/median 1.31 (HiSeq), 1.20 (NovaSeq). Workers busy 96.3–97.5% of the run; core use 94.3% (HiSeq), 95.0% (NovaSeq) on this box (not the 88% seen before; different box/state).
- Loss at 4 threads: end-of-run idle 2.3%, start 0.4%, steady 0.9%, plus ~2.3% "in a job but not on CPU" (page faults, allocation, preemption by reader/writer threads).
- Smaller jobs (8000/4000/2000 pairs) cut the end idle from 0.38 s to 0.09 s but the wall-time change is within noise; more jobs in flight: nothing. Scheduling is worth ≤ 1–2% at 4 threads.
- For 16/32 threads (estimate): 16000-pair jobs leave too few per worker (2 per worker at 32 threads; tail ~10–15%). Use 2000–4000-pair jobs in streaming (no measured cost), one shared ordered queue, ordering window ~4×threads jobs. At 32 threads the single reader pair and the ordered writer may become the limit; measure reader/writer MB/s there.

## process_correct (S4, proof/mapfiles2 506ebe8)
Proved, no sorry, standard axioms, as `process_correct'`: the Spec's exact statement, assuming one lemma `job_eq` (a fast job = mapReads of its two slices), which S-G is proving. Covers carries, slices of 4·16000 lines, up to 8 jobs in flight, any chunk sizes, a step failing exactly when mapReads of the whole files fails, and the last job when one file has more slices. Remaining: job_eq, and closing the sorry in Proofs/MapFiles without changing the Spec text (generic proof applied there, or exact copies).
- 031ba75 (S-H): FASTQ record checks fused into the line scans, errors byte-identical (`@[csimp] parseFastqB_eqF`); parse 48.7M → 32.4M. NovaSeq −1.0%, HiSeq −1.2%. FASTQ edge cases 20/20.
- Cumulative on fused/writer vs 53c1ab2: NovaSeq 1,831.0M → 1,652.4M (−9.8%), HiSeq 2,049.0M → 1,833.7M (−10.5%), SAM identical.
- Next: closures and reference counting in the aligner; investigate the fallback tiers redoing work (report only).

## Integration (S-G, spec/mapfiles 4ec347f) and speed of the new build before the optimizations
CI FUZZ=1: all hashes OK, build OK, all Spec mirrors OK, output fuzz 2917 pairs with no violations, FASTQ cases 20/20. Only failure: the remaining `sorry` (job_eq, being closed now).
SAM vs festive (tier tags stripped) identical on 200k and 5M, NovaSeq and HiSeq.
4 cores, 3 interleaved reps, medians (wall / CPU):
| run | festive 027ef1e | new build |
|---|---|---|
| 1M NovaSeq, map only | 22.4 / 85.4 s | 21.7 / 83.4 s |
| 1M HiSeq, map only | 23.2 / 90.0 s | 23.1 / 89.4 s |
| 5M NovaSeq FIFO, whole run | 121.7 / 466.4 s | 117.4 / 449.9 s |
| 5M HiSeq FIFO, whole run | 130.3 / 500.9 s | 128.0 / 490.7 s |
No slower anywhere. (The ~10% instruction savings on fused/writer are not in these numbers yet.)
S4 (proof/mapfiles2 70e9215): process_correct now proved inside Proofs/MapFiles.lean with the Spec text unchanged (via copies in Proofs/MapDefs.lean, checked by check_copies.sh); only job_eq left.

## Aligner rare paths (S-H, investigation)
- Last resort (1.7% of pairs, 15.5% of instructions): its best pair is usually tied, and the reported pair follows pairsAt's tie order, so it can't be skipped without changing which tied pair is reported (an output change, not allowed). Best same-output saving ≤ 0.9%. Dropped.
- Walk (14.5% of pairs, 15% of instructions): mostly the banded DP kernel bandCellsJ (~90 instructions per cell, boxed arrays). Same-result options: word copies in window extraction (~0.6%, doing now); a flat-array kernel (~2%, about a day of re-proving). Decision for Rowan.

## Merged into festive
spec/mapfiles 64ae73f merged into festive (code identical to 64ae73f; only notes differ).
- FUZZ=1 CI on 64ae73f: ALL CHECKS PASSED. 470 theorems, standard axioms only; `Spec.Total.process_correct`, `Spec.MapCopy.job_eq`: [propext, Classical.choice, Quot.sound] (re-checked by a local build). No sorry outside Spec/. All 8 FROZEN hashes OK. Mirrors and the MapDefs copy check OK.
- Fuzz (S-F) on 64ae73f: 210 / 210 pass (chunk sizes 1/7/4096/8 MB, 41 validity cases, random pairs, uneven read lengths).
- SAM = festive with tier tags removed (200k and 5M, NovaSeq and HiSeq).
- Layout: all specs in Spec/ (Alignment, Mapping, Aligner, Fasta, Fastq, Trim, Sam, MapFiles) + Main.lean.

## Mapped-unknown accuracy (S-A, experiment branch exp/unknown-walkbest; Spec untouched, proofs rebuilt, not merged)
Cause: when the router's gate budget (60000) trips, the fallback walk reports the FIRST acceptable pair among a few anchors (rarest seed per strand, up to 3 entries).
Idea A: the walk evaluates all its candidates and keeps the best AS1+AS2 (proved: bestPair_mem + walkAt_sound).
| set | at true position | gap > 16 | gap 0 | wall (1 run) |
|---|---|---|---|---|
| mason 200k (sim) | 187,909 → 188,813 (+904) | 10,154 → 9,281 | 504 → 570 | |
| low-error 200k (sim) | 193,308 → 194,489 (+1,181) | 3,103 → 1,807 | 1,852 → 2,412 | |
| NovaSeq 1M | | 52,430 → 44,035 | 20,952 → 25,089 | 20.8 → 22.4 s |
| HiSeq 1M | | 40,180 → 35,411 | 15,095 → 16,719 | 25.2 → 25.4 s |
Mapped counts unchanged; SAM changes only on pairs that were mapped-unknown. Next: cut the NovaSeq time cost (stop early when the candidate is near the bound), steer anchors with the other mate's seeds.

## Speed: final build (NOTE: the 'new' column below wrote its SAM into a RAM file because of the /dev/null bug; corrected FIFO-sink numbers follow)
## (was) Speed: final build (festive = spec/mapfiles 64ae73f) vs old festive (e96862d) vs minibwa (S-T)
1M plain, SAM to /dev/null, taskset 0..T-1, median of 3, index load measured in the run and subtracted. Map-only seconds | Gbp per core-hour (map CPU) | core use.
| set | threads | old festive | new | minibwa |
|---|---|---|---|---|
| NovaSeq (0.60 Gbp) | 1 | 60.9 s / 18.3 / 0.98 | 57.2 s / 19.5 / 0.97 | 175.0 s / 6.3 / 0.99 |
| | 2 | 31.4 s / 17.8 / 0.97 | 28.1 s / 19.9 / 0.97 | 88.5 s / 6.2 / 0.99 |
| | 4 | 15.8 s / 17.9 / 0.96 | 14.5 s / 19.7 / 0.95 | 44.3 s / 6.2 / 0.99 |
| HiSeq (1.0 Gbp) | 1 | 65.3 s / 28.1 / 0.97 | 58.3 s / 31.5 / 0.97 | 333.1 s / 5.4 / 0.99 |
| | 2 | 32.7 s / 28.7 / 0.95 | 30.3 s / 31.6 / 0.93 | 166.9 s / 5.4 / 0.99 |
| | 4 | 17.5 s / 28.7 / 0.89 | 16.8 s / 31.5 / 0.85 | 84.4 s / 5.4 / 0.99 |
- New vs old festive at 4 threads: NovaSeq −8.2% map time / −9.4% CPU; HiSeq −4.0% / −8.8%.
- New vs minibwa at 4 threads: NovaSeq 3.1× faster wall, 3.2× Gbp per core-hour; HiSeq 5.0× wall, 5.8× per core-hour.
- SAM md5 = festive with tier tags removed (NovaSeq bcd41c6e…, HiSeq 89fb1ec8…). Reps within ~3%.
- To look at: HiSeq core use at 4 threads is 0.85 (old 0.89); index load 1.8 s vs 1.5 s.

## Accuracy and uniqueness vs minibwa (S-P and S-A, 2026-11-10)
Real reads, 200k pairs, % of pairs: proper pair ours 93.8 (NovaSeq) / 93.6 (HiSeq), minibwa 97.6 / 98.1. Ours proved unique 82.4 / 84.6; minibwa MAPQ 60 on both mates 84.9 / 87.4 (MAPQ ≥ 30: 90.9 / 92.3). Ours mapped-unknown 11.4 / 9.1; ours not proper 6.2 / 6.4.
Of our unique pairs, minibwa gives MAPQ < 30 to only 0.5% (789 / 532 pairs). Both unique: same position within 10 bp 99.25% (NovaSeq), 75.6% (HiSeq; unexplained, probably trimming / soft clipping on 2×250).
Simulated, pairs correct (both mates within 10 bp of truth), ours vs minibwa: mason 93.9 vs 98.0; low 96.6 vs 98.3; high 80.9 vs 98.0.
By our class (n; ours correct %; minibwa correct %): unique: mason 86,604; 100.00; 99.99 · low 94,164; 99.99; 99.99 · high 59,278; 99.94; 99.97. unknown: 10,017; 72.9; 84.7 · 5,348; 45.6; 69.7 · 23,814; 90.8; 95.2. Not mapped/proper: 3,379; 0; 87.5 · 488; 0; 76.4 · 16,908; 0; 95.0.
=> Our "unique" is as correct as minibwa's MAPQ 60. The accuracy gap is (1) pairs we leave unmapped (the biggest part; 16.9% on `high`), (2) mapped-unknown pairs.
S-A (exp/unknown-walkbest, proved, Spec untouched): walk keeps the best candidate with early stop at −4: unknown pairs at truth mason 14,898 → 15,791 (minibwa 17,357), low 4,854 → 5,961 (minibwa 7,286); time +3–5% on 1M NovaSeq (noisy).

## Streamed 10M NovaSeq pairs, 4 threads, ours vs minibwa (S-P, 2026-11-10; curl | gunzip into FIFOs; 3.02 Gbp)
| | ours (64ae73f + trace) | minibwa |
|---|---|---|
| wall | 303.5 s | 742.8 s (incl. 158.9 s cold index load; ~584 s map) |
| aligner CPU | 832.8 s | 2233.3 s |
| cores busy (aligner CPU / wall) | 2.74 | 3.01 |
| peak RSS | 5.74 GB | 8.79 GB |
| Gbp/hr (wall) | 35.8 | 14.6 (18.6 without its load) |
| Gbp per core-hour (aligner CPU) | 13.06 | 4.87 |
Raw download+gunzip alone: 350k pairs/s (≈ 10× our mapping rate), so the stream is not the limit.
SLOW JOBS in ours: 6 of 625 jobs over 5 s (#185 25.5 s, #445 29.8 s, #525 10.3 s, #564 17.4 s, #566 10.1 s, #606 26.5 s; median 1.25 s). For 97.9 s of the 296.7 s span fewer than 4 jobs ran (82.8 s with only 1). So the slow-job problem is also in NovaSeq, about 1 job in 100, and costs roughly a third of the wall time. Must fix (see FINISH_CHECKLIST).
