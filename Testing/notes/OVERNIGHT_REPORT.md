# Overnight report (in progress)

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
