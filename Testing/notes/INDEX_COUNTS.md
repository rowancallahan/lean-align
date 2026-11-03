# Index-side heavy 25-mer table (`speed/index-counts`, off proof/gaveup2 d18dbbd)

Goal: Rowan's `Read.highlyRepetitiveIn` witness (≥ `gaveUpSeeds` = 2 grid seeds, each with
`Genome.occurrences` ≥ `gaveUpRepeats` = 200, both strands) as a cheap lookup instead of the
genome-checked places count (~0.5–1M instr per repetitive seed, forward strand only).

## Design (approved by the coordinator)
- Table H: the sorted canonical codes (min of the 2-bit code and its reverse-complement code; 50 bits)
  of 25-mers with ≥ 200 occurrences counting both strands. 25 is odd, so no 25-mer is its own reverse
  complement.
- A new section of the saved index, written after `ns`; `LoadedIndex` gains a field. The builder is
  unproved fast code. Soundness comes from a check added to `indexOk`, which runs once at build time, as
  the existing checks do. A builder bug can only cost speed.
- Check, per entry c: decode the bytes W and the reverse-complement bytes W', then require
  `inChromCount (lookupSeed W) + inChromCount (lookupSeed W') ≥ 200`. This reuses `Mz.lookupSeed_mem`
  and `_sorted` and GaveUp's `count_le_occurrences` and `placeOf_nodup`. The forward count is
  ≤ `forward.sum` and the rc count is ≤ `backward.sum`, so no disjointness argument is needed. One extra
  lemma: `reverseComplement` is an involution on ACGT, because the canonical code maps a seed to W or W'.
- Query: the grid seed must be all ACGT. Compute its canonical code and binary-search H. Soundness
  needs only "found ⇒ some H[i] = c", without any sortedness proof. That gives
  `occurrences (seed i) ≥ 200`, then countP monotonicity gives `highlyRepetitiveIn`.
- Wiring: the leftover path (after the router) replaces `repeatMate`. Witness-first before the router
  is kept only as a measured option, because it gives up on pairs the router would place uniquely.

## hg38 counts (Testing/scripts/heavy_count.c; uppercase bench-release genome.fa, 195 chromosomes)
Windows: all-ACGT 25-letter windows inside one chromosome, 2,934,849,080 in total. The largest count
is 331,484 copies.

| copies ≥ | distinct canonical 25-mers | table at 8 B | windows covered |
|---|---|---|---|
| 100 | 467,415 | 3.7 MB | 270.6M (9.2%) |
| **200** | **228,871** | **1.8 MB** | 237.8M (8.1%) |
| 500 | 93,915 | 0.8 MB | 196.7M (6.7%) |
| 1,000 | 47,129 | 0.4 MB | 164.6M (5.6%) |
| 10,000 | 2,371 | 0.02 MB | 50.8M (1.7%) |

C counter: 32 hash partitions over 4 threads, 7.7 min wall (26.6 min CPU), about 7 GB peak. A Lean
builder can use the same partitioned sort-and-count. 16 partitions ran out of memory on this 15 GB box.

## RAM budget
Rowan's limit is a whole loaded index just under 8 GB; today it is ~5.3 GB. The heavy table at N = 200
takes 1.8 MB, so it uses almost none of the ~2.5 GB headroom. That leaves ≈ 2.5 GB for a later
short-seed component.

## Status
Lean is not available in this session: the permission policy refused to run the elan/Lean release.
Nothing in Lean is built yet: no table section, check, wiring, CI, or Ir measurements.
