# Index-side heavy 25-mer table (`speed/index-counts`, on festive-fermi 39ae4e8)

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

## What is built and proved (Proofs/Heavy.lean, Proofs/HeavyBuild.lean, Proofs/Aligner.lean)
- Table `H`: both orientations, 25 bytes per entry, sorted (the query needs no canonical code). Mask `M`: one byte
  per entry, 1 = passed `entryOk` on the built index. Both are saved after `ns`; `LoadedIndex` is a 6-tuple.
- `entryOk i`: `capCount(entry) + capCount(rc entry) ≥ 200`. `capCount` = in-chromosome places among the first 200
  places of the exact place list; it is computed with the capped lookup (`capCount_eqF`, csimp). `indexOk` adds
  `heavyOk` (every masked entry passes); the mask and the check run on 16 tasks (`heavyMask_eqP`, `heavyOk_eqP`).
- `heavyMate_sound`: ≥ `gaveUpSeeds` grid seeds found (binary search, `M = 1`) ⇒ `highlyRepetitiveIn`. Uses
  `GaveUp.occurrences_eq` (occurrences = forward(w) + forward(rc w)) and `seedCount_le_occList` per strand. The proof
  needs no sortedness: a found entry equals the seed byte for byte.
- Completeness: `buildIndex_eq_saveIndex` keeps its statement and is re-proved. New `heavyOk_mask`: two checked
  indexes of one genome have the same exact sorted place lists (`lookupSeed_mem`/`_sorted`), so a mask computed
  on the built index passes on the loaded one.
- The builder `HeavyBuild.table` is unproved and capped at 2^63 bytes. Pass 1 uses 256 MB of saturating byte counters
  over a 28-bit hash of the canonical code; pass 2 keeps exact counts in a hash map for codes whose counter is ≥ 200.
- Wiring: the gave-up stage (leftovers, after the router) uses `heavyMate` instead of `repeatMate`.
  `witnessFirst` (Proofs/Aligner.lean) is OFF by default. When on, a flagged pair answers bound 0 +
  `.repetitiveUnknown` before the router. Both settings are proved.
- CI with FUZZ=1 passes on 67c608f: 452 theorems, standard axioms only.

## hg38 build (this box: 4 cores, 15 GB)
| | 39ae4e8 | this branch |
|---|---|---|
| index size | 5,326,114,456 B | 5,338,015,764 B (+11.9 MB, +0.22%) |
| build wall / CPU | 24.8 min / 30.3 min user | 31.0 min / 39.1 min user (+6.2 min wall, +25%) |
| peak RSS | not recorded (logging failed) | 10.76 GB |
- Table: 457,742 entries (= 2 × 228,871, the C count). Every entry passed the check: the mask has 457,742 ones.
- The builder alone (heavy_bench): 4.6 min single-threaded, plus 2.6 min to read the FASTA.
- Loaded RAM: +11.9 MB per loaded copy. `rdBytes` copies H and M on every load (one per task per chunk).

## Ir (callgrind, the shim, first 2000 pairs, index load included; Testing/repro/ir.sh with the index as argument)
| binary | index | NovaSeq | HiSeq (hg002) |
|---|---|---|---|
| festive-fermi 0e48158 (no floor) | shim.idx | 960.4M | 1309.4M |
| proof/gaveup2 d18dbbd (gaveUp 500, ManyPlaces) | shim.idx | 2732.7M | 1993.6M |
| speed/floor-real-spec 61e4daa (repeatMate, 200) | shim.idx | 1754.0M | 1602.8M |
| festive-fermi 39ae4e8 (this branch's base: repeatMate) | shim.idx | 1526.8M | 1478.7M |
| **this branch 67c608f (heavyMate)** | heavy.idx | **1300.1M** (−14.8% vs 39ae4e8) | **1450.5M** (−1.9%) |
| this branch, witnessFirst := true | heavy.idx | 1103.7M | 1190.0M |
- The heavy functions do not show up in the profile. The remaining overhead vs 0e48158 is the proved floor for
  non-repeat leftovers: `lookAt` is 220M (17%) of the NovaSeq run.
- Witness-first (one flag) is below 0e48158 on HiSeq. It unmaps pairs, though: mapped SAM records 3740 → 3108
  (NovaSeq) and 3742 → 3024 (HiSeq).

## SAM vs 39ae4e8 (same 2000 pairs)
Mapped records are identical (NovaSeq 3740 / 3740, HiSeq 3742 / 3742). 3 pairs differ, all unmapped in both runs:
2 NovaSeq + 1 HiSeq pairs that the old forward-only witness missed now answer `repetitiveUnknown` (XB −13 / −12)
instead of `unknown` after the second look (XB −17). `repetitiveUnknown` lines: NovaSeq 42 → 46, HiSeq 18 → 20.

## Not done
- The builder passes are single-threaded; they could be split by hash range over 4 tasks.
- H and M could be read in place from the index bytes instead of copied on every load.
