# Witness-first: measurements (branch `speed/witness-first`, off ff61781; measurement only)

Spec on main (b7eb931 / 38a5676): `.repetitiveUnknown` needs `found = none` and a mate `highlyRepetitiveIn`
(≥ `gaveUpSeeds = 2` grid seeds with `Genome.occurrences ≥ gaveUpRepeats = 200`, both strands counted). So a
pair may be answered without the router whenever a mate has the witness.

Method:
- `Testing/benches/WitnessBench.lean` (`lake exe witness_bench`, unproved, measurement only) runs the
  witness-first check per mate:
  - grid seeds whose bucket (`hiB − loB`, plus the reverse-complement seed's bucket in `both` mode) is ≥ N;
  - if ≥ 2 such, verify via `lookupPWk` (first N places, in-chromosome count, a lower bound on occurrences)
    until 2 seeds verify.
- Router cost of the caught pairs = shim on all 2000 pairs − shim on the pairs not caught.
- Shim binary `g4n200` = ff61781 with `gaveUpRepeats = 200` (local change, not committed).
- Baseline: festive-fermi 0e48158 (`base0e`).

## 1. Pairs caught (N = 200)
| set | bucket sizes only (upper bound) | verified, forward places | verified, forward + rev-comp |
|---|---|---|---|
| NovaSeq 2k | 381 | 318 (15.9%) | 350 (17.5%) |
| HiSeq 2k | 439 | 349 (17.5%) | 400 (20.0%) |
| NovaSeq 200k | — | 30,861 (15.4%) | 35,543 (17.8%) |
| HiSeq 200k | — | 36,145 (18.1%) | 40,934 (20.5%) |
These pairs become unmapped (`.repetitiveUnknown`, `found = none`), including many the router maps today (Alu /
L1 reads). That is an accuracy decision for Rowan, not a speed detail.

## 2. Ir (2000 pairs)
| | NovaSeq | HiSeq |
|---|---|---|
| 0e48158, all pairs | 960.6M | 1309.4M |
| ff61781 at N = 200, all pairs | 1565.8M | 1682.9M |
| ff61781 at N = 200, pairs not caught (both strands) | 947.2M | 1090.6M |
| 0e48158, the same pairs not caught | 640.1M | 772.0M |
| router + floor work the caught pairs cost today (1565.8 − 947.2; 1682.9 − 1090.6) | 618.6M | 592.4M |
| witness-first check, both strands (`mateRep` inclusive) | 630.3M | 799.8M |
| witness-first check, forward only | 405.8M (skips 331.0M) | 593.5M (skips 543.9M) |
| witness-first estimate (rest + check, both) | ~1577M | ~1890M |
- The check's cost is the verification: `placesLB` (index bucket scans to N genome-checked places plus the
  in-chromosome count), 537M of 630M on NovaSeq. It runs on every mate with ≥ 2 large buckets, caught or not.
- Verification costs about as much as the router work it skips, or more. **Witness-first does not pay with
  scan-based verification.**
- The rest is still ~1.5× the baseline on the same pairs. Non-repeat leftovers still take the second look: NovaSeq
  `lookAtGF` 210M of `alignOneP` 609.5M vs 320.8M at 0e48158; HiSeq 180M of 650.1M vs 369.4M. That cost is the
  proved floor (`.unknown` needs `bestPossibleScore < requiredMapBound`), not repeats.

## 3. Native CPU (200k pairs, user seconds, 4 cores, one warm run each)
| | NovaSeq | HiSeq |
|---|---|---|
| 0e48158 | 16.9 | 25.0 |
| ff61781 at N = 200 | 37.1 | 43.0 |
| ff61781 at N = 200, pairs not caught only | 28.0 | 28.3 |
| 0e48158, pairs not caught only | 10.6 | 13.1 |
| bench, single-threaded (index load + read/trim + check), both / forward | 22.8 / 14.9 | 29.8 / 21.2 |
By Ir, the check is ~70% of the bench, so witness-first native ≈ 28 + 10–15 s on NovaSeq: no better than 37 s.

## 4. Reverse-complement occurrences (item 2)
Counting both strands, as the Spec allows, catches +32 pairs on NovaSeq 2k (318 → 350) and +51 on HiSeq
(349 → 400). It costs a second lookup per seed: check 405.8M → 630.3M on NovaSeq. To prove it,
`count_le_occurrences` needs the rev-comp windows as distinct `(chromosome, start)` occurrences. They are
distinct from the forward ones unless the seed is its own reverse complement, which an odd length (25) rules out.

## 5. A per-key exact occurrence count in the index (item 3), estimate
- What: for every 25-mer with ≥ N occurrences (both strands), a stored count, or a lower bound, which is enough
  for soundness. Looked up by the seed's code (hash table or sorted array plus binary search): O(1) per seed.
- Build: each genome 25-mer has exactly one minimizer, so it lives in exactly one bucket. Counting bucket by
  bucket (gather the windows, sort by code, count runs) needs only per-bucket memory and is ~one genome pass ×
  w windows. Estimate 10–30 min single core for hg38, like the current build.
- Size: unknown without counting. Grid seeds that verify are ~15–20% of reads' seeds. If the distinct
  repetitive 25-mers are 10⁷–10⁸, the table is 0.1–1.2 GB at 12 bytes per entry. A Bloom-style
  "count ≥ N" set is not usable: it has false positives, so it is not a witness.
- Proof: the table becomes part of `buildIndex`. It needs (a) each stored count ≤ `Genome.occurrences` of its
  word (soundness only needs the lower bound), and (b) save/load round-trip, like the existing index parts.
  (a) is a counting proof over the bucket partition: every window counted is a distinct `(chr, start)` equal to
  the word or its reverse complement. That is the same shape as `count_le_occurrences`, lifted from one lookup
  to the whole build. Estimate: a multi-day proof (comparable to `MzBuildOk`), not hours.
- Effect: the check drops from ~630M to the bucket-size pass plus O(1) per seed (~1–2M per 2k pairs). Witness-first
  would then remove ~619M (NovaSeq) / ~592M (HiSeq) at ~zero cost: NovaSeq ≈ 950M ≈ baseline 960.6M, HiSeq
  ≈ 1095M < 1309M. That is the only route here to "at or below baseline", and it unmaps the 17–20% of pairs in §1.

## 6. What witness-first loses (S-G's caveat), and the router-first variant
The caught pairs' answers today (ff61781 at N = 200, 2k subsets, first SAM line per pair, XU tag):
| | NovaSeq, forward | NovaSeq, both strands | HiSeq, forward | HiSeq, both strands |
|---|---|---|---|---|
| caught | 318 | 350 | 349 | 400 |
| today unique and mapped (XU unique) | 200 | 225 | 247 | 280 |
| today mapped, XU unknown | 83 | 84 | 66 | 73 |
| today unmapped (unknown or gaveUp) | 33 | 39 | 35 | 44 |
Witness-first (both strands) would unmap 309 of the 1855 pairs mapped today on NovaSeq (16.7%), 225 of them
proved unique. On HiSeq it is 353 of 1861 (19.0%), 280 unique. The usual case is a repetitive mate whose
partner is unique.

Router first, then the witness for router failures, is what `afterLeftover` does today (`repeatMate` on a
leftover, before the second look). At N = 200 it gives up on 40 NovaSeq / 17 HiSeq pairs (2k) and loses
nothing the router maps. Its cost is the ff61781 N = 200 row of §2: NovaSeq 1565.8M (+605M over 0e48158; of
that `afterLeftover` 519M = second looks 455M + witness 63M), HiSeq 1682.9M (+374M; `afterLeftover` 214M).
Counting reverse-complement occurrences there would add the leftovers caught in the both-strands column but
not the forward one: 6 more NovaSeq and 9 more HiSeq pairs, each skipping a second look of ~8M on average. The
saving is ~50M per set, minus a second lookup per leftover seed. That is small next to the 455M of second looks
on the leftovers that are not repetitive (the proved floor).
