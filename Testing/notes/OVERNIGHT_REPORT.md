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
