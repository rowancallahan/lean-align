# What a softer trim threshold would do (measurement only; decision: stays at 25)

Base `fix/fast` f465a57. Only the per-base score constant `Q` of the quality trim was changed (`Phred - Q`, T = Q); `minLength` stays 25.
Scale: 200 000 pairs per set (not 1M). `novaseq_200k` = NovaSeq 2x151; `hg002_200k` = HG002 2x250 (stands in for HiSeq).
`map shim2.idx R1 R2 out.sam 100 1000`, 4 cores (`taskset -c 0-3`), SAM to a real file, warm cache. minibwa `map -t 4`. Script: `Testing/fuzz/trim_threshold.py`.
The 13 slow pairs were not measured for this (stopped on request).

## Proofs: not parametric in 25
The implementation is (`trimReadQ Q`, `ReadTrim.defQ`); the spec side hard-codes 25 in four places:
`Aligner/mapper/ReadTrim.lean` `defQ`, `Spec/Trim.lean:28`, `Proofs/Trim.lean:29` (copy of the spec) and `Proofs/Trim.lean:56` (`baseScoreS`).
Changing `defQ` alone breaks `Proofs.Trim` (`baseScoreS_eq`, omega). Changing all four to T = 20/15/10 builds the whole `lean-align` target (408 jobs, proofs included)
without any proof edit. The binaries were built that way, locally; nothing else was changed and the edits are not on this branch.

## Results (T25 / T20 / T15 / T10)
| | novaseq_200k | hg002_200k |
|---|---|---|
| trimmed length, mean (kept mates) | 148.5 / 150.0 / 150.5 / 150.8 | 231.3 / 239.7 / 246.0 / 248.4 |
| median | 151 / 151 / 151 / 151 | 248 / 249 / 249 / 250 |
| mates < 50 | 0.50 / 0.13 / 0.03 / 0.01 % | 0.47 / 0.06 / 0.00 / 0.00 % |
| mates dropped (< 25) | 0.33 / 0.07 / 0.03 / 0.00 % | 0.49 / 0.03 / 0.00 / 0.00 % |
| pairs mapped | 93.80 / 92.94 / 92.22 / 91.79 % | 93.61 / 91.29 / 86.60 / 84.53 % |
| pairs proper (ours sets 0x2 on every mapped pair) | = mapped | = mapped |
| pairs unique (both XU:Z:unique) | 82.42 / 82.15 / 82.03 / 82.02 % | 84.55 / 81.22 / 75.63 / 73.46 % |
| our unique pairs agreeing with minibwa (same chr, both mates within 300 bp) | 99.99 % each (13-14 elsewhere) | 99.98-99.99 % (36 / 20 / 15 / 15 elsewhere) |
| minibwa: mapped / proper / MAPQ 60 | 99.08 / 97.62 / 85.15 % | 99.57 / 98.06 / 87.57 % |
| wall (warm) / CPU at 4 threads, ours | 6.4, 6.4, 6.1 s / 15.8, 16.4, 14.2 s (T20/15/10; T25 run was cold: 142 s wall, 16.8 s CPU) | 5.8 / 6.9 / 6.9 / 8.3 s; 14.7 / 17.5 / 17.6 / 18.9 s |
| minibwa wall / CPU | 200 s (cold) / 46 s | 27 s / 84 s |

Reading: a softer rule keeps longer reads and drops almost nothing, but it lowers pairs mapped and unique, a lot on 250 bp reads (hg002, T15: -7 points mapped, -9 points unique);
NovaSeq loses little (-0.4 point unique at T15). The placement of pairs that stay unique does not change. No hol-trace P lines (the trace build was not made here).
Per the lead: the threshold stays at 25.
