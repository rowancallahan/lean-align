# Does our trimmer cut away bases minibwa aligns well? (NovaSeq 2x151, HiSeq 2x250, 200k pairs, real reads)

Script `Testing/fuzz/trim_overcut.py`; full reports with 10 sample mates each in `Testing/notes/trim_overcut/`. SAMs from the ff61781 build (adapter cut + quality window + `dropShort`; the trimming is the same as on the festive-fermi head).
Our kept window = our SAM SEQ located inside the original read. **Overcut mate**: we cut the whole mate or >= 30 bases of it, minibwa maps the mate with MAPQ >= 30, and in the cut region minibwa has >= 30 aligned bases with <= 5 % mismatches against hg38 (computed from its CIGAR and the reference, not from NM).
The quality trimmer is `ReadTrim.trimRead = trimReadQ defQ`, `defQ = 25`: the kept window is the one maximizing the sum of (Q_i - 25); it is a single constant. My Python replica of that window matches the shim on 94.9 % (NovaSeq) / 96.0 % (HiSeq) of mates; the rest are cut further by the adapter cutter (`cutTruSeq`) or `dropShort`.

| | NovaSeq | HiSeq |
|---|---|---|
| overcut mates (of 400 000) | **673** (0.17 %) | **23 726** (5.9 %) |
| pairs with an overcut mate | 660 (0.33 % of pairs) | 21 992 (11.0 % of pairs) |
| whole mate cut away | 42 | 181 |
| partial cuts: 3' only / both ends / 5' only | 375 / 212 / 44 | 20 927 / 2 614 / 4 |
| bases cut per mate: 30-49 / 50-74 / 75-99 / 100-149 / 150+ | 278 / 194 / 94 / 65 / 42 | 11 575 / 6 814 / 2 611 / 1 634 / 1 092 |
| mean Q of the cut bases: < 20 / 20-24 / 25+ | 35 / 589 / 49 | 6 453 / 17 246 / 27 |
| minibwa mismatch rate in the cut region: 0 % / 1-2 % / 3-4 % / 5 % | 111 / 214 / 327 / 21 | 5 044 / 8 219 / 10 009 / 454 |

Quality profile: the cut bases are mostly **mean Q 20-24** (88 % NovaSeq, 73 % HiSeq), i.e. just below the Q = 25 cut, not junk: minibwa's real mismatch rate there is 0-4 %. (Q20-24 would predict 0.4-1 % errors; the 2-4 % seen includes true variants and minibwa's own clips at the boundary.)
**Trim threshold that would keep >= 90 % of the cut bases** (largest Q for which the best window covers them):
- NovaSeq: Q = 24: 170 mates, 23: 111, 22: 85, 21: 57, 20: 47, 19-10: 162, Q = 25: 11, never (the cut is a 5' or adapter cut that no Q reaches): 30.
- HiSeq: Q = 24: 1 030, 23: 1 134, 22: 1 333, 21: 1 715, 20: 1 844, 19: 1 956, 18: 2 191, 17: 2 348, 16: 2 592, 15: 2 508, 14: 2 492, 13: 1 374, <= 12: 1 189, never: 8, Q = 25 (kept only by adapter or length rules): 12. Counting the mates each setting would keep: Q = 20 keeps 7 068 of the 23 726 overcut HiSeq mates (30 %), Q = 15 keeps 18 663 (79 %); NovaSeq Q = 20 keeps 481 of 673 (71 %), Q = 15 keeps 613 (91 %). Most HiSeq mates need Q 14-18.
- 3' tails dominate (HiSeq 88 % 3' only), which is the ordinary quality decay of 2x250 reads.

## A gentler `defQ`: measured (festive 39ae4e8, local edit of `ReadTrim.defQ` only, never pushed; one run each, 4 cores)

Raw lines in `Testing/notes/trim_overcut/defq_runs.log`, counts by `Testing/fuzz/defq_measure.py`. "mapped" = both mates mapped; unique = both mates `XU:Z:unique`; repetitiveUnknown (`gaveUp`) and all-insertion pairs are 0 on this head, so unmapped = `none`.

| set | defQ | mapped | unique | unmapped | pairs < -50 | pairs < -100 | user CPU (s) |
|---|---|---|---|---|---|---|---|
| NovaSeq | 25 (now) | 187 599 | 164 839 | 12 401 | 2 793 | 0 | 30.3 |
| NovaSeq | 20 | 185 878 (-1 721) | 164 292 (-547) | 14 122 | 3 865 | 0 | 31.9 |
| NovaSeq | 15 | 184 445 (-3 154) | 164 061 (-778) | 15 555 | 3 874 | 0 | 33.0 |
| HiSeq | 25 (now) | 187 231 | 169 101 | 12 769 | 2 361 | 0 | 28.2 |
| HiSeq | 20 | 182 588 (-4 643) | 162 439 (-6 662) | 17 412 | 4 189 | 0 | 34.1 |
| HiSeq | 15 | 173 211 (-14 020) | 151 258 (-17 843) | 26 789 | 6 027 | 0 | 30.9 |

**A lower defQ (keeping more bases) is worse on every count**: fewer pairs mapped and unique, more pairs below -50, and no CPU saving (user CPU is within the run-to-run spread, one run each; the wall and total CPU of the first run include a cold index load).
Why: the shim aligns end to end under the -4 per mismatch score and gives `none` when the best pair is below the -16 bound. The extra bases that minibwa aligns "well" (0-4 % mismatches) still carry 1-4 mismatches over 30-130 bases, i.e. -4 to -16 per mate, which pushes pairs under the bound; trimming them gave a pair that scores. So the overcut finding above is real (minibwa aligns those regions), but it is not recoverable by lowering defQ under the current end-to-end scoring. What would recover them is local alignment (clipping, scored like minibwa) or a clip penalty, not a gentler trimmer. The opposite direction (a higher defQ) was not run.
