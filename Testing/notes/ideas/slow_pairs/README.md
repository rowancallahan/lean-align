# Slow pairs (hiseq5m = first 5M pairs of GIAB HG002 D1_S1_L001 2x250, see BENCH_SETUP.md)

Each slowN_R1.fq / slowN_R2.fq is ONE pair; mapping it alone (index ic.idx, 1 core, load subtracted) takes:

| pair | abs pair index in hiseq5m | festive e96862d | mapfiles 64ae73f | SAM |
|---|---|---|---|---|
| slow1 | 2,538,239 | 55.3 s | 59.0 s | chr1:25214717 25M / chr1:25215227 29M, MAPQ 0, XU unknown, XT bestUnchecked (festive) |
| slow2 | 2,468,894 | 5.5 s | 5.7 s | chr1:84052254 30M / 84052361 26M, MAPQ 0, XU unknown, bestUnchecked |
| slow3 | 929,449 | 3.1 s | 3.1 s | both mates unmapped (flags 77/141), XB -1, XU unknown, XT boundsOnly |

Typical pair: about 1 ms. slow1 is an A-rich/low-complexity read (R1 starts with 26 A), both mates end up clipped to 25M/29M.
These are the jobs the hol-trace saw as 55 s / 7 s / 4.6 s (trace job idx 166/161/66 = chunks 158/154/58 of 16000 pairs).
Exact SAM lines and times: timings_and_sam.txt. Found by ddmin on the pairs of the chunks (a 2-pair file A+B was slow, then A alone).
