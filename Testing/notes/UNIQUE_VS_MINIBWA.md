# Our uniqueness (XU) vs minibwa c07de5c

lean-align 027ef1e (Aligner code identical to the festive branch head) with the hg38 ic.idx, vs minibwa c07de5c `map -t 4` (release mb index).
SAM written to files. Real: first 200k pairs of the bench release's novaseq_200k and hg002_200k (HiSeq 2x250). Simulated: Testing/benches/sim_pairs.py mason/low/high, seed 1, 100k pairs. 1M pairs not run.
Proper pair = flag 0x2 on both mates. minibwa Q60/Q30 = min MAPQ of both mates (proper pairs). Pair correct (sim) = both mates within 10 bp of true start.

| % of all pairs | NovaSeq | HiSeq |
|---|---|---|
| proper pair, ours | 93.80 | 93.61 |
| proper pair, minibwa | 97.62 | 98.06 |
| ours XU unique | 82.42 | 84.55 |
| minibwa Q60 both | 84.89 | 87.41 |
| minibwa Q>=30 both | 90.93 | 92.29 |
| ours unknown | 11.38 | 9.06 |
| ours not proper | 6.20 | 6.39 |

2x2 counts (ours unique or not x minibwa Q60 or not): NovaSeq 157,212 / 7,627 / 12,576 / 22,585 (U&60, U&not60, notU&60, notU&not60); HiSeq 163,251 / 5,850 / 11,562 / 19,337.
vs Q>=30: NovaSeq U&30 164,050, U&<30 789, notU&30 17,813, notU&<30 17,348; HiSeq 168,569 / 532 / 16,016 / 14,883.
Both unique: same exact position 82.11% (Nova) / 26.72% (HiSeq); within 10 bp 99.25% / 75.57%.
Ours unknown (22,752 / 18,117): minibwa same exact position both mates 27.69% / 7.23%; within 10 bp 49.50% / 25.64%.
minibwa min-MAPQ when within 10 bp: Nova Q60 6915, Q30-59 2335, Q1-29 783, Q0 1230; HiSeq Q60 2720, Q30-59 848, Q1-29 343, Q0 735.
minibwa min-MAPQ over all ours-unknown: Nova Q60 8532, Q30-59 3811, Q1-29 2957, Q0 6790, not proper 662; HiSeq Q60 6971, Q30-59 2664, Q1-29 2357, Q0 5518, not proper 607.

Simulated, pair correct %: mason ours 93.91 / mb 98.03; low 96.60 / 98.26; high 80.87 / 97.98.
By our class (n; ours %; mb %): mason unique 86,604; 100.00; 99.99, unknown 10,017; 72.94; 84.66, not proper 3,379; 0; 87.54. low unique 94,164; 99.99; 99.99, unknown 5,348; 45.62; 69.67, not proper 488; 0; 76.43. high unique 59,278; 99.94; 99.97, unknown 23,814; 90.82; 95.19, not proper 16,908; 0; 94.96.

## Why pairs are not proper (from our tags)
Real NovaSeq 12,409 (6.20%): boundsOnly 10,672 (unknown, XB < -16: 6,880; unknown, XB >= -16: 2,405; repetitiveUnknown: 1,387), trimmedAway 1,304 (mate 2: 1,148; mate 1: 156), stoppedEarly 388, eachMateUnique 45.
Real HiSeq 12,782 (6.39%): boundsOnly 10,247 (unknown XB < -16: 8,291; unknown XB >= -16: 919; repetitiveUnknown: 1,037), trimmedAway 1,923, stoppedEarly 567, eachMateUnique 45.
Simulated high 16,908 (16.91%): boundsOnly 16,594 (unknown XB < -16: 15,423 (+1 XB >= -16); repetitiveUnknown: 1,170), stoppedEarly 312, trimmedAway 2.
Simulated mason 3,379: boundsOnly unknown XB < -16 2,589; repetitiveUnknown 714; stoppedEarly 74; trimmedAway 2. low 488: repetitiveUnknown 231 + 43 stopped, unknown XB < -16 205 + 8, trimmedAway 1.
Truth check (random 1,500 of each boundsOnly / unknown / XB < -16 class, untrimmed reads vs true interval, match 0, mismatch -4, gap -(6+2k)): high 1500/1500 have truth pair score below requiredMapBound (-16 for 150 bp reads), median -38; mason 1500/1500, median -28. Fragment length is never outside 100-1000 (sim clamps 170-900). So these pairs are below the bound by the spec; they are not misses of a pair that scores within it.
Not done: truth check for the repetitiveUnknown and stoppedEarly classes, real-read classes by truth.
