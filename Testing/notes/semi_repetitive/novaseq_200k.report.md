## novaseq_200k: 5257 pairs reach the complete search and are not highly repetitive (fewer than 2 grid seeds at >= 200 occurrences in either mate)

### Outcome of the pair

- unmapped: boundsOnly (bound below the floor = proved none): 4593 (87.4%)
- gave up (places rule), unmapped: 439 (8.4%)
- pair found >= -100: 225 (4.3%)

Our label (XU): unknown: 4818, gaveUp: 439; tier (XT): boundsOnly: 4901, bestUnchecked: 225, stoppedEarly: 123, deepSearchTie: 8

### Max seed occurrence count per mate (over the 25-mer grid seeds, genome both strands)

0-0: 3183, 1-1: 2141, 2-4: 753, 5-9: 537, 10-19: 482, 20-49: 791, 50-99: 459, 100-149: 251, 150-199: 383, 200-+: 1534

### Grid seeds at >= 200 per mate (0 or 1 by selection)

0 seed(s): 8980, 1 seed(s): 1534

### Mate length after trimming

0-49: 595, 50-99: 1031, 100-139: 1167, 140-150: 3595, 151-199: 4126, 200-249: 0, 250-+: 0

### Candidate places within the error cap (hits of mate 1; then mate 2 hits near them)

mate 1: 0-0: 2271, 1-1: 547, 2-4: 238, 5-9: 431, 10-19: 538, 20-49: 878, 50-+: 354
mate 2 near mate 1: 0-0: 3751, 1-1: 319, 2-4: 127, 5-9: 285, 10-19: 295, 20-49: 268, 50-+: 212

### minibwa on the same pairs

MAPQ 60: 2387 (45.4%), MAPQ 1-29: 1017 (19.3%), MAPQ 0: 850 (16.2%), MAPQ 30-59: 579 (11.0%), unmapped/one mate: 424 (8.1%)

minibwa places the pair within 400 bp of ours (both mates): 207 (3.9%); minibwa has XA: 1286 (24.5%)

Outcome x minibwa MAPQ:

| our outcome | pairs | minibwa MAPQ >= 30 | same place | minibwa MAPQ 0 |
|---|---|---|---|---|
| gave up (places rule), unmapped | 439 | 67 | 0 | 285 |
| pair found >= -100 | 225 | 145 | 207 | 27 |
| unmapped: boundsOnly (bound below the floor = proved none) | 4593 | 2754 | 0 | 538 |

### The semi-repetitive subset (max seed occurrence >= 20 in some mate): 2491 (47.4%)

- unmapped: boundsOnly (bound below the floor = proved none): 2013 (80.8%)
- gave up (places rule), unmapped: 354 (14.2%)
- pair found >= -100: 124 (5.0%)

max seed occurrence in the subset: 20-49: 474, 50-99: 298, 100-149: 155, 150-199: 272, 200-+: 1292
mate-1 candidate places in the subset: 0-0: 1081, 1-1: 232, 2-4: 120, 5-9: 159, 10-19: 202, 20-49: 405, 50-+: 292
minibwa MAPQ in the subset: MAPQ 1-29: 765, MAPQ 60: 657, MAPQ 0: 645, MAPQ 30-59: 370, unmapped/one mate: 54

## Examples (first the semi-repetitive pairs, last three are non-repetitive for contrast)

### `A00744:46:HV3C3DSXX:2:1103:30427:24314`
```
mate1 144 bp [s0:9][s1:0][s2:11][s3:20][s4:10]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:3][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 95 candidate places for mate 1 within the cap, 109 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp stoppedEarly
minibwa: chrY:11576021+ 151M / chrY:11576288- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 1 hits 20 places and each hit needs a banded check; 95 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:16685:31203`
```
mate1 151 bp [s0:0][s1:40][s2:21][s3:28][s4:21][s5:15]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:1][s3:0][s4:0][s5:3]
complete search: 130 candidate places for mate 1 within the cap, 15 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp boundsOnly
minibwa: chrUn_KI270754v1:31475+ 151M / chrUn_KI270754v1:31704- 151M  MAPQ 0/0  XA
```
Why expensive: the busiest seed of mate 1 hits 40 places and each hit needs a banded check; 130 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1104:7193:4961`
```
mate1 151 bp [s0:31][s1:27][s2:0][s3:27][s4:27][s5:286]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 116 candidate places for mate 1 within the cap, 127 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  gaveUp stoppedEarly
minibwa: chrY:56703542+ 151M / chrY:56703723- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 1 hits 286 places and each hit needs a banded check; 116 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:24325:35133`
```
mate1  44 bp [s0:22]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:1][s1:1][s2:1][s3:1][s4:1][s5:1]
complete search: 1 candidate places for mate 1 within the cap, 1 for mate 2 near them
ours:    chr17:5220433- 44M / chr17:5220167+ 151M  AS 0+0  unknown bestUnchecked
minibwa: chr17:5220433- 107S44M / chr17:5220167+ 151M  MAPQ 50/60  XA
```
Why expensive: the busiest seed of mate 1 hits 22 places and each hit needs a banded check.

### `A00744:46:HV3C3DSXX:2:1103:18602:33051`
```
mate1 151 bp [s0:0][s1:28][s2:73][s3:43][s4:0][s5:1]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:39][s1:38][s2:34][s3:142][s4:63][s5:0]
complete search: 22 candidate places for mate 1 within the cap, 49 for mate 2 near them
ours:    chr1_KI270709v1_random:11374- 151M / chr1_KI270709v1_random:11272+ 151M  AS -8+-4  unknown bestUnchecked
minibwa: chr1_KI270709v1_random:11374- 151M / chr1_KI270709v1_random:11272+ 151M  MAPQ 0/0  XA
```
Why expensive: the busiest seed of mate 2 hits 142 places and each hit needs a banded check; 22 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:14913:27101`
```
mate1 151 bp [s0:30][s1:41][s2:19][s3:0][s4:5][s5:22]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:25][s1:8][s2:349][s3:0][s4:40][s5:14]
complete search: 24 candidate places for mate 1 within the cap, 45 for mate 2 near them
ours:    chr1:143216744+ 151M / chr1:143216951- 150M  AS -8+-8  unknown bestUnchecked
minibwa: chr1:143216744+ 151M / chr1:143216950- 151M  MAPQ 0/0
```
Why expensive: the busiest seed of mate 2 hits 349 places and each hit needs a banded check; 24 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:29197:22842`
```
mate1 151 bp [s0:0][s1:0][s2:2][s3:0][s4:0][s5:0]   (occurrences per 25-mer grid seed)
mate2 129 bp [s0:0][s1:3][s2:0][s3:20][s4:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr5:49658642+ 10M5D131M10S / chr5:49658601- 62S89M  MAPQ 33/41
```
Why expensive: the busiest seed of mate 2 hits 20 places and each hit needs a banded check.

### `A00744:46:HV3C3DSXX:2:1103:19461:26678`
```
mate1 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:3]   (occurrences per 25-mer grid seed)
mate2 145 bp [s0:11][s1:141][s2:1][s3:0][s4:0]
complete search: 13 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr8:119408566- 151M / chr8:119407609+ 151M  MAPQ 60/60
```
Why expensive: the busiest seed of mate 2 hits 141 places and each hit needs a banded check; 13 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:5014:26052`
```
mate1 148 bp [s0:4][s1:0][s2:1185][s3:0][s4:0]   (occurrences per 25-mer grid seed)
mate2 143 bp [s0:0][s1:0][s2:2][s3:15][s4:0]
complete search: 13 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr2:179247336- 151M / chr18:47666396+ 59S34M58S  MAPQ 60/29
```
Why expensive: the busiest seed of mate 1 hits 1185 places and each hit needs a banded check; 13 candidate places for mate 1 inside the cap.

### `A00744:46:HV3C3DSXX:2:1103:27832:34413`
```
mate1  35 bp [s0:0]   (occurrences per 25-mer grid seed)
mate2  25 bp [s0:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr1:68228886+ * / chr1:68228886- 18S31M102S  MAPQ 0/1  XA
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

### `A00744:46:HV3C3DSXX:2:1104:25907:1548`
```
mate1 147 bp [s0:0][s1:0][s2:0][s3:0][s4:0]   (occurrences per 25-mer grid seed)
mate2 150 bp [s0:3][s1:0][s2:0][s3:0][s4:1][s5:0]
complete search: 0 candidate places for mate 1 within the cap, 0 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr8:138974031- 151M / chr8:138973543+ 151M  MAPQ 60/60
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

### `A00744:46:HV3C3DSXX:2:1104:25970:2253`
```
mate1 151 bp [s0:1][s1:1][s2:1][s3:1][s4:1][s5:0]   (occurrences per 25-mer grid seed)
mate2 151 bp [s0:0][s1:0][s2:0][s3:0][s4:0][s5:0]
complete search: 6 candidate places for mate 1 within the cap, 8 for mate 2 near them
ours:    *:0+ * / *:0+ *  AS None+None  unknown boundsOnly
minibwa: chr9:6870056+ 147M4S / chr9:6870055- 3S148M  MAPQ 60/60
```
Why expensive: no seed is frequent; the cost is the many short or error-rich candidates (small seeds / long trimmed mate).

