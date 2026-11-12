## novaseq_200k: 200000 pairs, 400000 mates

### 1. Per-mate classification (percent of all mates)

| class | mates |
|---|---|
| same pos+strand, same CIGAR | 282863 (70.72%) |
| same alignment diagonal (POS shifted by our trimming / minibwa clipping / an indel in a trimmed or clipped part), CIGAR differs | 40060 (10.02%) |
| same pos+strand, CIGAR differs | 33618 (8.40%) |
| different pos, repeats (either MAPQ 0) | 23139 (5.78%) |
| degenerate (ours all-insertion) | 10872 (2.72%) |
| mapped by minibwa only | 8246 (2.06%) |
| mapped by ours only | 654 (0.16%) |
| unmapped by both | 536 (0.13%) |
| different pos, other | 7 (0.00%) |
| DIFFERENT pos: ours unique (60), minibwa MAPQ>=30  [ALARMING] | 5 (0.00%) |

- different pos, repeats (either MAPQ 0): 59 of 23139 are on the same chromosome+strand within 50 bp (indel/clip/trim shifts); minibwa has XA on 7171; ours XT/XU: unknown=23125, unique=14

- DIFFERENT pos: ours unique (60), minibwa MAPQ>=30  [ALARMING]: 1 of 5 are on the same chromosome+strand within 50 bp (indel/clip/trim shifts); minibwa has XA on 2; ours XT/XU: unique=5

- different pos, other: 1 of 7 are on the same chromosome+strand within 50 bp (indel/clip/trim shifts); minibwa has XA on 4; ours XT/XU: unique=7

### 1b. Our degenerate all-insertion mates: what minibwa did

10872 mates (5436+ pairs). minibwa: mapped, MAPQ 0: 1501 (13.81%), mapped, MAPQ 1-29: 1929 (17.74%), mapped, MAPQ 30-59: 778 (7.16%), mapped, MAPQ 60: 5570 (51.23%), unmapped: 1094 (10.06%)
minibwa has XA on 1413 (13.00%); proper flag 7580 (69.72%); clipped 3771 (34.69%).

### 2. Score check: mates at the same place (same pos+strand or same diagonal), minibwa unclipped

356541 mates at the same place.

| group | minibwa strictly better | equal | ours better |
|---|---|---|---|
| same query length (283822) | 818 (0.29%) | 282918 (99.68%) | 86 (0.03%) |
| ours trimmed/shorter query (67098) | 573 (0.85%) | 56965 (84.90%) | 9560 (14.25%) |

minibwa clipped, not comparable: 5621 (1.58%).
Gain (minibwa score - ours, same query length) histogram: +2: 14, +4: 30, +6: 9, +8: 20, +10: 16, +12: 7, +14: 13, +16: 6, +18: 17, +20: 8, +22: 12, +24: 10

minibwa strictly better, same query length: by our XU / XT / score: ('unknown', 'boundsOnly', 'degenerate-like: AS<-100')=278; ('unknown', 'boundsOnly', 'AS>=-100')=212; ('unknown', 'stoppedEarly', 'degenerate-like: AS<-100')=173; ('unknown', 'stoppedEarly', 'AS>=-100')=124; ('unknown', 'eachMateUnique', 'AS>=-100')=28; ('unknown', 'deepSearchTie', 'AS>=-100')=3
Note: "ours better" or "minibwa better" with same query length at the same place both indicate scoring/NM-convention issues if frequent; an optimal end-to-end aligner never loses at the same placement.

### 3. Pair score AS1+AS2 where minibwa maps the pair confidently (both mapped, min MAPQ >= 30)

minibwa confident pairs: 182462; we map both mates of 180076 (98.69%); unmapped by us: 2386.

| our pair score | pairs | of which our pair degenerate | same place as minibwa (both mates) | minibwa unclipped both, its score in our model < -50 |
|---|---|---|---|---|
| [-inf, -100) | 5252 | 2827 | 928 | 677 of 3198 unclipped |
| [-100, -50) | 1383 | 1 | 1012 | 354 of 871 unclipped |
| [-50, -32) | 1806 | 0 | 1574 | 246 of 1300 unclipped |
| [-32, -16) | 6136 | 0 | 5844 | 135 of 5060 unclipped |
| [-16, 1) | 165499 | 0 | 165338 | 240 of 162712 unclipped |

Cumulative over minibwa-confident pairs that we map: score < -16: 14577 (8.09%), score < -32: 8441 (4.69%), score < -50: 6635 (3.68%), score < -100: 5252 (2.92%)
A floor of -50 would unmap 6635 pairs that minibwa maps with MAPQ>=30 (plus the 2386 we already do not map).
minibwa's own pair score in our model (unclipped on both mates, 174151 (95.45%) of confident pairs): < -16: 11374, < -32: 4483, < -50: 1993, < -100: 126.

Examples of pairs below the floor: see novaseq_200k.examples.tsv (section LOW_PAIR).
