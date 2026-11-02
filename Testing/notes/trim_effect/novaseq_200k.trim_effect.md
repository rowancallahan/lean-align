## novaseq_200k: 200000 pairs, trimming vs no trimming (same shim otherwise)

| | trimming | no trimming |
|---|---|---|
| both mates mapped (incl. all-insertion) | 195609 (97.80%) | 188215 (94.11%) |
| mapped, not degenerate | 190173 (95.09%) | 185930 (92.97%) |
| unique | 163877 (81.94%) | 163024 (81.51%) |
| unmapped mates (trimmed away entirely, or no result) | 8782 (2.20%) of mates | 23570 (5.89%) of mates |
| share of all mapped incl. degenerate pairs with pair score < -50 | 12431 (6.36%) | 10579 (5.62%) |
| share of non-degenerate mapped pairs with pair score < -50 | 7000 (3.68%) | 8294 (4.46%) |
| share of all mapped incl. degenerate pairs with pair score < -100 | 9971 (5.10%) | 7439 (3.95%) |
| share of non-degenerate mapped pairs with pair score < -100 | 4568 (2.40%) | 5154 (2.77%) |

(no-trim scores are over the full reads, trimmed scores over the kept bases, so score shares are not like for like.)

### Unique pairs

| class | pairs |
|---|---|
| unique in both builds, same place | 162050 (81.03%) |
| unique in both builds, different place | 0 (0.00%) |
| unique only with trimming | 1827 (0.91%) |
| unique only without trimming | 974 (0.49%) |

Only with trimming: the no-trim build says {'unmapped/degenerate': 438, 'unknown': 1389}. Only without trimming: the trim build says {'unknown': 921, 'unmapped/degenerate': 53}.
No-trim tier for "only with trimming": {'boundsOnly': 1581, 'stoppedEarly': 241, 'eachMateUnique': 2, 'deepSearchTie': 3}; trim tier for "only without trimming": {'boundsOnly': 804, 'stoppedEarly': 156, 'deepSearchTie': 7, 'eachMateUnique': 7}.

### Unique in both builds, different place: 0 pairs (FULL-read score at each build's placement, both mates summed; end to end, 0/-4/-(6+2k))


Verdicts: {}

unique only with trimming: 1827 pairs; the other build maps 1389 of them (non-degenerate), same place for 1321, different place for 68.

unique only without trimming: 974 pairs; the other build maps 921 of them (non-degenerate), same place for 824, different place for 97.
