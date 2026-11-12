## novaseq_200k: trimmer overcut vs minibwa

Replica check: my best-window replica (Q=25) equals the shim's kept window on 379701 of 400000 mates (94.93 %); the rest are adapter cuts (`AdapterTrim.cutTruSeq`) and `dropShort`, which the replica does not do.

**Overcut mates** (cut >= 30 bases or the whole mate; minibwa MAPQ >= 30; >= 30 aligned bases in the cut region with <= 5 % mismatches): **673** mates in 660 pairs, of 400000 mates.

- whole mate cut away: 42; partial cuts: 631 (5'/3' end: 3': 375, 5'3': 212, 5': 44)
- bases cut per overcut mate: 30-49: 278, 50-74: 194, 75-99: 94, 100-149: 65, 150-199: 42, 200-+: 0
- mean Q of the cut bases: 0-9: 0, 10-14: 2, 15-19: 33, 20-24: 589, 25-29: 10, 30-34: 14, 35-+: 25
- mismatch rate of minibwa in the cut region: 0-0: 111, 1-1: 49, 2-2: 165, 3-3: 140, 4-4: 187, 5-+: 21 (percent)
- largest Q that would keep >= 90 % of the cut bases (current Q = 25): Q=25: 11, Q=24: 170, Q=23: 111, Q=22: 85, Q=21: 57, Q=20: 47, Q=19: 45, Q=18: 30, Q=17: 29, Q=16: 13, Q=15: 15, Q=14: 9, Q=13: 10, Q=12: 2, Q=10: 9, Q=None: 30

Pairs affected: 660 (0.33 % of pairs).

### Sample of overcut mates

- `A00744:46:HV3C3DSXX:2:1103:10104:28009` mate2: length 151, cut 151 (whole mate) at 3', mean Q of the cut bases 23.2, minibwa MAPQ 60, 7/147 mismatches in the cut region, would be kept at Q=21
- `A00744:46:HV3C3DSXX:2:1103:13639:30592` mate2: length 151, cut 75 at 3', mean Q of the cut bases 21.1, minibwa MAPQ 60, 3/75 mismatches in the cut region, would be kept at Q=18
- `A00744:46:HV3C3DSXX:2:1103:17445:33176` mate2: length 151, cut 87 at 5'3', mean Q of the cut bases 21.4, minibwa MAPQ 41, 2/43 mismatches in the cut region, would be kept at Q=20
- `A00744:46:HV3C3DSXX:2:1103:21856:36871` mate2: length 151, cut 59 at 3', mean Q of the cut bases 21.1, minibwa MAPQ 60, 1/50 mismatches in the cut region, would be kept at Q=20
- `A00744:46:HV3C3DSXX:2:1103:26702:35399` mate2: length 151, cut 151 (whole mate) at 3', mean Q of the cut bases 19.7, minibwa MAPQ 60, 2/44 mismatches in the cut region, would be kept at Q=12
- `A00744:46:HV3C3DSXX:2:1103:30734:25097` mate2: length 151, cut 38 at 3', mean Q of the cut bases 24.9, minibwa MAPQ 60, 0/38 mismatches in the cut region, would be kept at Q=24
- `A00744:46:HV3C3DSXX:2:1103:32904:29606` mate2: length 151, cut 56 at 5', mean Q of the cut bases 35.3, minibwa MAPQ 60, 2/56 mismatches in the cut region, would be kept at Q=None
- `A00744:46:HV3C3DSXX:2:1103:6334:31219` mate2: length 151, cut 118 at 5'3', mean Q of the cut bases 21.2, minibwa MAPQ 60, 0/33 mismatches in the cut region, would be kept at Q=16
- `A00744:46:HV3C3DSXX:2:1104:13440:2566` mate2: length 151, cut 93 at 5', mean Q of the cut bases 22.0, minibwa MAPQ 60, 2/43 mismatches in the cut region, would be kept at Q=22
- `A00744:46:HV3C3DSXX:2:1104:26765:4539` mate2: length 151, cut 151 (whole mate) at 3', mean Q of the cut bases 23.5, minibwa MAPQ 50, 0/32 mismatches in the cut region, would be kept at Q=22
