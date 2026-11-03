## novaseq_200k: 6898 pairs where we give `none` (both mates unmapped) and minibwa maps both mates with MAPQ >= 30

### Primary class (first match: fragment, clip >= 10, trimmed >= 10, indel, small clip, then gave up / errors / unexplained)

| class | pairs |
|---|---|
| fragment | 1785 (25.9%) |
| clip | 1393 (20.2%) |
| trimmed | 1112 (16.1%) |
| indel | 725 (10.5%) |
| smallclip | 151 (2.2%) |
| gaveup | 538 (7.8%) |
| errors | 1194 (17.3%) |
| unexplained | 0 (0.0%) |

### Overlap (a pair counts in every class it has)

| flag | pairs |
|---|---|
| fragment | 1785 (25.9%) |
| clip | 1898 (27.5%) |
| trimmed | 2512 (36.4%) |
| indel | 1073 (15.6%) |
| smallclip | 708 (10.3%) |
| none of the five | 1732 (25.1%) |
| two or more | 2283 (33.1%) |

### Clipped pairs (1898)

clipped mates: 2330 ; clip at the read's 5' end: 513, 3' end: 1652, both ends: 152
clipped bases per clipped mate: 10-19: 503, 20-29: 339, 30-49: 472, 50-74: 594, 75-99: 270, 100-+: 152

Pair score of the ALIGNED part (clipped part excluded), our model; thresholds: -16 = the bound a `none` answer must beat (junkScore), -50 = report floor, -100:

| clipped pairs with aligned-part score | >= -16 | >= -50 | >= -100 | < -100 |
|---|---|---|---|---|
| count | 652 | 1242 | 1792 | 106 |

Rough end-to-end score if the clipped bases were forced in as mismatches at 3 per base (random sequence: 4 x 3/4): >= -16: 0, >= -50: 40, >= -100: 246 of 1898.

### Not clipped

5000 pairs. Aligned score >= -16: 1328, >= -50: 3606, >= -100: 4844.
no-cause pairs (1732): minibwa NM per mate: 0-1: 1275, 2-3: 476, 4-5: 739, 6-7: 466, 8-11: 380, 12-19: 126, 20-+: 2; ours trimmed bases per mate: 0-0: 2163, 1-4: 1024, 5-9: 277, 10-+: 0
fragment class by reason: fragment > 1000: 697, dovetail / containment even without the clipped ends: 483, different chromosome: 426, read-through: proper only once the clipped ends (adapter) are excluded: 158, same strand: 21
dovetail overshoot (bases the forward mate starts after / ends after the reverse mate, aligned part): 1-1: 131, 2-2: 87, 3-4: 41, 5-9: 13, 10-19: 13, 20-49: 18, 50-+: 120 of 483

## Examples (10, spread over the primary classes)

- `A00744:46:HV3C3DSXX:2:1103:10004:31031` **clip**: minibwa chr1:11532824- 13S138M / chr1:11532725+ 151M MAPQ 60/60; NM 7/2; fragment 237; our trimmer removed 41/4 bases; aligned-part pair score -36; ours: `unknown` boundsOnly XB -13
- `A00744:46:HV3C3DSXX:2:1103:10104:28009` **trimmed**: minibwa chr16:3130343- 151M / chr16:3130177+ 147M4S MAPQ 60/60; NM 0/7; fragment 317; our trimmer removed 0/151 bases; aligned-part pair score -28; ours: `None` trimmedAway2 XB None
- `A00744:46:HV3C3DSXX:2:1103:10004:26584` **indel**: minibwa chr2:4405778- 84M30D67M / chr2:4405607+ 151M MAPQ 60/60; NM 30/2; fragment 352; our trimmer removed 0/0 bases; aligned-part pair score -74; ours: `unknown` boundsOnly XB -17
- `A00744:46:HV3C3DSXX:2:1103:10004:32033` **fragment**: minibwa chr9:129164896+ 151M / chr9:129167616+ 133M18S MAPQ 60/60; NM 2/3; fragment None; our trimmer removed 0/0 bases; aligned-part pair score -20; ours: `gaveUp` boundsOnly XB -16
- `A00744:46:HV3C3DSXX:2:1103:10755:29543` **smallclip**: minibwa chr1:55631897+ 151M / chr1:55631934- 149M2S MAPQ 60/48; NM 0/8; fragment 188; our trimmer removed 0/0 bases; aligned-part pair score -32; ours: `unknown` stoppedEarly XB -17
- `A00744:46:HV3C3DSXX:2:1103:10059:34006` **gaveup**: minibwa chr2:190898743+ 151M / chr2:190899188- 151M MAPQ 54/60; NM 1/0; fragment 596; our trimmer removed 0/0 bases; aligned-part pair score -4; ours: `gaveUp` stoppedEarly XB 0
- `A00744:46:HV3C3DSXX:2:1103:10031:35336` **errors**: minibwa chrUn_KI270438v1:104208- 151M / chrUn_KI270438v1:104038+ 151M MAPQ 48/57; NM 3/4; fragment 321; our trimmer removed 0/0 bases; aligned-part pair score -28; ours: `unknown` boundsOnly XB -17
- `A00744:46:HV3C3DSXX:2:1103:28673:22654` **clip**: minibwa chr12:6685116+ 87M64S / chr12:6685501- 34S117M MAPQ 60/53; NM 0/0; fragment 502; our trimmer removed 6/0 bases; aligned-part pair score 0; ours: `gaveUp` boundsOnly XB -13
- `A00744:46:HV3C3DSXX:2:1103:29432:23938` **trimmed**: minibwa chr12:95303137- 151M / chr12:95302785+ 151M MAPQ 60/60; NM 8/11; fragment 503; our trimmer removed 110/9 bases; aligned-part pair score -76; ours: `unknown` boundsOnly XB -1
- `A00744:46:HV3C3DSXX:2:1103:28040:32737` **indel**: minibwa chr2:236868314+ 28M28D123M / chr2:236868522- 151M MAPQ 41/38; NM 31/0; fragment 359; our trimmer removed 1/0 bases; aligned-part pair score -74; ours: `gaveUp` boundsOnly XB 0
