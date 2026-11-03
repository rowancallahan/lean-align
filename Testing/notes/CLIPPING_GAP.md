# The clipping gap: pairs we give `none` and minibwa maps (MAPQ >= 30 on both mates), real reads

Data: the debug-build SAMs of the semi-repetitive run (`speed/gaveup2-fast` ff61781 with `gaveUpRepeats = 200`, local only; the two answers differ from the head's only for repeat pairs given up on earlier), NovaSeq 2x151 and HiSeq 2x250, 200k pairs each; minibwa c07de5c `-t 4`.
Script `Testing/fuzz/clipping_gap.py`, full reports in `Testing/notes/clipping_gap/`. Population: ours has both mates unmapped (`none`) and minibwa maps both mates with MAPQ >= 30:
**NovaSeq 6 898 pairs, HiSeq 7 637 pairs** over the whole set. (The 2 821 and 1 386 quoted earlier were the part of these that reached the complete search in the semi-repetitive run; the rest were answered earlier, mostly by the repeat rule or the router's bound.)
Everything is computed from minibwa's alignment and the original FASTQ; we have no alignment for these pairs. "Our model": match 0, mismatch -4, gap of k -(6+2k).

## Why we don't map them (primary class, first match in this order)

| class | meaning | NovaSeq | HiSeq |
|---|---|---|---|
| fragment | not a proper pair in the Spec's sense (see below) | 1 785 (25.9 %) | 1 160 (15.2 %) |
| clip | minibwa soft-clips >= 10 bases in some mate | 1 393 (20.2 %) | 3 235 (42.4 %) |
| trimmed | our trimmer removed >= 10 bases of a mate (or the whole mate) | 1 112 (16.1 %) | 2 139 (28.0 %) |
| indel | a mate with >= 2 gap events or >= 5 gap bases | 725 (10.5 %) | 525 (6.9 %) |
| small clip | minibwa clips 1-9 bases | 151 (2.2 %) | 59 (0.8 %) |
| gave up | none of those, our label is gaveUp (places / repeat rule) | 538 (7.8 %) | 53 (0.7 %) |
| errors | none of those, minibwa's alignment scores < -16 in our model (too many mismatches for the bound a `none` must beat) | 1 194 (17.3 %) | 466 (6.1 %) |
| unexplained | alignment >= -16 end to end and we still say none | 0 | 0 |

Overlap (a pair counts in every class it has): clip 27.5 % / 53.0 %, trimmed 36.4 % / 76.6 %, indel 15.6 % / 30.2 %; two or more classes 24.5 % / 65.5 %. On HiSeq most pairs have several causes at once (long 2x250 reads with a poor 3' tail: minibwa clips it, our trimmer cuts it, and the rest of the read has an error or two).

**The fragment class by reason** (NovaSeq / HiSeq): fragment > 1000: 697 / 38; different chromosome: 426 / 273; same strand: 21 / 22; **dovetail or containment even without the clipped ends: 483 / 543**; **read-through, proper only once the clipped ends (adapter) are excluded: 158 / 284**.
Dovetail overshoot (bases the forward mate starts after, or ends after, the reverse mate, aligned part): 1 base: 131 / 160, 2 bases: 87 / 70, 3-4: 41 / 56, 5-9: 13 / 18, 10-19: 13 / 12, 20-49: 18 / 23, 50+: 120 / 179. So over 40 % of the dovetails are 1-2 bases past each other: the properness rule has slack 0 (`dovetailSlack`), and minibwa places the mates a base apart.

## Clipped pairs (clip >= 10 bases in some mate): 1 898 NovaSeq, 4 045 HiSeq

- Clipped mates: 2 330 / 5 206. At the read's 3' end: 1 652 / 4 048; 5' end: 513 / 702; both ends: 152 / 448. Clipped bases per clipped mate: 10-19: 503 / 871, 20-29: 339 / 565, 30-49: 472 / 943, 50-74: 594 / 903, 75-99: 270 / 695, 100+: 152 / 1 229.
- **Pair score of the aligned part (clipped part excluded, our model):** >= -16: 652 / 639; >= -50: 1 242 / 1 529; >= -100: 1 792 / 2 973; < -100: 106 / 1 072. So excluding the clip would pass the -100 floor for 94 % of the NovaSeq clipped pairs and 74 % of the HiSeq ones; but only 34 % / 16 % would pass the -16 bound that a `none` answer must beat (a pair at >= -16 cannot be `none`), and 66 % / 37 % the -50 floor. The HiSeq pairs mostly fail because the aligned part itself carries errors, tails of 100+ clipped bases, and indels.
- If the clipped bases were forced in end to end as mismatches (about 3 per base on random sequence) almost none of them pass: >= -50: 40 / 19, >= -100: 246 / 228 of the clipped pairs. So end-to-end alignment cannot rescue them; clipping (a local alignment) or adapter removal is the only route.
- The 3' bias (71 % / 78 % of clips at the 3' end) is the signature of adapter read-through and quality decay, not of structural variation.

## Not clipped (5 000 NovaSeq / 3 592 HiSeq pairs)

Aligned score >= -16: 1 328 / 325; >= -50: 3 606 / 1 877; >= -100: 4 844 / 3 019. These are the fragment, indel, trimmed and error-rich pairs: no clip would help them, but a dovetail slack, a looser fragment range or a different handling of mismatches would for some.

## What it means for Rowan's decision (local alignment / clipping)

1. Clipping alone explains a fifth (NovaSeq) to a half (HiSeq) of these `none` pairs, and for the NovaSeq clipped pairs excluding the clip passes the -100 floor in 94 %; the read-through adapter pairs (158 / 284) are a special case a plain adapter trimmer might remove.
2. **A dovetail slack of 1-2 bases would admit about 220 NovaSeq and 230 HiSeq of these pairs** without any clipping; that is a setting (`dovetailSlack`) rather than a new alignment mode.
3. Another 18 % / 6 % are error-rich pairs (minibwa's own alignment has 4-9 mismatches per mate): the -16 bound, not the search, is why we say `none`.
4. Our trimmer removes the whole mate for some good reads (example 2: a 151 bp mate with 7 mismatches in 147 trimmed away entirely, `trimmedAway2`).

## Examples (10 each; `ours:` is our label and bound XB)

NovaSeq:

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

HiSeq:

- `HISEQ1:93:H2YHMBCXX:1:1116:10003:51861` **clip**: minibwa chr11:88527964+ 250M / chr11:88528165- 10S240M MAPQ 60/60; NM 4/9; fragment 441; our trimmer removed 43/50 bases; aligned-part pair score -52; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:10014:41435` **trimmed**: minibwa chr17:26619352- 250M / chr17:26619142+ 245M5S MAPQ 53/48; NM 8/8; fragment 460; our trimmer removed 1/40 bases; aligned-part pair score -64; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:10056:55965` **indel**: minibwa chr18:33829386+ 86M7D164M / chr18:33829459- 13M7D237M MAPQ 60/60; NM 7/7; fragment 330; our trimmer removed 0/1 bases; aligned-part pair score -40; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:10000:56051` **fragment**: minibwa chr4:113443869+ 52M4D78M2D48M5D21M3D28M23S / chr4:113443868- 11S53M4D78M2D48M5D21M3D39M MAPQ 60/60; NM 18/18; fragment 276; our trimmer removed 49/12 bases; aligned-part pair score -136; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:10000:43832` **smallclip**: minibwa chr3:93470434+ 250M / chr3:93470450- 9S241M MAPQ 60/60; NM 14/13; fragment 257; our trimmer removed 0/9 bases; aligned-part pair score -108; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:11194:44133` **gaveup**: minibwa chr13:80916731- 250M / chr13:80916404+ 250M MAPQ 48/60; NM 2/1; fragment 577; our trimmer removed 4/2 bases; aligned-part pair score -12; ours: `gaveUp` boundsOnly XB 0
- `HISEQ1:93:H2YHMBCXX:1:1116:10018:56250` **errors**: minibwa chr6:148782163+ 88M1I161M / chr6:148782204- 47M1I202M MAPQ 60/60; NM 3/4; fragment 290; our trimmer removed 1/0 bases; aligned-part pair score -36; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:19540:42649` **clip**: minibwa chr11:56707204- 64M3D7M12I13M1D83M1I15M55S / chr11:56707077+ 51S39M3D36M1D7M2D4M3I6M3D91M13S MAPQ 52/53; NM 33/27; fragment 419; our trimmer removed 0/4 bases; aligned-part pair score -236; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:19024:60901` **trimmed**: minibwa chr12:68538633- 133M11D117M / chr12:68538436+ 198M1I51M MAPQ 60/60; NM 12/3; fragment 458; our trimmer removed 0/14 bases; aligned-part pair score -48; ours: `unknown` boundsOnly XB -17
- `HISEQ1:93:H2YHMBCXX:1:1116:18445:57855` **indel**: minibwa chr1:194267565+ 100M18I132M / chr1:194267665- 9S241M MAPQ 60/60; NM 19/1; fragment 341; our trimmer removed 0/3 bases; aligned-part pair score -50; ours: `unknown` boundsOnly XB -17
