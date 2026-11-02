# Real reads: lean-align vs minibwa (hg38, NovaSeq 200k and HiSeq 200k)

Ours: `claude/festive-fermi-mf9mo6` head e384063 (quality trimming, capBudget 5000, chunk 20000, n32 kernels), release `shim.idx`
(SHA-256 matches the release; the head accepted it), `lean-align map shim.idx R1 R2 out.sam 100 1000`. minibwa c07de5c built
from lh3/minibwa, `map -t 4`, release index. Lean 4.35 came from the GitHub release zip (release.lean-lang.org is blocked by the proxy).
Script: `Testing/fuzz/real_vs_minibwa.py SET ours.sam mb.sam R1.fq R2.fq`. Full reports and the 20+20+20 raw example records
are in `Testing/notes/real_vs_minibwa/` (`SET.report.md`, `SET.examples.tsv`). No truth: this shows disagreements, not errors.

**Method point that changes the numbers.** We quality-trim mates and print the trimmed SEQ with no `S`. A naive POS comparison
calls 30 591 NovaSeq mates "ours unique, minibwa MAPQ >= 30, different position"; nearly all are a 1-bp trim shift. The script finds the
trimmed SEQ inside the original read, and calls two mates the same place when their M-segment diagonals (POS minus read offset) share one.

## 1. Per-mate classes (percent of 400 000 mates)

| class | NovaSeq | HiSeq |
|---|---|---|
| same pos+strand, same CIGAR | 70.72 | 21.29 |
| same pos+strand, CIGAR differs | 8.40 | 32.28 |
| same alignment diagonal (trim / clip / indel in trimmed part), CIGAR differs | 10.02 | 34.47 |
| different pos, repeats (either MAPQ 0) | 5.78 | 4.78 |
| **different pos, ours unique, minibwa MAPQ >= 30 (alarming)** | **5 mates (0.001)** | **12 mates (0.003)** |
| different pos, other | 7 | 20 |
| mapped by minibwa only | 2.06 | 5.75 |
| mapped by ours only | 0.16 | 0.07 |
| unmapped by both | 0.13 | 0.16 |
| ours degenerate all-insertion | 2.72 (10 872 mates) | 1.19 (4 770) |

HiSeq "CIGAR differs" is large because 2x250 reads are trimmed or clipped often, not because placements differ.
Different-position repeats: minibwa has XA on 7 276 / 6 386 of them in the earlier count; ours is almost always `unknown` there.

**Degenerate all-insertion mates, what minibwa did** (NovaSeq / HiSeq): mapped with MAPQ 60 for 51 % / 50 %, MAPQ 30-59 7 % / 7 %,
MAPQ 1-29 18 % / 19 %, MAPQ 0 14 % / 19 %, unmapped 10 % / 5 %; proper flag 70 % / 79 %; soft-clipped 35 % / 59 %.
So half of our last-resort pairs are reads minibwa maps confidently, the main sensitivity gap, as in the October note.

## 2. Score check at the same place (minibwa recomputed in our model; only where it has no clipping)

| | NovaSeq | HiSeq |
|---|---|---|
| mates at same place | 355 300 | 349 362 |
| minibwa clipped, not comparable | 5 250 (1.5 %) | 24 973 (7.2 %) |
| same query length: minibwa strictly better | 449 (0.16 %) | 170 (0.20 %) |
| same query length: equal | 99.82 % | 99.79 % |
| same query length: ours better | 47 | 12 |
| ours trimmed (shorter query): minibwa strictly better / ours better | 340 / 9 376 | 720 / 80 240 |

"Ours better" with a trimmed query is expected: minibwa scores the extra low-quality bases we dropped. **Every one of the 619 mates
where minibwa is strictly better at the same length is labelled `unknown` by us (never unique or multimapper)**: NovaSeq `boundsOnly` 490
(278 with AS < -100), `stoppedEarly` 297, `eachMateUnique` 28, `deepSearchTie` 3; HiSeq `boundsOnly` 206, `stoppedEarly` 95, `eachMateUnique` 61, `deepSearchTie` 1.
No unique claim is contradicted by a better end-to-end alignment at the same place.

## 3. Pair score AS1+AS2, pairs minibwa maps confidently (both mates, min MAPQ >= 30)

NovaSeq: 182 462 pairs (we map both mates of 98.7 %); HiSeq 184 996 (95.6 %).

| our pair score | NovaSeq pairs (degenerate) | HiSeq pairs (degenerate) |
|---|---|---|
| < -100 | 5 252 (2 827) | 4 129 (1 271) |
| -100 .. -50 | 1 383 (1) | 898 (4) |
| -50 .. -32 | 1 806 (0) | 923 (1) |
| -32 .. -16 | 6 136 | 6 687 |
| >= -16 | 165 499 | 164 204 |

Share of minibwa-confident pairs we map that score < -16 / < -32 / < -50 / < -100: NovaSeq 8.1 / 4.7 / 3.7 / 2.9 %; HiSeq 7.2 / 3.4 / 2.8 / 2.3 %.
**A -50 floor would unmap 6 635 (NovaSeq) and 5 027 (HiSeq) pairs that minibwa maps confidently**, on top of the 2 386 / 8 155 we already miss.
Of those, the below -100 bin is mostly degenerate pairs (54 % NovaSeq, 31 % HiSeq: our "gave up" answers). The -100..-50 and -50..-32
bins are real alignments (almost none degenerate); in them minibwa's own alignment, scored in our model, is also < -50 for 354 of 871 (NovaSeq) and
155 of 366 (HiSeq) unclipped pairs (but over untrimmed reads), and the same place as ours for 59 % / 48 %. Reading: the floor mostly removes
degenerate pairs, but each set has ~1 400 / ~900 real pairs in -100..-50 that minibwa maps and that are partly genuine high-error pairs, partly trimming/clipping artifacts.
Pairs examples: `SET.examples.tsv`, section LOW_PAIR. Caveat: minibwa's score here is over the full read, ours over the trimmed one.

## 4. Examples with explanations

Alarming class (only 5 + 12 mates, all listed in `SET.examples.tsv` section ALARMING). Patterns:
- **Our trimmed mate is short (75-135 bp) and lands on one copy of a segmental duplication, minibwa's full-length read prefers another** (HiSeq
  `10257:52325` both mates: ours chr22_KI270733v1_random, minibwa chr21, whose XA lists our copy; `17914:59681` mate 2: ours 118 bp after trimming 132, minibwa 168M82S 196 bp away,
  XA lists ours; `8802:50180` both mates: ours 16438408, minibwa 14810874 with XA listing ours, minibwa MAPQ 39-41). Trimming removed the bases that tell the copies apart, yet we called it unique. This is the one pattern to look at: a unique claim on a trimmed read.
- **Near-identical repeat copies, minibwa MAPQ only 40-50 with n2 > 1** (NovaSeq `29414:28573`, `5421:23343`): both tools give a proper pair (insert ~300 / ~490); ours has AS -8/-8 and -12/0, minibwa NM 3 on each mate (about -24) at its place, so ours scores at least as well; minibwa's MAPQ shows it is unsure.
- **Different pair (mate 2 anchored elsewhere)**: `16648:42181` mate 1: minibwa pairs it 1 Mb away (TLEN 1 051 047, MAPQ 29), ours proper at 302 bp. Fragment-range (100-1000) difference, not an error.
- **Indel/clip near the start** (NovaSeq `16351:30686`, `13928:25614`, `22959:27477`): trimmed or clipped part holds an indel; 4-24 bp apart; same alignment otherwise. Left in the class because the diagonal match tolerance is the first aligned segment only for these.
- **Adapter/clip at the 3' end** (HiSeq `19478:55738`, `19772:45126`, `20459:61108`, `4517:62498`, `9614:58907`): minibwa soft-clips 13-133 bases, we trim 50-175; positions differ by the clip, same locus. Several also carry an XA.

"minibwa better" (SET.examples.tsv, MINIBWA_BETTER; 20 each): all are `unknown` pairs with large penalties from the unfinished-search tiers
(`boundsOnly`, `stoppedEarly`): ours is a gapped alignment at the right place that is far from optimal (AS -136 / -400 / -264 / -524, a staircase of
1-5 bp indels), while minibwa has one clean indel (for example 69M10D82M, NM 10). Exceptions: HiSeq `12021:48777`, `14237:46779` (label `eachMateUnique`, `unknown`): ours `248M1I1M` AS -8, minibwa `250M` with one mismatch = -4.
These have the same read length and place, so ours is 4 worse: a 1-base insertion at the last base instead of a mismatch. Worth a look if the kernel is meant to be optimal at that
tier (the label is `unknown`, so no proof is violated). Counts: NovaSeq 28 and HiSeq 61 mates with `eachMateUnique` + `unknown` and AS >= -100.

## 5. Not done / caveats

- Disjoint-unique rescoring (both tools unique, disjoint intervals): the class above counts 5 / 12 mates; the genome (3 GB `genome.fa`) was not downloaded, so not rescored.
- minibwa's score uses NM; N bases and clipped mates are not comparable (counts above).
- The release `shim.idx` is from f7ab094; it loaded and ran at e384063 without complaint.

## 6. Rescoring minibwa's placement in our model (alarming class and both-unique disjoint pairs)

Script `Testing/fuzz/rescore_unique.py`; per-pair detail in `Testing/notes/real_vs_minibwa/SET.rescore.md`. In scope: both mates mapped by both tools, ours
`XU:Z:unique`, minibwa MAPQ >= 30 on both mates, and at least one mate whose reference interval is disjoint from minibwa's: **2 NovaSeq pairs, 5 HiSeq pairs**
(the other alarming mates have a partner that is not unique for us or not confident for minibwa, e.g. `16648:42181`, where minibwa's pair is 1 Mb apart at MAPQ 29).
Each mate: our trimmed SEQ aligned end to end (0 / -4 / -(6+2k), ends free in hg38 `genome.fa`, SHA-256 verified) in a window of +-10 (plus minibwa's indel
total) around minibwa's placement; pair proper = opposite strands, outer fragment 100-1000. Sanity: at our own placement the recomputed score is >= our AS (asserted, held for all 14 mates).

**Result: 0 of 7 where minibwa's placement scores >= ours.** All 7 are proper pairs at minibwa's placement and score lower than ours:

| pair | ours | minibwa's placement (our model) | margin | what differs |
|---|---|---|---|---|
| NovaSeq 29414:28573 | -16 | -48 | 32 | near-identical copy ~280 kb away (minibwa MAPQ 48/50, XA); minibwa has 3 mismatches per mate |
| NovaSeq 5421:23343 | -12 | -16 | 4 | tandem copy 9.5 kb away; one mate tied, the other 4 worse (one mismatch) |
| HiSeq 10257:52325 | -22 | -30 | 8 | chr22 KI270733v1_random vs chr21 copy (minibwa MAPQ 38/39, XA lists ours); 1 extra mismatch per mate |
| HiSeq 17914:59681 | -12 | -16 | 4 | mate 2 at a copy 196 bp away (minibwa 168M82S, MAPQ 56, XA lists ours); one mismatch |
| HiSeq 4517:62498 | -16 | -36 | 20 | copy 12 Mb away (minibwa 237M13S / 246M4S, MAPQ 49, XA lists ours) |
| HiSeq 8802:50180 | 0 | -4 | 4 | tandem copy 1.6 Mb away, minibwa MAPQ 39/41; mate 2 tied, mate 1 one mismatch worse |
| HiSeq 9614:58907 | -8 | -32 | 24 | mate 2: 16 clipped bases and 4 mismatches at minibwa's place |

Margins of 4 are one mismatch: ours is only strictly better by a single base in 3 pairs (5421:23343, 17914:59681, 8802:50180), so the unique claim there rests on the trimmed bases.
**Did trimming remove the separating letters?** Scoring the FULL original read at both places (not the trimmed one): in 4 of the 7 pairs minibwa's copy wins on the full read
(sum of both mates): 8802:50180 ours -56 vs minibwa -40; 4517:62498 -160 vs -88; 9614:58907 -90 vs -64; 17914:59681 -188 vs -180 (tie-ish). In 29414, 10257 and 5421 ours wins on the full read too.
So in four pairs we call unique on a trimmed read where the discarded 3' bases (47-175 bases cut, all low quality) point to the other copy. Per our model these claims are correct on the trimmed
read, as the proof states, but their uniqueness depends on the trimming choice; if trimming should not change which copy is called unique, this is where it does.
