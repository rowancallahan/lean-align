# Index tricks for semi-repetitive read pairs (comparison, 2026-11-03)

Question: pairs whose 25-letter seeds hit tens to a few hundred places, or whose only unique seed is spoiled by an error, so the proved complete search checks many candidates.
Frame: the Spec does not change; a trick only changes which candidates are tried, every answer is still checked by the proved aligner. A trick needs
**(a) soundness of the lookup** (what it returns really occurs; we already do this with a runtime checker, `Mz.lookupSeed_mem`, `indexOk`) and, for the "no good pair" bounds, **(b) a completeness guarantee** (pigeonhole style).
Not run on real examples: `SEMI_REPETITIVE_EXAMPLES.md` (branch `docs/semi-repetitive`) was not read; no experiments were done for this note. Numbers are either from existing repo notes (named) or derived arithmetic (marked *derived*).

## What the repo already has (so this is not from scratch)

- The proof framework `SeedSketch` (`Aligner/mapper/SketchMapper.lean`, `.../MapperSketch.lean`, notes `Testing/benches/seed_schemes_notes.txt`): a seed scheme is usable if "an exact match of length >= L shares a key at a computable offset" (`conserved` + `nonempty`).
  Proved for: k-mers, **any** minimizer order and every function of the L-letter window (`windowSketch`; includes mod-minimizer, double-decycling and similar), **closed** syncmers (`closedSyncmer_hits`: every 2k-s-1 letters hold one). **Open** syncmers measured and rejected (17.4 % of read seeds have none). Spaced seeds and strobemers: "not done".
- Today's index: k=22 minimizers over the 25-letter seed, 5-byte slots, 4 x (2^26+1) bytes of bucket offsets, packed genome included, **5.3 GB** (budget < 8 GB, so **about 2.7 GB** free). From the slot size, *derived*: (5.3 - ~0.8 genome - 0.27 buckets) / 5 B ~ 0.84e9 slots ~ 0.27 per base.
- Pigeonhole in use: `exists_clean_seed_amongE`: P penalty -> floor(P/4)+1 disjoint seeds, one is clean (`DEEP_CAPS.md`, table: P=16 -> 5 seeds; 25 letters only up to P~23 at 150 bp).
- Measured on hg38 (`VARIABLE_SEEDS.md`): 16.8 % of positions have no unique substring up to 32 letters; 25-mer seeds average 690 hits, median 1, p99 13.5k; a unique substring is not proof of the right locus (up to ~4 % of mates are pinned to a wrong copy by a unique 24-32-mer).

## Per trick

**1. Closed syncmers** (Edgar 2021, PeerJ [10.7717/peerj.10805](https://doi.org/10.7717/peerj.10805)).
Idea: a k-mer is kept if its smallest s-mer is at its first or last position; selection depends on the k-mer alone, so the same k-mer is chosen in read and genome, and mutations in flanking letters cannot delete it. Every 2k-s-1 letters hold one (proved here).
Buys: no fewer candidates per seed (it is a sampling, not a filter); its use is that all syncmers inside a clean seed are conserved, so we can pick the one with the smallest bucket (repo measured: 0.27-0.15 per base, 35-50 % slower than minimizers in the Lean prototype).
Memory: density ~ 2/(k-s+1) -> 0.15-0.27/base = roughly today's size or smaller (3.1e9 x 0.2 x 5 B ~ 3.1 GB, *derived*).
Proof: sound and complete, already proved (`closedSyncmer_hits`); needs only the checker. Open syncmers: no usable bound.

**2. Minimizer variants** (mod-minimizer, double-decycling, frequency-weighted orders; Roberts 2004, Schleimer 2003; as cited in `seed_schemes_notes.txt`).
Idea: change the order or selection rule only. Buys: **the frequency-weighted order** (k-mers in crowded buckets sort last) directly cuts bucket entries per lookup, the closest match to "seeds with tens-hundreds of hits"; repo notes report it reduces scanned entries; others only change density (at L=25, (w,k)=(7,19): random 0.25, mod-minimizer 0.177 measured, lower bound ~0.154; from `seed_schemes_notes.txt`).
Memory: at or below today's. Proof: free for every window function (proved). Note: a weighted order needs the genome counts at build time and the order is part of what the checker verifies (bucket content is checked, not the order).

**3. Variable/shorter k-mers kept only where needed (small second index), longer k-mers in specific places.**
Idea: seeds that hit >= N places get a second key made of 40-50 letters (or a context check) instead of more candidates. Two forms:
(a) *Stored context / longer keys*: store genome letters around each entry and compare under a mask before touching the genome: a pure **filter**, completeness unchanged (`lettersAgree_complete` proved; repo measured genome checks fall to ~true occurrences). Costs spare key bits only.
(b) *Second index of 50-mers (or 32-mers) only at positions whose 25-mer is heavy*: positions in repeats are ~17 % of the genome (no unique substring <= 32), i.e. ~0.53e9 positions; at 5 B/slot and density 1: ~2.6 GB (*derived*, just under the free 2.7 GB), at density 0.3: ~0.8 GB. A 50-mer split in two halves gives "a read with <= 1 error has a clean half" (repo idea in `EXPERIMENTS_NEXT.md`).
(c) *Shorter seeds for deeper caps*: contiguous 21/18-mers keep the proved pigeonhole (`DEEP_CAPS.md`) but have 2.2x/4.2x more hits and ~5-6 GB; only as a second small index for pairs that failed pass 1.
Buys: (a)+(b) fewer candidates AND the bound stays provable if the heavy-place rule is itself checked ("positions not in the second index have a unique-enough 25-mer", a checkable property). Proof: (a) done; (b) needs a new lookup theorem + checker like `Mz`; the pigeonhole argument is the existing one with 2 seeds of 50 letters (e <= 1 spoiled seed).

**4. Spaced seeds** (PatternHunter, Ma, Tromp, Li 2002, [10.1093/bioinformatics/18.3.440](https://doi.org/10.1093/bioinformatics/18.3.440); deterministic multi-seed filters: Burkhardt and Karkkainen 2003, "Better filtering with gapped q-grams", Fund. Inform., cited from memory).
Idea: the key is the letters at a fixed pattern of positions (e.g. 11 of 18), so hits at nearby offsets are less correlated and a pattern tolerates mismatches at its skipped positions.
Buys: higher sensitivity per index (probabilistic), **not** fewer candidates: the key is as specific as a contiguous seed of the same weight. For semi-repeats it helps the "unique seed spoiled by one error" case only if a second pattern is indexed.
Memory: one full index per pattern, ~today's size each (>= 2 patterns does not fit; with minimizer-style sampling of pattern positions, ~0.3/base each).
Proof: **deterministic completeness is possible, but only with a family of patterns**: any set of e error positions must leave a clean placement (a covering design). The disjoint-blocks argument already gives that for contiguous blocks (e+1 blocks); a family of spaced patterns needs a new combinatorial lemma per pattern set. Single pattern: no guarantee. Mismatches only: indels shift the pattern, so gaps break it. Not done in the repo.

**5. Bit-sampling LSH for Hamming distance** (Indyk and Motwani 1998, STOC, "Approximate nearest neighbors: towards removing the curse of dimensionality", cited from memory).
Idea: pick k random positions of the length-n read; reads within d mismatches agree on all of them with probability (1-d/n)^k; L tables (different position sets) boost it: miss probability (1-(1-d/n)^k)^L. Example *derived*: n=150, d=6, k=25: per-table hit 0.36, L=10 -> miss ~1.2 %, L=20 -> ~1.3e-4.
Buys: finds near copies despite errors (the "unique seed spoiled" case) and selects by the whole read, so candidates are those that agree on k positions (as specific as a 25-mer).
Memory: each table indexes every genome window, 3.1e9 x >= 4 B ~ **12.4 GB per table** (*derived*): impossible at full density; only on the repeat positions (~0.53e9 -> ~2.1 GB per table at 4 B) or with sampled positions; so at most one or two tables. Hamming only (no gaps): scoring has gaps, so it finds candidates, gaps are found by the aligner.
Proof: **random sampling gives no usable completeness** (a probability is not a Lean `forall`). The deterministic version is the covering family of item 4 and the pigeonhole already used. As a candidate generator it is fine under (a) only (checker that table entries equal the genome letters at the sampled positions).

**6. Strobemers / randstrobes** (Sahlin 2021, Genome Res [10.1101/gr.275648.121](https://doi.org/10.1101/gr.275648.121); strobealign, Genome Biol 2022 [10.1186/s13059-022-02831-7](https://doi.org/10.1186/s13059-022-02831-7)).
Idea: a seed is 2-3 short k-mers (strobes) linked by a hash: the second strobe is chosen from a window downstream (randstrobe: the k-mer in the window minimizing a hash combined with the first). Matches survive substitutions and indels between the strobes.
Buys: strobealign reports it reduces repetitiveness of seeds ("E-hits") because a seed is as specific as its whole span (a 2x20 randstrobe over ~40-60 letters is rarely repeated), while tolerating errors between strobes. This is the trick that targets exactly "semi-repetitive but with errors".
Memory: one entry per anchor (strobealign uses syncmers as strobes: density ~1/(k-s+1), few hundred million entries for hg38, *estimate* ~ 1-2 GB at 5 B/entry, not measured).
Proof: soundness easy (key = letters at the anchor positions; compare them). Completeness: **no anchored guarantee**: the second strobe depends on the downstream window, so an error in that window changes the choice; a guarantee exists only if the whole span is clean (then it is a window function with L = span, proved class, but costs length and reintroduces the pigeonhole at span >> 25). So: candidate finder only (use for ordering/prefiltering, never to claim "nothing else"). The `seed_schemes_notes.txt` reaches the same conclusion.

## Summary: which give a usable completeness bound

| trick | candidates | memory on hg38 (free 2.7 GB) | sound | complete (usable for "no good pair") |
|---|---|---|---|---|
| closed syncmers | same as minimizers, pickable | 0.15-0.27/base (~2-4 GB, replaces) | yes | **yes, proved** (L = 2k-s-1) |
| minimizer variants / weighted order | weighted: fewer entries per lookup | <= today | yes | **yes, proved** for every window function |
| stored context (3a) | down to ~true occurrences | spare bits | yes | **yes, proved** (filter) |
| second index of long keys at repeat positions (3b) | big cut in repeats | 0.8-2.6 GB (*derived*) | needs new checker | yes with 2 halves for e <= 1 (new lemma) |
| shorter contiguous seeds (3c) | more hits (2-4x) | 5-6 GB | needs checker | yes (existing pigeonhole) |
| spaced seeds | not fewer | ~today per pattern | needs checker | only for a covering family (new combinatorics) |
| bit-sampling LSH, multi-table | not fewer, better recall with errors | 12.4 GB/table full; ~2 GB on repeats only | checker on sampled letters | **no** (probabilistic); deterministic = covering design |
| strobemers | fewer in repeats, error tolerant | ~1-2 GB (*estimate*) | easy | **no** anchored guarantee; candidates only |

Recommendation, one line: take the cheap proved ones first (weighted minimizer order + stored context), then a small second index of long keys at repeat positions (3b); use strobemer/LSH style seeds only as unproved candidate generators if the examples show they find placements the proved search takes long to rule out.
Caveat: the estimates above are arithmetic, not experiments; the repo's own measurements are named where used.

## Mapping the tricks to the real examples (`SEMI_REPETITIVE_EXAMPLES.md`, branch `docs/semi-repetitive`, ff61781 build; read 2026-11-03)

What the examples show (their numbers): of the pairs reaching the complete search and not given up as highly repetitive (NovaSeq 5 257 = 2.6 %, HiSeq 2 708 = 1.4 %), 47 % / 61 % are truly semi-repetitive (max seed 20-199 or one seed >= 200); 77-81 % of those end "proved none", 14-15 % "gave up" on the places rule. About half of all selected mates have a max seed count of 0-1 (short after trimming, or errors every few bases), and ~16 % of selected mates are < 100 letters. The cost is the product: 20-400 banded checks per mate.

| example class (pair IDs abbreviated) | what an index trick would do | verdict |
|---|---|---|
| **Several moderately heavy seeds on both mates**, e.g. `1103:18602` (mate1 28/73/43, mate2 39/38/34/142/63; 22+49 candidates), `1103:14913` (349 on one seed) | stored context (3a) and a frequency-weighted order drop most banded checks to true occurrences; no completeness cost | **first choice**, proved class |
| **Tandem / segdup block: 4-5 consecutive seeds all at 15-40 hits, s0 = 0**, e.g. `1103:16685` (130 candidates, minibwa MAPQ 0 with XA), `1103:30427` (chrY, 95+109) | candidates agree on one diagonal across seeds: a "2 hits on a diagonal" rule (q-gram lemma, `seed_schemes_notes.txt` section 2(1): j segments give >= j-3 clean) or strobemers (6) collapse them. Longer keys (3b) also separate copies only if copies differ in the flanks | 2-hit rule is provable with new pigeonhole lemma; strobemers = unproved candidate order |
| **One very heavy seed, neighbours near 25-30**, e.g. HiSeq `1116:11533` (552), `1104:7193` (286) | a 50-mer key (3b) around the heavy seed cuts the 552/286 hits if the flanking 25-mers are unspoiled | works when flanks are clean; second index at repeat positions |
| **One heavy seed, neighbours 0**, e.g. `1103:5014` (1185 hits, other seeds 0-4), `1103:19461` (141, rest 0-11) | the neighbours do not occur at all, i.e. the read has errors beside the repeat; long keys cannot help (they contain the errors). Needs error-tolerant seeding (spaced seed, bit-sampling LSH, strobemers) or shorter seeds (3c) | no proved option under the 8 GB budget; candidate generators only |
| **Short mate (35-62 bp) pinned to a unique long mate**, e.g. `1103:24325`, HiSeq `1116:8126`, `1116:12736`, `1116:2475` | already answered quickly (`bestUnchecked`, 1 surviving candidate); a 50-mer key does not exist for a mate < 50 letters | nothing to gain; 3b must not be required for short mates |
| **No frequent seed, many zero counts** (`1103:29197`, `1104:25907`, `1104:25970`, `1103:27832`) | not a repeat problem: errors, short trimmed mates, or clipping (minibwa maps with `113S38M`, `62S89M`; our global alignment cannot clip). Shorter seeds (3c) give candidates; clipping is a Spec/scope question | outside index tricks; `requiredMapBound` already allows "proved none" for these |
| HiSeq 2x250 with 9 seeds per mate and 20-70 hits each (`1116:19980`, `1116:12807`, chrY / `_random` contigs) | many seeds per mate means the pigeonhole needs only one clean: ordering by smallest bucket plus the 2-hit rule; strobemers fit 250 bp best | 2-hit rule + weighted order |

Reading across the table: the classes that dominate the cost (first three rows, ~50 % of selected pairs) are reachable with tricks that keep the completeness proof (stored context, weighted order, 2-hit diagonal rule, long keys at repeat positions). The classes where a unique seed is spoiled by an error beside a repeat (row 4) are the ones only error-tolerant, unproved seeding can find, and they are also the ones the Spec allows to leave unmapped when the best pair is below `requiredMapBound`. The examples were collected with local edits (`gaveUpRepeats = 200`, a debug print) that are not pushed, so the counts describe that build, not the current head.
