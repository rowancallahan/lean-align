# Adversarial audit of the spec (read-only), 2026-11-02, box S1

Base: origin/claude/festive-fermi-mf9mo6 at f3f7be1. Read: Spec/Alignment.lean, Mapping.lean, Aligner.lean, Fasta.lean, Fastq.lean,
Sam.lean, Shim.lean. Nothing in Spec/, Proofs/, Main.lean changed. Question for every definition: what is the laziest or most wrong
implementation that still satisfies the theorem, and what does a user see?

Evidence that compiles: `Testing/notes/spec_audit/SpecAuditEvidence.lean.txt` (copy to a `.lean` file, `lake env lean` it; imports Spec.Aligner;
standard axioms only). It proves, on a toy genome, findings 1 and 7, and checks the `#eval` facts of findings 5 and 6.

## Summary table (ordered by severity)

| # | finding | severity | smallest fix |
|---|---|---|---|
| 1 | `.unknown` + `found = some r`: the reported pair can be garbage (all-insertion mates at EMPTY windows is a proper pair); `bestPossibleScore := 0` is always true. PROVED in Lean | high | add a floor to reported pairs |
| 2 | `.unique` / `.multimapper` carry no floor either: a contaminant gets "unique, MAPQ 60, proper pair" at score -400 | high | same floor, or a fourth `junk` uniqueness |
| 3 | `bestPossibleScore` is only an upper bound; with `unique`/`multimapper` the pair IS best, yet XB may say 0 | medium | for `unique`/`multimapper` require `bestPossibleScore = found score` |
| 4 | Placement equality is too fine for "unique/multimapper": same-locus alternatives (2 mismatches = 1 gap, tandem shifts) count as ties; and too coarse in the other direction (near-ties are "unique") | medium | locus-overlap equivalence; a near-tie margin |
| 5 | `N = N` scores as a match (0); N runs of hg38 give perfect alignments of N-reads | medium | N never matches |
| 6 | Case: lowercase is neither matched with uppercase nor complemented; the shim accepts soft-masked FASTA and non-ACGTN silently, and the end-to-end hypothesis `GenomeIsDNA` is not checked | medium | uppercase or reject at read time; or case-fold in the spec |
| 7 | `AlignmentKernelCorrect` is satisfied by a kernel that always says `.unaligned 1` (PROVED) or returns a garbage path with a huge `slack` | medium (kernel slot) | bound `threshold` and `slack` |
| 8 | Only *proper* pairs compete: better improper alignments (large indels/SV, translocations, chimeras) are ignored, the forced proper pair may get MAPQ 60 | medium | covered by 1+2 (floor) and by documenting scope |
| 9 | Trimming: the theorems start after trimming; a trimmer that trims everything/almost everything is not excluded here; one trimmed mate drops the other mate's alignment; SEQ/QUAL printed are the trimmed ones; no adapter handling vs dovetail slack 0 | medium | state the trimmer contract in the end-to-end theorem or document it |
| 10 | FASTA names: the whole header line (with spaces) becomes the chromosome name / RNAME / `@SQ SN` | medium | name = up to first whitespace |
| 11 | The `.chromosomes` sidecar is trusted and not tied to the index; wrong or missing sidecar mislabels RNAME silently | medium | store names/lengths in the index; spec a function `chromosomesOf index` |
| 12 | `InsertSettings`: `junkScore` is an absolute pair-sum (long reads are all junk); any positive value makes "report nothing" valid; `range.1 > range.2` makes nothing proper | low-medium | scale or validate |
| 13 | `IsProper` edge cases (dovetail, containment, RF, empty windows, leading/trailing D/I, TLEN vs fragment) | low | document; empty windows covered by the floor |
| 14 | Shim/SAM plumbing: partial SAM on error, panics (`toNat!`, `fromUTF8!`), QNAME empty/tabs, FASTQ `@`/`+` not validated, MAPQ stand-in, `XT` tier claims | low | see list |

## 1. A garbage pair satisfies `PairAnswer.Correct` (high)

`PairAnswer.Correct` (Aligner.lean) says three things: the found pair is a real proper pair, the bound is >= every proper pair, and the
uniqueness label is true. For `.unknown` the label is only `found = none -> bestPossibleScore < junkScore`; when `found = some r`, nothing is asked.
The reported pair need not even be the best at its own placements: any `PairAlignment` is allowed, including the worst path.

Concrete counterexample (proved in the evidence file, `lazy_correct`): genome = one chromosome of 2000 A, both mates = ACGT, `range = (100, 1000)`.
Mate 1 placed forward at `[1000, 1000)` (empty window), mate 2 reverse at `[1300, 1300)`, each aligned as all insertions (`CIGAR 4I`, score -14, pair -28).
It is `IsProper` (same chromosome, opposite strands, fragment 300 in range, no dovetail). The answer `⟨some that pair, 0, .unknown, .boundsOnly⟩`
is `Correct`: the bound 0 holds because every score is <= 0 (`pathScore_le`), uniqueness `.unknown` with `found ≠ none` asks nothing.
So the laziest correct aligner reports, for every pair, a proper pair of two all-insertion mates at empty windows (score -612 for 2x150), `bestPossibleScore = 0`, `unknown`.
It maps nothing and satisfies the theorem, and the SAM prints flag 99/147 ("properly paired"), a CIGAR like `150I`, `XB:i:0`.
(This is the hole already found, one level further: the `junkScore` guard stops "report nothing", not "report garbage".)
The repo's own measurements show why this matters: pairs that end with a "degenerate last-resort pair" are 1-3 % of 200k hg38 pairs (NEAR_TIE_COVERAGE.md).
Smallest fix, in `Correct`'s `.unknown` arm:
`(∀ r, answer.found = some r → insertSettings.junkScore ≤ r.mate1.score + r.mate2.score)` and, to stop "report a pair at -17 when the best is 0",
a margin: `answer.bestPossibleScore ≤ r.mate1.score + r.mate2.score + insertSettings.reportSlack` (new field, e.g. 8 or 16).
Also forbid empty windows by requiring `placement.start < placement.stop` for reported mates (an empty window is never a mapping of a non-empty read).

## 2. `.unique` and `.multimapper` have no floor (high)

`.unique` needs `pair.IsUniqueBestProper`: best among proper pairs and strictly better than every proper pair at other placements. A read pair
that comes from nowhere (contaminant, PhiX, adapter dimer, species mix-up) still has a best proper pair in the genome; if it is the single best one
(random 2x150 against 3.1 G: best score about -100 to -200), an implementation may say `.unique` and the SAM prints MAPQ 60, flag "proper pair", `XU:unique`.
Nothing in the spec says a unique pair must be a good one; `junkScore` constrains only the `found = none` case. Our router chooses `unknown/none` for such pairs,
but that is a property of the implementation, not guaranteed by the theorem, and MAPQ 60 is printed from `uniqueness` alone (`Sam.mapq`).
Fix: same floor as finding 1 for all three labels (`junkScore ≤ pair score` whenever `found = some`), or add `Uniqueness.junk` for "best pair below the floor, not reported".

## 3. The bound can be loose even when the pair is proved best (medium)

`bestPossibleScore` only has to be >= every proper pair's score. With `.unique` or `.multimapper` the reported pair is itself the best proper pair,
but an implementation may print `XB:i:0` for a pair scoring -30. The tag then says "a perfect pair might exist" about a proved best pair, and anything computing
"gap between found and best" from XB is wrong. Fix: in the `.unique` and `.multimapper` arms add `answer.bestPossibleScore = r.mate1.score + r.mate2.score`.
(`Tier` is declared "a performance record only, no claim", but it is printed as `XT:Z:` next to proved fields; an implementation may print `eachMateUnique` for everything.)

## 4. Placement equality and uniqueness (medium)

`pair.placements ≠ other.placements` compares (chromosome, start, stop, strand) exactly.
- Same locus, different `stop` or `start` counts as a different placement. Example: near a read end two mismatches (-8) tie with one gap of length 1 (-8)
  that moves `stop` by one; or a read inside a microsatellite `(CA)n` shifted by the repeat unit. The pair is then labelled `multimapper` (MAPQ 0) although it has a single locus.
  The set of such pairs is not measured here; by construction it affects every read with >= 2 errors within a few bases of an end.
- The other direction: ties are only between *placements*; two proper pairs at the same placements but different CIGARs are the same pair (fine), but a pair whose
  second-best proper pair is 1 point lower is still `unique` -> MAPQ 60. The spec has no near-tie margin
  (the repo has a note about "near-tie MAPQ labels (later)").
Fix: define "same locus" as same chromosome and strand with overlapping intervals (or start within a window) for the tie test, and add a margin to `unique`
(`other.score + margin < pair.score`), or leave `unique` strict and print MAPQ from a separate setting.

## 5. `N` matches `N` (medium)

`scoreWalk` gives `matchScore` whenever `q = r` as characters. Read N against genome N scores 0 (perfect); read N against A scores -4 (an ordinary mismatch).
The bench hg38 (195 sequences) has about 150 Mb of N (centromere, gaps, telomere padding). A read (or trimmed mate) made only of N, which NovaSeq no-calls produce, aligns at score 0 anywhere in an N run: huge
numbers of tied placements, `multimapper`, `XB:i:0`, "properly paired" flags. Verified: `scoreWalk defaultScoring [.diag,.diag] ['N','N'] ['N','N'] none = 0` (evidence file).
Fix: `if q = r ∧ q ≠ 'N'` for the match, and a (possibly smaller) N penalty otherwise.

## 6. Case and alphabet (medium)

`complement` handles only uppercase A/C/G/T; `q = r` is exact. Facts (evidence file): `['a'] vs ['A']` scores -4; `reverseComplement ['a','c','N'] = ['N','c','a']` (lowercase is not complemented).
`alignPairs_correct` has no alphabet hypothesis, `alignPairs_end_to_end` has `GenomeIsDNA` (A, C, G, T, N only), but the shim never checks it:
a UCSC soft-masked `hg38.fa` (about half lowercase) builds an index and maps with mismatches everywhere; the output is "correct" for the theorem and useless.
IUPAC codes (R, Y, K...) in a genome are also mismatches. Fix: uppercase while reading FASTA/FASTQ (cheap, trusted) or reject; or make the spec compare case-insensitively.

## 7. Kernel slot (medium for the website, none for the aligner theorem)

`AlignmentResult.unaligned threshold` is correct when every path scores < threshold. All scores are <= 0, so `.unaligned 1` is always correct:
`AlignmentKernelCorrect defaultScoring (fun _ _ => .unaligned 1)` is PROVED in the evidence file (`lazy_kernel_correct`). The comment "(important so not everything goes here)" is not enforced.
Likewise `.bounded cigar score slack` with `slack = 10^9` and the all-gap path is correct. Only `AlignmentKernelExact` is meaningful.
Fix: a parameter `unalignedBound` (the score below which a pair is junk, e.g. `junkScore`), `.unaligned t` correct only with `t ≤ unalignedBound`, and `.bounded` only with `slack ≤ maxSlack`.

## 8. Only proper pairs compete (medium; scope)

Everything is about the best *proper* pair. A pair whose mates align perfectly on different chromosomes, or 50 kb apart (deletion, translocation, large insert),
has an excellent improper alignment that the spec ignores; the forced proper pair (very low score) may be reported `unique` with MAPQ 60 (finding 2). Also
chimeric reads, soft clips and split reads cannot be aligned (global alignment of the whole trimmed mate, no clipping: a 20-base adapter tail is mismatches or `20I`).
This is a scope decision; the dangerous part (a confident label on a bad pair) is closed by the floor of findings 1 and 2.

## 9. Trimming (medium)

The theorems take the trimmed mates as given. (e): a trimmer that returns `none` for every mate, or keeps one base, satisfies `alignPairs_correct` (every result `.trimmedAway`, or 1-letter reads that are all multimappers).
What protects us is `ReadTrim`'s own frozen contract (best-scoring quality window), which is outside these files; the end-to-end theorem does not mention it.
Also: `.trimmedAway .one` only needs mate 1 to be `none` (it may be chosen when both are trimmed); one trimmed mate makes the whole pair unmapped (the good mate's alignment is lost, but it is printed with flag
`mate unmapped` and its trimmed letters); SAM `SEQ`/`QUAL` are the trimmed ones, with no `H`/`S` clip and no record of the removed bases (original length is lost);
a mate that is empty in the FASTQ is the same as trimmed away. There is no adapter trimming, so fragments shorter than the read length leave adapter bases that cannot align
(`dovetailSlack = 0` rejects read-through mates) -> unmapped, for example cfDNA (about 165 bp inserts) with 2x150 reads.

## 10. FASTA names (medium)

`readFasta` uses the whole line after `>` as the name. Ensembl/NCBI headers (`>1 dna:chromosome chromosome:GRCh38:1:1:248956422:1 REF`) give RNAME and `@SQ SN` with spaces;
other tools on the same genome (GATK dictionary, samtools faidx) use the first word, so the SAM is inconsistent with the reference it was made from. Lines before the first `>` are ignored.
Fix: name = text up to the first space/tab.

## 11. Sidecar `.chromosomes` (medium)

`Shim.lean` trusts that `INDEX` is `buildIndex byteGenome` (this is `hIndex`) and that `INDEX.chromosomes` lists the same genome's names and lengths. The spec has no link between the two:
an index rebuilt for another genome next to an old sidecar, or a sidecar edited by hand, gives wrong `@SQ` and `RNAME` for correct placements (chromosome *index* is right, the name is wrong).
`readChromosomeList` falls back to `(line, 0)` on a malformed line and uses `toNat!` (panics). Fix: let `buildIndex` contain names/lengths and add a spec function reading them back; drop the sidecar.

## 12. `InsertSettings` (low-medium)

`junkScore : Int := -16` is the sum for the pair, absolute: for 2x150 it is 4 mismatches; for a 10 kb read every pair is below it, so "report nothing" is always allowed (long reads, Rowan's later goal).
Any `junkScore > 0` makes `found = none` always valid (all scores <= 0), the theorem quantifies over all settings and the shim fixes the default, so this is harmless today.
`range = (min, max)` with `min > max` makes no pair proper: every bound is vacuous and all pairs may be left unmapped (the shim passes the command-line numbers unchecked).
Fix: express `junkScore` per base or as a fraction of the maximum, validate `min ≤ max`.

## 13. `IsProper` details (low)

Facts, from the definition: orientation FR only (RF/outie excluded); the reverse mate inside the forward mate (`reverse.stop < forward.stop`) is excluded with slack 0, equal intervals are allowed;
`fragment = reverse.stop - forward.start` counts reference length (deletions count); TLEN printed by the SAM is `max stop - min start` and equals `fragment` only when `dovetailSlack = 0`;
mates on different chromosomes are never proper; empty windows and CIGARs that start or end with D or I are legal for a reported mate (finding 1); `Nat` subtraction in `fragment` is guarded by the third conjunct, so no truncation issue.
`IsUniqueBest` (single read) and `exists_best` are unused by `PairAnswer.Correct`.

## 14. Shim and SAM plumbing (low)

(f) Checked and fine: POS = start + 1; reverse flag 16 and mate-reverse flag 32 from the right placements; SEQ/QUAL reversed (and complemented) on the reverse strand with the same complement table as the spec;
RNEXT `=`, PNEXT = other.start + 1; TLEN sign (leftmost positive, tie -> mate 1 positive); mate 1 line first. Unchecked or surprising:
- On a mid-run error (FASTQ out of step, bad quality length, I/O) the program exits non-zero but leaves a SAM that is a valid prefix with a complete header: a pipeline that ignores the exit status consumes a truncated file. (Write to a temp name and rename at the end.)
- `toNat!` on the command line, `String.fromUTF8!` on read names/qualities/letters panic on non-numeric or non-UTF-8 input.
- `samName` can be empty (name `/1`) or contain tabs; QNAME > 254 chars not checked; the FASTQ reader does not verify `@` and `+`; a wrapped (multi-line) FASTQ is rejected only by the sequence/quality length check, and only if the lengths differ.
- `mapq` is 60 for `unique`, else 0; `unknown` pairs print flag 2 (proper pair) with MAPQ 0; `XT:Z:` prints a tier that the spec says carries no claim.
- `samChunk` zips pairs with results; it relies on the proved equal length (a shorter result list would drop reads silently).
- `buildIndex : ByteArray` may contain the genome verbatim (the theorem only quantifies `index = buildIndex byteGenome`); nothing bounds time or memory of `alignPairs`.

## Suggested minimal patch set for Spec/ (for Rowan to choose)

1. `Correct`, all three arms: `∀ r, found = some r → junkScore ≤ r.mate1.score + r.mate2.score ∧ r mates have start < stop`; `.unknown` also `bestPossibleScore ≤ pair score + reportSlack`.
2. `.unique`/`.multimapper`: `bestPossibleScore = found pair score`.
3. `scoreWalk`: N never matches; `readFasta`/`readFastqRecord`: uppercase (or reject non-ACGTN) before building the index and aligning.
4. Tie test by locus overlap, plus an optional margin for `unique`.
5. FASTA name = first word; names and lengths stored in the index.
6. `AlignmentResult.Correct`: bounds on `threshold` and `slack`.
