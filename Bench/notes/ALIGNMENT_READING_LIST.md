# Reading list: specifying affine-gap edit distance & local alignment in Lean

Compiled 2026-08-18 for the next verified-algorithm challenge in this project.
Goal: Rowan writes the spec by hand; these are the sources to read first.

## Headline from the prior-art search

No mechanized proof of Smith–Waterman, Needleman–Wunsch-with-scoring, or
affine-gap (Gotoh) alignment was found in any prover (Lean, Isabelle/AFP,
Coq/Rocq, Agda, F*). Verified work stops at unit-cost edit distance and LCS.
A declarative "optimum over all alignments" spec with affine gaps appears to
be genuinely open territory.

## Read these first (the core four)

1. **Wagner & Fischer (1974), "The String-to-String Correction Problem"**,
   J. ACM 21(1). https://dl.acm.org/doi/10.1145/321796.321811
   THE template for a non-algorithmic spec: edit distance defined as the
   minimum cost over all edit scripts, the equivalent "trace" (monotone
   matching) formulation, and only then the DP with a correctness proof.

2. **Gotoh (1982)**, J. Mol. Biol. 162:705–708.
   https://courses.cs.duke.edu/compsci260/fall20/resources/AlignmentPapers/1982.gotoh.pdf
   The O(mn) affine-gap three-matrix recurrence — the fast implementation to
   verify. Its traceback description contains known errors (see #3, #4).

3. **Altschul & Erickson (1986), "Optimal sequence alignment using affine
   gap costs"**, Bull. Math. Biol. 48:603–616.
   https://link.springer.com/article/10.1007/BF02462326
   Corrects Gotoh's traceback errors; careful treatment of gaps abutting
   sequence ends. Read alongside Gotoh.

4. **Flouri, Kobert, Rognes & Stamatakis (2015), "Are all global alignment
   algorithms and implementations correct?"**
   https://www.biorxiv.org/content/10.1101/031500v1.full.pdf
   Shows widely used affine-gap implementations return suboptimal alignments
   at gap boundaries. Catalogs exactly the corner cases a Lean proof must
   nail; also the motivation for why this deserves mechanization.

## Textbook treatments

- **Durbin, Eddy, Krogh & Mitchison, "Biological Sequence Analysis", ch. 2**
  — defines score as a max over alignments FIRST, then derives NW/SW/affine
  (three-state M/X/Y view — the cleanest mental model for the affine cost).
- **FU Berlin lecture notes, "Pairwise alignment" (Reinert et al.)** — free,
  close to Durbin ch. 2 with more formality; proofs of the recurrences.
  https://www.mi.fu-berlin.de/wiki/pub/ABI/SequenceAlignmentWS13/alignment.pdf
- **Paris Descartes slides on Gotoh** — states the per-matrix invariants
  ("best score ending in a gap in x") that become the Lean lemmas connecting
  Gotoh to the spec.
  https://helios2.mi.parisdescartes.fr/~lomn/Cours/BI/Material/gap-penalty-gotoh.pdf
- **Smith & Waterman (1981)** (3 pages) — local alignment as max over all
  pairs of substrings, with the 0-floor.
  https://courses.cs.duke.edu/compsci260/fall20/resources/AlignmentPapers/1981.smith.waterman.pdf
- Gusfield ch. 11–12 (edit-distance/similarity duality, end-gap-free
  variants); Jones & Pevzner (alignment = path in edit graph — an alternate
  spec shape).

## Prior formal-verification art (build on / differentiate from)

- **Mathlib Levenshtein (Lean 4)** — `Mathlib.Data.List.EditDistance.*` by
  Kim Morrison (same author as lean-zip). Generic delete/insert/substitute
  costs, `suffixLevenshtein` last-row formulation, estimator interface.
  Removed from current master; read at a tagged release:
  https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.10.0/Mathlib/Data/List/EditDistance/Defs.lean
  Note: its definition is algorithmic (recursive), NOT "min over alignments"
  — the missing declarative spec is exactly this project's gap to fill.
- **Isabelle AFP `Monad_Memo_DP`** (Wimmer, Hu & Nipkow, ITP 2018) —
  verified memoization/DP framework; examples include minimum edit distance
  and LCS. State of the art in "fast DP proven equal to naive reference."
  https://isa-afp.org/entries/Monad_Memo_DP.html
- **Kong et al. (2018)**, Levenshtein metric in Lean 3 (insertion/deletion
  codes). https://ieeexplore.ieee.org/document/8664354/
- **Algebraic Dynamic Programming** (Giegerich et al.) — grammar of
  candidates + scoring algebra + choice function; affine-gap alignment is a
  running example. The published analogue of "spec = objective over all
  candidates, implementation = fused DP."
  https://link.springer.com/article/10.1186/1471-2105-6-224
- **Little & Pauleve**, DP by semiring shortcut fusion from a brute-force
  spec (includes edit distance). https://arxiv.org/pdf/2107.01752

## Read mapping with a stated sensitivity guarantee (added 2026-09-14)

Neither is mechanized in a proof assistant. Both give paper definitions and
guarantees that a Lean mapper could formalize.

- **RazerS** (Weese, Emde, Rausch, Döring & Reinert, Genome Research 2009) and
  **RazerS 3** (Weese, Holtgrewe & Reinert, Bioinformatics 2012), SeqAn.
  - "Fully sensitive" k-error read mapping for Hamming and edit distance.
  - Guarantee from the pigeonhole principle (k+1 pieces, one is exact) and
    q-gram counting (SWIFT filter).
  - Indexes the reads, not the genome, and scans the reference linearly.
  - Candidates are checked with banded Myers bit-vector alignment.
  - Memory (RazerS 3 paper): about 9 GB best-mode / 15 GB all-mode for 10M 100 bp reads on human.
  - Parallelism: reads distributed statically across threads, verification queued dynamically.
  - https://genome.cshlp.org/content/19/9/1646
  - https://academic.oup.com/bioinformatics/article/28/20/2592/206947
- **Rabema** (Holtgrewe, Emde, Weese & Reinert, BMC Bioinformatics 2011, 12:210).
  - A strict definition of the read mapping problem: the gold standard for a read is every matching interval within distance k.
  - False negatives are missed intervals; false positives are reported intervals outside the gold standard.
  - Evaluation tools read SAM output from any mapper; the gold standard was built with RazerS.
  - Candidate template for a Lean "mapper completeness" spec.
  - https://bmcbioinformatics.biomedcentral.com/articles/10.1186/1471-2105-12-210
  - https://github.com/holtgrewe/rabema

## Inspiration / ecosystem

- lean-zip: https://github.com/kim-em/lean-zip
- "Why Lean is faster than Rust": https://kim-em.github.io/blog/2026-7-24-why-lean-is-faster-than-rust/
- Cautionary tale on spec boundaries (fuzzing found bugs *outside* lean-zip's
  verified core): https://kirancodes.me/posts/log-who-watches-the-watchers.html
- VerifyThis competition (verified-algorithm challenges, no alignment task
  posed so far): https://verifythis.github.io/

## Spec-writing checklist (subtleties distilled from the above)

- Pick min-cost distance OR max-score similarity for the frozen spec; the
  other is a corollary (duality: Gusfield ch. 11).
- Define an alignment as a list of columns from {(a,b), (a,-), (-,b)} whose
  projections are the two inputs (or as a Wagner–Fischer trace). The column
  list makes affine cost a state-dependent fold: the cost of a column depends
  on whether the previous column was a gap in the same sequence.
- Empty conventions: distance(ε, y) = sum of inserts; decide end-gap policy
  (global vs. semiglobal — Altschul & Erickson discuss end effects).
- Affine convention: gap of length k costs o + k·e or o + (k−1)·e — sources
  differ (Durbin vs. Gotoh). Fix it once in the spec.
- Local alignment: the empty alignment is admissible with score 0, so the
  optimum is ≥ 0 by definition; meaningfulness wants expected pair score < 0.
- Tie-breaking: the score spec is tie-free. Any traceback-returning
  implementation should be specified as "member of the argmax set", not
  equality of alignments — this is where the Gotoh/Flouri bugs live.
  (v1 recommendation: return score only.)
