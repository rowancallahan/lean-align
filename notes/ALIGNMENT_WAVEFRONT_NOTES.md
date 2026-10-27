# The verified wavefront aligner: what was built, what it is, what it isn't

Written 2026-08-18, documenting `AlignmentWavefront.lean`.

## Headline

`wfaAlign` is an adaptive alignment algorithm — fast when the strings are
similar, degrading gracefully as they diverge — with an **unconditional**
theorem:

```
theorem wfaAlign_equals_getBestAlignment (sc : Scoring) (xs ys : List Char) :
    wfaAlign sc xs ys = getBestAlignment sc xs ys
```

Every scoring (including pathological ones), every input, exact path and
tie-break. Axioms: propext, Classical.choice, Quot.sound only. No sorry,
no @[extern], no partial, no native_decide.

The trick that keeps the theorem hypothesis-free: **runtime certification**.
The algorithm checks `reasonableB sc` (the ReasonableScoring inequalities)
at run time and, per band width, checks that the in-band optimum's doubled
score strictly beats a proved upper bound on anything leaving the band.
Only *certified* answers are returned early; failing everything, the band
doubles until it covers the whole grid, where the banded computation is
proved to coincide with the exact one. `ReasonableScoring` therefore never
appears in the correctness statement — it only determines *when the fast
path fires*, i.e. performance, which the benchmark measures empirically.

## Also delivered: the match-zero translation (requested as a theorem)

- `pathPenalty`: the doubled penalty model — matches cost 0, a mismatch
  `2(M−X)`, a gap column `M−2E`, opening a run `−2O`.
- `penalty_transform`: for every valid walk,
  `2·score + penalty = M·(m+n)`. So maximising similarity score IS
  minimising penalty, ties included (`score_le_iff_penalty_ge`), and
  `pathPenalty_nonneg` shows penalties are nonnegative exactly under
  `ReasonableScoring` — the WFA precondition, derived rather than assumed.

## Honest naming: how this relates to WFA and BiWFA

This algorithm is **Ukkonen-style band doubling with a certification
test** — the same adaptive principle as WFA (cost grows with divergence,
work concentrates near the diagonal), and the same shortest-path-on-a-DAG
view of alignment Rowan pointed out.  It is *not* the WFA data structure:

- WFA proper stores, per penalty value s and diagonal k, only the
  furthest-reaching point, and extends matches greedily for free.  Its
  correctness rests on a greedy-exchange lemma ("some optimal alignment
  always extends maximal match runs"), proved by alignment surgery that
  reorders columns without increasing affine penalty.  Mechanizing that
  surgery (with run-boundary bookkeeping) is the main remaining wall.
- BiWFA additionally meets in the middle for O(s) memory, which needs an
  alignment-splitting lemma plus tie-break coordination across the
  meeting point.  Under the exact lexicographic-tie contract this is the
  hardest part; under a score-only contract it becomes much closer.

What was proven here covers the *certification* and *band geometry*
halves of that program (deviation bounds, penalty transform, filtered
argmax transfer with tie preservation, banded tabulation), all reusable
for a future true-furthest-reaching implementation. The remaining new
mathematics for full WFA is the greedy-exchange lemma; for BiWFA, the
splitting lemma. Neither needs a contract change to attempt.

## Proof architecture (for the next session or the next model)

1. `walkStats` mirrors `scoreWalk` case-for-case; `scoreWalk_eq_stats`
   decomposes any walk's score exactly. `stats_eq_counts` ties statistics
   to plain `List.count` on valid walks; consumption sums give count
   identities (`xConsumed_sum_eq_counts`).
2. `inBand lo hi p`: every prefix's deviation (gapX − gapY so far) stays
   in a window that shifts with each consumed column.
   `counts_of_not_inBand`: leaving the band forces gap counts past the
   window edges. `inBand_of_wide`: wide windows admit every valid walk.
3. `bandedBestAux` (spec: earliest maximum over band-filtered allPaths)
   = `bBellman` (guarded three-way recursion), via the same
   Bellman-lemma machinery as the unbanded proof plus a filter
   distribution lemma (`filter_inBand_map_cons`).
4. Banded tabulation: `BCell` cells hold `Option` best-per-prev-class;
   rows truncate when the window dies (`hi < 0`), giving the adaptive
   cost profile. Row invariant `bSpecRow` + `bCellHead_bSpecRow` make
   truncation transparent. `bandedRun_eq` lands the tabulated corner on
   `bBellman`.
5. Certification: `maxOn_acc_exchange` + `maxOn_filter_fold` +
   `maxOn?_of_filter_maxOn?` — if the filtered earliest-maximum strictly
   beats every rejected element, it is the full list's earliest maximum
   (left bias survives because filtering preserves relative order).
   `bound_arith` is the closed integer inequality; `two_score_le_offBandBound`
   instantiates it with walk statistics; `certified_global` assembles.
6. Driver `wfaGo` (fuel = m+n+2, w = 2, 5, 11, 23, …): wide-band and
   fuel-exhaustion exits fall back to `gotohFusedAlign` (already proved);
   early exits require certification. `wfaAlign` gates on `reasonableB`.

Known performance headroom (not correctness): rows still materialise
cheap guard-failing cells left of the window (O(m²) trivial conses in the
similar-strings regime). A skip-count row representation would remove
this; the invariant needs a drop-offset. Also each certification failure
recomputes the band from scratch; WFA-style incremental widening would
reuse work.

## Sources used for this development

Alignment & adaptive algorithms:
- Ukkonen (1985), "Algorithms for approximate string matching",
  Information and Control 64 — the band-doubling / cutoff idea.
- Marco-Sola, Moure, Moreto, Espinosa (2021), "Fast gap-affine pairwise
  alignment using the wavefront algorithm", Bioinformatics 37(4) — WFA.
- Marco-Sola et al. (2023), "Optimal gap-affine alignment in O(s) space",
  Bioinformatics 39(2) — BiWFA.
- Eizenga & Paten (2022), "Improving the time and space complexity of
  the WFA algorithm and generalizing its scoring", bioRxiv — the
  match-reward ↔ match-zero scoring transformation formalized here as
  `penalty_transform`.
- Gotoh (1982); Altschul & Erickson (1986); Flouri et al. (2015) — as in
  ALIGNMENT_READING_LIST.md.

Shortest-path framing (per Rowan's observation):
- Dijkstra (1959); Hart, Nilsson & Raphael (1968) — A*; admissible
  heuristics correspond to our certified bounds (branch-and-bound with a
  proved admissible bound = the certification lemma).
- Spouge (1989), "Speeding up dynamic programming algorithms for finding
  optimal lattice paths", SIAM J. Appl. Math — A* for alignment lattices.
- Ukkonen's cutoff as the ancestor of both banding and wavefronts.

Verification patterns:
- The window project's own Contract/Faster proofs (maxOn? machinery).
- Wimmer, Hu & Nipkow (2018), Monad_Memo_DP (Isabelle) — verified DP
  framing, for contrast: bottom-up rows avoided its memo-monad needs.
