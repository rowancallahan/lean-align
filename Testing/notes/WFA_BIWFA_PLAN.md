# Plan: true WFA and BiWFA, verified against the frozen spec

> **STATUS (2026-08-19): EXECUTED.**  True WFA is DONE — implementation
> (`AlignmentWfa.lean`) plus unconditional theorems `wfaAlign_sound`
> (valid walk + true score) and `wfaAlign_score` (exact optimal score =
> frozen spec, `.map (·.2)` equality).  The greedy lemma lives in
> `AlignmentExchange.lean` (`bellmanAux_match_extend`), proven at the
> bellmanAux level with NO walk surgery — via prev-state swap bounds and
> a pure-extension exchange induction (the surgery plan below was not
> needed for it; surgery WAS needed, in constructive form, for the
> boundary `demoteCell` inside WFA).  BiWFA v1 is implemented and
> soundness-proven (`AlignmentBiwfa.lean`); its optimality proof is the
> main open item.  See SESSION_SUMMARY.md §"TRUE WFA + BIWFA DELIVERED"
> for the full map.  The rest of this file is the original plan, kept
> for the record.

Written 2026-08-18 as the working plan for the next session. Everything
referenced here compiles today; this file is the bridge across context
compaction. Read ALIGNMENT_WAVEFRONT_NOTES.md first for the architecture
of what already exists.

## Current state (all proven, all compiling)

- Frozen spec `getBestAlignment` (AlignmentSpec.lean, untouched).
- `bellmanAlign`, `gotohAlign`, `gotohFusedAlign` = spec (AlignmentAlgorithms.lean).
- `bandDoublingAlign` = spec, UNCONDITIONALLY (AlignmentWavefront.lean) —
  renamed from wfaAlign; this is Ukkonen-style certified band doubling,
  NOT true WFA. Machinery inside it that WFA will reuse:
  - `penalty_transform`: 2·score + pathPenalty = M·(m+n) on valid walks;
    `pathPenalty_nonneg` under `ReasonableScoring`; order reversal lemma.
  - `bestAux`/`bellmanAux` Bellman lemmas incl. tie-break (left-biased maxOn).
  - Certification transfer: `maxOn?_of_filter_maxOn?` (+ the two fold
    lemmas) — filtered earliest-max transfers to full list when rejected
    elements are strictly below.
  - `bound_arith`, `two_score_le_offBandBound`, `certified_global`.
  - Runtime-check pattern: `reasonableB` gate + proven fallback makes the
    final theorem hypothesis-free. REUSE THIS for WFA: the WFA fast path
    fires only under the runtime check; fallback = gotohFusedAlign.
- `getBestAlignment_lex_least` / `getBestAlignment_characterization`
  (AlignmentLexicographic.lean): the returned path is the lex-least
  optimal walk (diag < gapX < gapY via `LexLT`). This is the KEY to
  making greedy match-extension compatible with the tie-break: lex order
  PREFERS diag, and WFA's free extension takes diag on matches — they
  point the same way.

## The one genuinely new lemma WFA needs: greedy match extension

Everything else is engineering. State it against `bellmanAux` (which IS
the spec, by `bestAux_eq_bellmanAux`):

```lean
theorem bellmanAux_match_extend (sc : Scoring) (hr : ReasonableScoring sc)
    (x : Char) (xs ys : List Char) (y : Char) (prev : Option Step)
    (hxy : x = y) :
    bellmanAux sc (x :: xs) (y :: ys) prev =
      let d := bellmanAux sc xs ys (some .diag)
      (.diag :: d.1, sc.matchScore + d.2)
```

i.e. on a match, the three-way maxOn is won by the diagonal branch.
Unfolding `bellmanAux` (cons/cons case), this needs the diag candidate
to be ≥ the gapX and gapY candidates:

```
M + best(xs, ys, diag) ≥ gapXCost prev + best(x::xs, ys, gapX)      (A)
M + best(xs, ys, diag) ≥ gapYCost prev + best(xs, y::ys, gapY)      (B)
```

(≥ suffices: left-bias of maxOn then picks diag on ties.)

**Proof strategy for (A)** (B symmetric). Work on the SPEC side
(`bestAux`, max over allPaths) and do walk surgery: given any valid walk
`p` of `(x::xs, ys)` scored from prev-state gapX, construct a valid walk
`p'` of `(xs, ys)` scored from diag-state with
`M + score(p') ≥ (gapXCost prev) + score(p)`. Surgery: `p` must consume
`x` somewhere — at its first gapY or diag column touching x. Two cases:
1. p = gapXs^k ++ diag(x,·) :: rest  — replace with
   p' = gapXs^k ++ rest-shifted…  (the match at the front absorbs one
   diag; count the run/extend deltas; hxy makes the moved diag a match,
   worth M ≥ any column's contribution under ReasonableScoring).
2. p = gapXs^k ++ gapY :: rest — the gapY consumes x; deleting the gapY
   and prepending nothing turns it into a walk of (xs, …); the deleted
   column releases ≥ E + (possibly O); M ≥ 0 ≥ E covers it.
Use `walkStats`/`scoreWalk_eq_stats` to do the accounting: the surgery
changes counts by bounded deltas, so the inequality reduces to
`bound_arith`-style integer facts. Expect ~300–600 lines. THIS IS THE
HARD PART; do it first and standalone (file: AlignmentExchange.lean).
If the general-prev version fights, prove it for prev ∈ {none, diag}
first (enough for extension after a diag run) and handle gap-prev at
the wavefront-update sites instead.

**Sanity check before proving:** #eval the claim on random small inputs
and scorings satisfying reasonableB. If a counterexample appears with
gap-prev, the restricted version is the true lemma (WFA literature: free
extension applies in the M-matrix, not mid-gap — expect exactly that).

## WFA implementation shape (after the lemma)

Penalty space (use `penalty_transform`): penalties x = 2(M−X),
e = M−2E, o = −2O, all ≥ 0 under the runtime check. Diagonal k = j − i,
offset = i (suffix-consumed count). Wavefront per penalty s: three maps
(M/I/D states) diagonal → furthest offset + path-so-far (shared cons
list, reversed). Represent diagonals as a `List (Int × Cell)` sorted by
k, or `Array` with k-offset — lists are proof-friendlier.

- fr-update recurrence mirrors bBellman with penalty indexing; free
  extension = repeated `bellmanAux_match_extend`.
- Termination: fuel = penalty of the all-gaps witness (computable),
  same pattern as bandDoublingGo.
- Correctness statement: score-only FIRST:
  `wfaScore sc xs ys = (getBestAlignment sc xs ys).map (·.2)` — Rowan
  has approved score-track thinking; then path via lex: the greedy
  lemma says the lex-least optimal path is exactly the greedy-extended
  one, so the wavefront traceback (prefer diag, then gapX, then gapY at
  equal penalty) reproduces the spec's path. `getBestAlignment_lex_least`
  + a uniqueness argument (lex-least is unique among optima: LexLT
  total on distinct valid walks — prove `LexLT_total`: distinct valid
  walks of the same strings are LexLT-comparable; neither is a prefix of
  the other since both consume everything) turn "my output is valid,
  optimal, lex-least" into "= getBestAlignment". That avoids replaying
  enumeration entirely — the characterization route working as designed.

Fallback-and-certify is NOT needed for WFA if the invariant proof is
completed (WFA is exact, not heuristic); the runtime `reasonableB` gate +
gotohFused fallback keeps the theorem unconditional exactly as before.

## BiWFA (after WFA)

New lemma: splitting. For any split of xs into xs₁ ++ xs₂:
score-optimal alignment decomposes as forward-best of (xs₁, ys-prefix)
+ backward-best of (xs₂, ys-suffix) maximized over the ys split point
and the state at the boundary (3 states). Statement against bestAux via
`allPaths` append decomposition — needs an allPaths-splitting lemma:
every walk of (xs₁ ++ xs₂, ys) factors uniquely as a walk of (xs₁, ys₁)
++ walk of (xs₂, ys₂) with ys = ys₁ ++ ys₂; score adds with a boundary
prev-state correction (scoreWalk of concatenation: prove
`scoreWalk sc (p ++ q) … = scoreWalk p … + scoreWalk q … (last-state p)`
— an append lemma over the fold, straightforward induction).
Tie-break across the meet is the delicate part; with the lex
characterization, prove the meet choice preserves lex-least (prefer the
earliest split achieving the optimum, diag-most boundary state first).
If it fights, land BiWFA on the score-only statement and report.

## Benchmarks

Add `wfa` (and later `biwfa`) to the noise + similar + length scenarios
next to band_doubling. Expected: wfa strictly dominates band_doubling
(incremental wavefronts, no thrown-away attempts, no guard-cell sweep),
near-linear on similar strings.

## Pitfalls learned this session (do not relearn)

- `by_contra`, `set`, `conv_rhs`, `split_ifs`, `ring_nf` are NOT in core
  Lean 4.33 — use cases-on-Bool, generalize/omega, `show…from` rewrites,
  fusedPick-style helper lemmas, distribute-then-omega.
- omega: treats products as atoms — keep atom shapes uniform; distribute
  with explicit rw chains (Int.mul_add/mul_sub/sub_mul/mul_assoc), or
  factor into a closed lemma like `bound_arith`. min/max on Int are NOT
  reliably handled — the band code avoided depending on it.
- rw inside `(x :: t).maxOn f h` hits dependent-proof motives — route
  head rewrites through `maxOnHead`-style congruence lemmas.
- `List.count` unfolds to `==`; use `simp +decide` to discharge closed
  Step comparisons.
- Functional induction (`f.induct`) splits every `if` into its own case;
  check `#check @f.induct` on a truncated copy before writing the cases.
- Keep `matches` out of field names (reserved keyword).
- Nested matches in defs make equation lemmas unusable — use
  headD/tail accessors with junk defaults + head-congruence lemmas.


## EMPIRICAL FINDING (2026-08-18, pre-compact): greedy lemma scoped exactly

Brute-force check (all string pairs to length 4+1 over {A,B}, 6 reasonable
scorings, all 4 prev states, 27k+ cases): `bellmanAux_match_extend` has
**ZERO violations for prev ∈ {none, some diag}** and fails ONLY in gap
states (1156 violations each for gapX/gapY; minimal counterexample:
xs="A", ys="AA", prev=gapX, scoring 2/-1/-3/-1 — extending the open gap
then matching beats matching immediately, +1 vs −2). So the lemma to
prove is exactly:

```lean
theorem bellmanAux_match_extend (sc : Scoring) (hr : ReasonableScoring sc)
    (x y : Char) (xs ys : List Char) (hxy : x = y) :
    bellmanAux sc (x :: xs) (y :: ys) none =
      let d := bellmanAux sc xs ys (some .diag)
      (.diag :: d.1, sc.matchScore + d.2)
```

(prev = none only; `bellmanAux_diag_eq_none` transports it to diag-prev.
This matches WFA exactly: free extension happens in the M-state only.)
The WFA wavefront must therefore extend matches only from M-state cells,
which is what the standard algorithm does anyway.

## Adaptive dispatch (Rowan's roadmap, recorded pre-compact)

KEY INSIGHT — dispatch is free correctness: because every algorithm in
this project carries `… = getBestAlignment`, ANY dispatcher that picks
among them — hash prefilter, corpus statistics, a learned model, wall-
clock feedback — is automatically proven correct by case analysis on the
branch. Heuristics never need proofs here; only the leaves do.

Planned dispatchers (in rough order):
1. **Identical-strings shortcut** (provable fast path, not just a hint):
   if xs == ys then return (replicate m .diag, m·M). Provable with
   existing machinery: score-optimality via the stats bound (diagCols ≤ m,
   gap terms ≤ 0 under ReasonableScoring), lex-minimality is immediate
   (the all-diag walk is LexLT-below every other valid walk at its first
   gap column). Cheap O(m) check; big win on corpus dedup workloads.
2. **Hash/near-identity prefilter as a HINT**: rolling hash or k-mer
   sketch to guess divergence, then branch band_doubling (low s) vs
   gotohFused (high s). Hash collisions harmless — both leaves proven.
3. **Corpus-adaptive selection**: after a few alignments against a
   sequence library, pick the empirically fastest proven algorithm for
   the rest (bandit-style). Correct by the same argument; the harness
   can live in the benchmark layer first.
4. **Later (Rowan): seeding at scale** — BWA-style FM-index/suffix-array
   seeds, chaining, seed-and-extend for very long sequences, on top of a
   Rowan-authored local-alignment spec. The verified-extension kernel
   these need is exactly the global aligners already proven here.
