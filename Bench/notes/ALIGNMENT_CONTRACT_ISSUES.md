# What the current contract makes hard, and what would unlock faster algorithms

Requested list of issues: things about the frozen `getBestAlignment`
contract that make banded / striped / A* / WFA-style implementations hard or
impossible to prove, and the smallest contract (or infrastructure) changes
that would unlock each.  Ordered roughly by leverage.  Nothing here has been
changed — the contract decisions are yours.

## 1. The path + exact tie-break requirement is the main wall

**Issue.** The contract returns the optimal *path*, tie-broken by the spec's
enumeration order (lexicographic: diag < gapX < gapY at the earliest
difference).  BiWFA, A*, and banded algorithms naturally find *an* optimal
alignment; forcing them to find *the lexicographically least* one is a
second, harder obligation stacked on top of optimality, and it is the reason
I shipped none of them today.

**Unlock (choose one):**
- **(a) Score-only companion track.**  Add a second challenge target
  `getBestScore := (getBestAlignment · ·).map (·.2)` and accept submissions
  proving equality to *that*.  WFA/A*/banded become provable without
  touching tie-breaking.  Weaker deliverable (no traceback), but honest and
  useful — most aligners are run score-only in filters anyway.
- **(b) Tie-break characterization theorem** (no contract change, provable
  work): prove once, against the current spec, that the returned path is
  exactly "the lexicographically least among optimal paths".  Then a
  submission can prove (i) its path is optimal and (ii) lexicographically
  least, instead of replaying enumeration order.  Modularizes the
  obligation; doesn't remove it.

## 2. Universally quantified scoring forbids every pruning argument

**Issue.** All theorems quantify over *all* `Scoring`, including adversarial
ones (positive gap scores, mismatch better than match).  Under such
scorings, optimal paths can wander arbitrarily far from the diagonal, so
*no* band bound, A* heuristic admissibility, or WFA wavefront argument can
be proven — they are all false in that generality.

**Unlock.**  A `ReasonableScoring` predicate in the contract, e.g.:

```
structure ReasonableScoring (sc : Scoring) : Prop where
  match_best   : sc.mismatchScore ≤ sc.matchScore
  mismatch_neg : sc.mismatchScore ≤ 0     -- (or < 0)
  gaps_neg     : sc.gapOpen ≤ 0 ∧ sc.gapExtend ≤ 0
  match_pos    : 0 ≤ sc.matchScore        -- (needed for some bounds)
```

and a second theorem tier: "for all sc satisfying ReasonableScoring,
algorithm = spec".  Band-safety ("an optimal path with score ≥ B stays
within k of the diagonal"), A* admissibility, and band-doubling termination
all become provable from these axioms.  You choose the exact predicate —
that's a spec decision.  Note the benchmark scoring (2/-1/-3/-1) satisfies
any sensible version.

## 3. Missing lemma infrastructure (no contract change needed)

Provable-now support lemmas that adaptive algorithms would lean on:

- Score upper bound: any alignment of strings of lengths m, n scores at most
  `min m n * matchScore` (under §2's predicate).
- Greedy lower bound: the score of any single concrete alignment (e.g. the
  all-diagonal-then-gaps one) bounds the optimum from below.  Enables
  branch-and-bound pruning proofs.
- Additivity/splitting: `bestAux` over a concatenation relates to bests of
  the pieces — the key lemma for divide-and-conquer (Hirschberg) and for
  block/striped processing.

## 4. `List Char` input and cons-list path output limit constant factors

**Issue.**  Striped/bit-parallel algorithms (Myers-style) want random access
(`Array`) and machine-word scores; the contract fixes linked lists and
big-integer `Int`.

**Unlock (representation-only, exactness preserved):**
- Accept `Array Char` inputs with the bridging spec
  `algo a b = getBestAlignment sc a.toList b.toList` — no semantic change.
- Accept run-length-encoded paths (CIGAR-style) with equality stated through
  a proven decoder: `decode (algo …) = getBestAlignment …`.  Still exact.
- Fixed-width scores (Int64/UInt32) need no-overflow side conditions, which
  need §2's bounds plus a length cap hypothesis
  (`xs.length + ys.length ≤ N`).  A theorem with an explicit length-cap
  hypothesis is still a universal theorem — just over a bounded domain; the
  benchmark can state its N.

## 5. Smith–Waterman needs its own spec (planned)

Local alignment computes a different function (max over all substring
pairs, floored at 0 by the empty alignment).  No proof of identity to the
global contract can exist.  When you write the local spec, the entire
Bellman/tabulation machinery from `AlignmentAlgorithms.lean` transfers: the
proof skeleton (objective-with-state, principle-of-optimality lemmas, row
tabulation with a spec-row invariant) was deliberately built to be reusable.

## 6. Top-down memoization (classic A* implementation style) is heavy in Lean

Bottom-up rows avoided verified hash-map reasoning entirely.  A* with a
priority queue + visited map would need a verified map and a Dijkstra-style
invariant — research-scale here (Isabelle's Monad_Memo_DP is the prior art).
If A* matters to you, the realistic route is: score-only track (§1a) +
ReasonableScoring (§2) + potential-function reweighting, and even then it is
the most ambitious item on this page.

## Recommendation, if you want a priority order

§1b (tie-break characterization — pure added theorem, no contract change),
then §2 (you write `ReasonableScoring` — it's a spec judgment call), then a
banded band-doubling implementation as the first genuinely adaptive proved
algorithm.  §1a (score-only track) is the cheapest way to open the door to
WFA-style submissions on the eventual website.
