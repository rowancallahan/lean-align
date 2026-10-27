# Proven read-window algorithms and benchmark

## What is frozen

`ReadWindowTrimmer/Contract.lean` remains the reference implementation.  The
optimized files import it; they do not copy or alter its definition of
`get_best_window`.

Its frozen SHA-256 checksum is recorded in `FROZEN_CONTRACT.sha256`. Verify it
with:

```bash
shasum -a 256 -c FROZEN_CONTRACT.sha256
```

The reference function enumerates every nonempty half-open window `(start,
end)`, scores each window, and calls `List.maxOn?`.  Because `List.maxOn?`
chooses the first maximizer, its exact tie rule is:

1. choose the smallest start index;
2. among tied windows with that start, choose the smallest end index.

Every optimized implementation preserves that exact returned
`Option (Nat × Nat)`, not merely the maximum score.

## The optimized algorithms

### 1. Incremental exhaustive algorithm

File: `ReadWindowTrimmer/Incremental.lean`

The frozen implementation repeatedly slices and sums each candidate window.
The incremental implementation still visits the same `n(n+1)/2` windows in
the same order, but carries the running sum forward when it extends a window by
one base.  It therefore avoids re-summing the common prefix of adjacent
windows.

The final theorem is:

```lean
theorem getBestWindowIncremental_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowIncremental scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore)
```

### 2. Linear maximum-subarray algorithm

File: `ReadWindowTrimmer/Linear.lean`

For every start index, the algorithm keeps only the shortest best prefix of
that suffix.  It computes all these summaries in one right-to-left pass.  A
final left-to-right `List.maxOn?` chooses the earliest start among tied scores.

The important tie decision is in `extendPrefixSummary`: extend through the
later suffix only when its contribution is **strictly positive**.  A zero
contribution would leave the score unchanged, so refusing to extend retains
the shorter window expected by the frozen implementation.

The final theorem is:

```lean
theorem getBestWindowLinear_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowLinear scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore)
```

This theorem is universal: it covers every nucleotide list, every integer
score list (including empty lists), and every function `Int → Int` used as the
per-base score.

### 3. Fused linear algorithm

File: `ReadWindowTrimmer/Fused.lean`

The first linear implementation materializes one best candidate for every
start index and then runs `List.maxOn?` over that list.  The fused version
combines those two stages: while its right-to-left recursion returns, it retains
only the best prefix for the current start and the best overall candidate seen
so far.  It therefore avoids allocating the intermediate candidate list.

Its final theorem is:

```lean
theorem getBestWindowFused_equals_frozen_get_best_window
    (nucleotides : List Nat)
    (scores : List Int)
    (baseScore : Int → Int)
    :
    getBestWindowFused scores baseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map baseScore)
```

### 4. Flat-state recursive algorithm

File: `ReadWindowTrimmer/Faster.lean`

The fused implementation stores nested pairs for its prefix and candidate.
`getBestWindowFlat` stores the same five scalar values in one structure and
marks the small update function `@[inline]`.  Its proof constructs the
corresponding fused result at every recursion step, so this is a representation
change rather than a change to the specification.

### 5. Flat `foldr` algorithm

`getBestWindowFoldr` expresses the same right-to-left computation with
`List.foldr`.  Lean's core library attaches a proved compiler-simplification
theorem to `List.foldr`: compiled code uses the tail-recursive, array-backed
`List.foldrTR`, while the logical definition remains the ordinary fold that is
easy to prove about.  The proof in this project first shows that the fold state
equals the direct recursive state for every list and starting index.

This uses Lean's checked `@[csimp]` mechanism.  It does **not** use `extern`,
`unsafe`, or `implemented_by`.

### 6. Packed `foldr` algorithm (current fastest)

`getBestWindowPacked` removes the `Option FlatResult` value from every fold
step.  A Boolean records whether a result exists, and the five result fields
are stored directly in the accumulator.  The proof converts every packed fold
step back to the flat fold step, then follows the already-proved chain to the
frozen specification.

The easiest standalone theorem to inspect is the first declaration in
`CheckFastestEquivalence.lean`:

```lean
theorem packed_function_is_identical_to_frozen_contract
    (nucleotides : List Nat)
    (scores : List Int)
    (perBaseScore : Int → Int)
    :
    getBestWindowPacked scores perBaseScore =
      get_best_window
        nucleotides
        scores
        (fun windowScores => windowScores.map perBaseScore)
```

## Current tie policy

The proved policy remains highest score, then leftmost start, then shortest
end.  Two audit examples lock this behavior down explicitly.

If the desired policy later becomes "leftmost, then longest," the central
algorithmic change is conceptually small: a zero-score suffix would be extended
instead of discarded.  The affected equivalence specification and proofs
should be changed together rather than silently changing the comparison.

Another future option is to prove only that the result is *a* maximum-scoring
valid window.  Such a theorem permits any tied maximizer, but it is weaker than
the current exact-output theorem.  The current files intentionally retain the
stronger guarantee.

## Relationship to existing read trimmers

The scoring idea `quality - cutoff` has a direct precedent: Cutadapt describes
subtracting a quality cutoff and using partial sums to find its trimming
position.  Cutadapt's documented operation is end trimming, however, whereas
this project maximizes over every contiguous nonempty window:

- [Cutadapt quality-trimming algorithm](https://cutadapt.readthedocs.io/en/v4.7/algorithms.html#quality-trimming-algorithm)

The closest implementation pattern found is seqtk's code labelled "Mott's
algorithm."  It accumulates a per-base score, records a new interval on a
strict improvement, and resets a negative running score.  seqtk uses an error
probability-based score and a minimum-length fallback, so it is related but not
identical to this project's objective:

- [seqtk Mott implementation](https://github.com/lh3/seqtk/blob/master/seqtk.c#L2804-L2925)

fastp and Trimmomatic's ordinary sliding-window modes solve a different
problem: they move a fixed-size window and cut once its mean quality is below a
threshold.  Trimmomatic also has a Maximum Information mode that evaluates
possible trim positions using coverage and error-related factors.  These are
useful later comparison targets, but neither is claimed to be functionally
identical to `get_best_window`:

- [fastp per-read quality cutting](https://github.com/OpenGene/fastp/blob/master/README.md#per-read-cutting-by-quality-score)
- [Trimmomatic paper: Sliding Window and Maximum Information](https://academic.oup.com/bioinformatics/article/30/15/2114/2390096)

## Reproduce the checks

From the `read_window_trimmer` directory:

```bash
lake build
lake env lean CheckFastestEquivalence.lean
lake env lean ReadWindowProofAudit.lean
lake exe read_window_benchmark
```

`lake build` type-checks and compiles the library and benchmarks.  The check
file prints the current fastest function's complete contract theorem. The audit
command prints the axioms used by all final theorems; `sorryAx` must not appear.
The length benchmark checks every result for equality before timing it.

## Benchmark design

The executable is compiled Lean code and measures elapsed monotonic wall-clock
time with `IO.monoNanosNow`.  Inputs are deterministic centered quality
envelopes with a five-value noise pattern. Raw quality is near 25 at the peak
and near 0 outside it. Thus the current `baseScore quality := quality - 10` is
near +15 at the peak and near -10 outside it.

One run on the development machine produced these representative per-call
times:

| length | frozen | incremental | fused | flat recursive | flat foldr | packed foldr |
|---:|---:|---:|---:|---:|---:|---:|
| 50 | 493 µs | 61.2 µs | 1.93 µs | 0.678 µs | 0.622 µs | **0.576 µs** |
| 100 | 3.66 ms | 248 µs | 3.65 µs | 1.26 µs | 1.15 µs | **1.10 µs** |
| 200 | 27.9 ms | 1.00 ms | 7.28 µs | 2.49 µs | 2.28 µs | **2.12 µs** |
| 400 | 217 ms | 4.08 ms | 14.8 µs | 4.88 µs | 4.50 µs | **4.31 µs** |
| 800 | 1.85 s | 17.2 ms | 32.3 µs | 11.2 µs | 9.11 µs | **8.59 µs** |
| 10,000 | not run | not run | 389 µs | 134 µs | 131 µs | **124 µs** |

On this run, the packed version was about 3.8 times faster than the previous
fused version at 800 bp.  These are empirical wall-clock observations, not a
formal speed theorem.
Repeat runs and release/hardware details should be recorded before publishing
performance claims or comparing this implementation with fastp or Trimmomatic.

## Read-length scaling graph

`ReadWindowLengthBenchmark.lean` uses lengths 25, 50, 100, 200, 400, 800,
1,600, 3,200, 6,400, and 10,000 bp.  It measures the frozen cubic and
incremental quadratic implementations only through 800 bp.  The five linear
implementations continue through 10,000 bp.  For every measured length it
checks the participating implementations for the same exact returned window,
then records seven compiled wall-clock trials. Input generation and agreement
checking are outside the timed region. Universal equivalence to the frozen
function is supplied by the Lean theorems rather than by these finite checks.

`plot_read_window_length_benchmark.py` creates a two-panel Matplotlib graph of
per-read latency and time normalized per base.  Both axes are logarithmic.
Each line is the trial mean, each shaded band is the observed minimum-to-maximum
range, and the legend reports a fitted empirical scaling exponent.  The
observed exponents in the recorded run are approximately 2.96 for the frozen
naïve implementation, 2.04 for incremental exhaustive, and approximately 1.0
for the linear implementations.

Reproduce it with:

```bash
lake exe read_window_length_benchmark
python3 plot_read_window_length_benchmark.py
```

Generated artifacts:

- `read_window_length_benchmark.csv`: every raw trial;
- `read_window_length_summary.csv`: mean and range at every length;
- `read_window_length_performance.png` and `.svg`: the complete comparison;
- `read_window_optimized_latency.png` and `.svg`: close-up latency graph for
  the three newest optimized implementations;
- `read_window_optimized_per_base.png` and `.svg`: close-up normalized-cost
  graph for those same three implementations.
