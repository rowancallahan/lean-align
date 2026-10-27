# Proved Lean read-window trimmer

This is a self-contained Lean 4 project for selecting the highest-scoring
nonempty contiguous window of a quality-score list.  Its fastest implementation
is proved to return exactly the same `Option (Nat × Nat)` as the frozen
executable specification for every input and every per-base scoring function.

Exact equality includes empty-input behavior, start and exclusive-end indexes,
and the current tie rule: highest score, then leftmost start, then shortest end.

The project has no dependency on the original learning lab and contains no
absolute filesystem paths. You can copy this entire directory elsewhere.

## First verification

From the repository root, run:

```bash
shasum -a 256 -c FROZEN_CONTRACT.sha256
lake build
lake env lean trimmer/CheckFastestEquivalence.lean
lake env lean trimmer/ReadWindowProofAudit.lean
```

The checksum must report `ReadWindowTrimmer/Contract.lean: OK`. The axiom
reports must not contain `sorryAx`.

## Main files

- `trimmer/ReadWindowTrimmer/Contract.lean`: frozen executable specification.
- `ReadWindowTrimmer/Faster.lean`: three newest optimized functions and their
  exact-equivalence proofs.
- `CheckFastestEquivalence.lean`: short, prominent statement of the complete
  contract for the current fastest `getBestWindowPacked` implementation.
- `ReadWindowProofAudit.lean`: prints the axioms used by every final theorem.
- `READ_WINDOW_ALGORITHMS.md`: detailed algorithm, proof, tie-policy, and
  benchmark explanation.
- `ROBOTS_README.md`: maintenance instructions for coding agents.

## Benchmarks and graphs

The raw CSV files and the plotting scripts are included.  To regenerate the
read-length benchmark and all of its graphs:

```bash
lake exe read_window_length_benchmark
python3 trimmer/plot_read_window_length_benchmark.py
```

The frozen cubic and incremental quadratic implementations stop at 800 bp.
All five linear implementations continue through 10,000 bp.

The Matplotlib script requires Python with Matplotlib and NumPy. Lean itself
does not require Python or any third-party Lean packages.
