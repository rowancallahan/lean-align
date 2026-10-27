# Proved UInt32 alignment kernels

`wfau3` / `wfaAlignU3` is the newest kernel. Its final proof was completed
2026-09-11. `wfau` and `wfau2` remain available as proved baselines.

The executable definitions are in `AlignmentWfaU32Run3.lean` and
`AlignmentWfaU32Fill3.lean`; the hot cell loops remain together with `lcpU`
in `AlignmentWfaU32Fill.lean` so the C compiler can inline their calls.
The general path stores three padded fronts in one array and uses an array
history and a shared zero array. The single-source path is shared with U2.
Both paths divide penalties by their gcd and rescale the returned level.

## Proof chain

1. `AlignmentWfaU32FillSpec3.lean`: exact values and unchanged padding of
   the executed block-array fill loop.
2. `AlignmentWfaU32Level3.lean`: checked source reads equal reads of the
   extracted fronts; `uLevel3_some` proves exact level equality with
   `uLevel` and preserves the proof-only `BWF` layout invariant.
3. `AlignmentWfaU32Loop3.lean`: seed, corner test and array/list history
   bookkeeping. `AlignmentWfaU32Kernel3.lean` uses these to prove
   `uLoop3_some` and `uRun3_some`, relating a successful run to `wfaRunOP`.
4. The existing lattice theorem gives the original optimal corner level.
   `acceptRuns_spec` combines it with the proved run checker and score
   identity. The traceback generator is checked at runtime.
5. `wfaAlignU3_score`, `_sound`, `_isSome`, and `_score_fun_eq` cover every
   scoring scheme and every pair of `Array Char` inputs. The exact shortcut
   and proved fallback handle inputs outside the fast-path gate.

The result has the specification's **optimal score** and a valid traceback;
the theorem does not require identical traceback choices among tied optima.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the final audit.
No implementation changes were needed while completing the final proof.

## Validation and timing

Run `sh alignment/checks/check_all.sh` for frozen-file checks, the build,
generated certificates, axiom audit, and executable cross-codec checks.
The U32 certificate covers 80 theorems; `CheckCertified.lean` also reports
U3 fast-path rejections, which can reveal a correct but slow fallback.

Use `pabench/repeat_bench.py` with `--kernels wfakf,wfau2,wfau3` for fresh
proof-gated comparisons. Keep all three repetitions and the raw cost
vectors. Use `pabench/plot_lines.py` on the resulting `summary.csv`.
`NEXT_IDEAS.md` records the previous performance work and further ideas;
its performance numbers predate completion of the final proof.
