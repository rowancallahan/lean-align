# Current alignment version review — 2026-09-11

Reviewed the changes from c2365f7 through 0a776c9, the working tree, the
reorganized codec certificates, both benchmark runners, and the new probes.
The validation improvements from this review are committed as e1a6e71.

## What changed

- 915042e moved the existing modules into `trimmer/` and
  `alignment/{spec,codecs,checks,probes,notes}`. Lake maps folders to module
  roots; imports retain their names. Direct content comparison found 23
  existing alignment implementation/proof modules unchanged from c2365f7.
- Generated per-codec certificates now collect the pinned exported
  statements and supporting theorem axiom reports. Both specs have frozen
  checksum files.
- 14a2888 added `wfaAlignK_score_fun_eq`: equality with `wfaAlign` as score
  functions. Traceback validity and totality are separate proved statements;
  identical traceback tie choices are not claimed.
- `pabench/simple/` provides a small, readable measurement path. Unlike the
  older runner, it grows its output array inside the timer and extracts
  costs afterward. Comparisons between current candidates use this same
  runner. Differences from older timings are not algorithm improvements.
- ca24046 and 0a776c9 added UInt32 and Nat probes, plus a nightly A*PA2
  build and native comparison data. The probes remain unproved.
- A local, uncommitted `alignment/codecs/wfa_u32/AlignmentWfaU32Level.lean`
  draft is registered as a default Lake target. It currently fails to
  elaborate and contains arithmetic lemmas, not a complete certified
  aligner. It has no exported score/soundness/totality certificate.

## Current candidates

| Runner kernel | Implementation | Status |
|---|---|---|
| `wfak` | `wfa_runs/AlignmentWfaRuns.lean`, `wfaAlignK` | Proved; direct runs and compact small-error shortcut |
| `wfaca` | `wfa_offsets/AlignmentWfaArray.lean`, `wfaAlignCA` | Proved; array inputs and per-step traceback |
| `wfah` | `wfa_small_errors/AlignmentSmallErrors.lean`, `wfaAlignH` | Proved; shortcut with per-step traceback |
| `wfahc` | `wfa_small_errors/AlignmentCompact.lean`, `wfaAlignHC` | Proved; compact shortcut, general fallback converts per-step output |
| `probe-u32`, `probe-nat` | `alignment/probes/` | Experimental; excluded from verified rankings |
| local `wfau` draft | `wfa_u32/` | Incomplete; not an executable certified codec |
| `biwfa` | `biwfa/AlignmentBiwfa.lean` | Soundness only; excluded from verified rankings |

The older Gotoh, banded, full WFA, and list variants retain their existing
proofs and implementations. Current competition for the fastest proved
codec is among the four array-input candidates above.

## Checks and small fixes

Both frozen hashes pass. All ten existing certificate files elaborate with
only the allowed logical axioms. The 5766-case cross-codec check passes with
zero mismatches and zero direct-run certificate rejections. The trimmer
audits pass. The overall `lake build` fails in the existing UInt32 draft;
the separate `simple_runner` build and the four comparison certificates pass.
The draft and its local Lake registration were left untouched.

e1a6e71 keeps the same organization and timing loop. It checks certificates
before measurement, rejects missing reference vectors and invalid pair
counts, enforces the axiom allowlist, and returns failure on failed
certificates. Six regression tests exercise these cases. The all-checks
script now preserves Lean failures instead of losing them in output-formatting
pipelines. The minimal runner gained dispatch for the existing `wfah` and
`wfahc` functions. A smoke comparison passed 16 vector checks.

## Next proof work

The UInt32 probe is not certified by the current draft lemmas. The probe uses
wrapping subtraction for `off + t - m`; the draft uses saturating subtraction.
Equating them requires the valid-cell geometry invariant, in addition to
upper bounds preventing overflow. Padded bands, the fused level loop, and
the single-source optimization also need refinement proofs. Complete these
in the existing `wfa_u32/` folder before promoting that candidate. Successful
runtime traceback checks establish validity and score, but do not alone prove
that the computed corner level is optimal.

## Fastest current proved version

Keep **`wfak` / `wfaAlignK`** as the default. Fresh three-run medians give it
the lowest runtime in **24 of 28** uniform-error workloads. In the other
four it trails `wfaca` or `wfah` by only **0.2–1.1%**, below what these
unpinned runs justify using for workload-specific switching.

| Candidate | Geometric mean runtime / `wfak` over 28 cells |
|---|---:|
| `wfak` | 1.000 |
| `wfaca` | 1.146 |
| `wfah` | 1.152 |
| `wfahc` | 1.325 |

At 1000 bp, microseconds per pair:

| Errors / costs | `wfak` | `wfaca` | `wfah` | `wfahc` | Native BiWFA |
|---|---:|---:|---:|---:|---:|
| 1%, unit | 19.93 | 25.65 | 26.95 | 36.41 | 4.35 |
| 1%, affine | 28.71 | 34.30 | 37.05 | 45.41 | 6.41 |
| 5%, unit | 102.79 | 106.03 | 106.79 | 116.49 | 9.27 |
| 5%, affine | 222.45 | 230.38 | 226.85 | 243.10 | 23.11 |

`wfak` is 4.5–11.1× BiWFA at 1000 bp and 3.02–25.66× across this full
length sweep; 10/28 cells are within 5×. It is our fastest proved codec,
not the fastest external implementation, and the general 2–5× target
remains unmet. The one/two-substitution fast path is shared with `wfahc`;
the direct-run general fallback is the reason to prefer `wfak` overall.

Data: `pabench/results/current_e1a6e71/`. Three fresh native and Lean sweeps,
four Lean kernels, 504 cost-vector checks, zero mismatches or unchecked
cases. Native A*PA2 simple/full use the existing nightly executable and
addendum YAML; they support the unit-cost cells. All 42 unsupported native
jobs per trial are expected Edlib/A*PA2 affine cases. Raw runs, medians,
min/median/max timings, source/executable hashes, and the audit log are saved.
Both sides run on this Mac with traceback construction timed and parsing
excluded; these are throughput measurements with no CPU pinning or frequency
control. The minimal runner's timing boundary is described above.

![Current comparison](../../pabench/results/current_e1a6e71/lengths_comparison.png)
