# Agent overview

Read this first. It is short on purpose; the dated history is in `SESSION_SUMMARY.md` (same folder).

## What the project is

A paired-end short-read aligner in Lean 4. `Spec/` states what a correct answer is; `Proofs/`
proves that the aligner the tool runs (`buildIndex`, `alignPairs`) always gives a correct answer.
The owner is Rowan. Goal after correctness: speed (currently ~2x minibwa on the benches) without
losing the proof.

## Current state (2026-10-27)

- Fully proved on Lean 4.35: `Spec.alignPairs_correct` and `Spec.alignPairs_end_to_end` depend only
  on `propext`, `Classical.choice`, `Quot.sound`. Five external kernels (leanchecker-paranoid,
  lean4lean, con-leche, con-ron, leanchecker) accept the export; nanoda ran out of memory on a
  15 GB box (no verdict). Tag `new-spec-typechecked` marks that commit on main.
- Milestone M1 is bounds-only: `answerOf` reports no pair and `uniqueness := .unknown`. Next (M2):
  report the found pair with its CIGAR and unique / multimapper (`notes/NEW_SPEC_ADAPTERS.txt`).
- Speed work is prepared on branch `speed/loop-shape` (not merged): six proved USize kernels,
  A/B scripts, and `notes/LOOP_SHAPE_PLAN.md` with ranked candidates. Its item I1 (`loadIndex`
  re-copied the multi-GB index on every `alignPairs` chunk) is done on branch `speed/index-views`:
  the loaded `G.w`, `ix.sl`, `ix.offs` are the saved bytes, and `buildIndex` checks the loaded index.
- Proved speedups still to port from old branches: `speed/150-stage`, `speed/150-loops` (old folder
  layout; see the "Branch check" entry near the end of `SESSION_SUMMARY.md`).

- The tier 2 heuristic is OFF in `alignPairs` (`TierHeur.rtxCfg`): it only pays once tier 2 pairs are
  reported (M2). Turn it back on then; see SESSION_SUMMARY.md (2026-10-27 evening).

## Where things are

| Path | What |
|---|---|
| `Spec/Alignment.lean`, `Spec/Mapping.lean`, `Spec/Aligner.lean` | The frozen statements. `Spec/Shim.lean`, `Fasta`, `Fastq`, `Sam` are trusted plumbing (not proved). |
| `Proofs/Aligner.lean` | `buildIndex`, `alignPairs` defined; both top theorems proved. |
| `Proofs/Bridge.lean`, `Hits.lean`, `Tiers.lean`, `Index.lean` | Translation from the internal model to `Spec/`. |
| `Proofs/core/` | Internal model the kernels and router are proved against (`AlignmentSpec`, `MapSpec`, `PairSpec*`). Not a spec; names will be changed later. |
| `Aligner/mapper/TierRouter.lean` | The tier router `tierPair` and `tierPair_sound`; `TierOk` near line 555. |
| `Aligner/kernels/`, `Aligner/index/` | Alignment kernels and index structures, each with its proofs. |
| `Aligner/LeanAlign/`, `Main.lean` | Command line and the only file-system code. |
| `Testing/scripts/CI_check.sh`, `check.sh`, `external_checkers.sh` | Developer check, final check, external kernels. |
| `Testing/checks/AuditAlignPairs.lean` | Audit: no unsafe / extern / implemented_by / partial / extra axioms behind the top theorems. |
| `Testing/benches/` | Benchmark executables and analysis scripts (`WholeGenome.lean` is the whole-genome harness). |
| `Testing/data/fetch.sh` | Downloads chr21, hg38 and HG002 reads (iGenomes and GIAB on S3) into `Testing/data/downloads/`. |
| `Testing/notes/` | Design notes, plans, `SESSION_SUMMARY.md` (dated log), `AGENTS_PLAN.md` (finished overnight plan). |

Lean module names did not change when folders moved; `lakefile.lean` maps each folder to its modules.

## Rules

- Never edit `Spec/` without Rowan's approval; then regenerate `Spec/FROZEN.sha256`.
- Finished work has no `sorry`, new axioms, `native_decide`, `implemented_by`, `extern`, `unsafe`,
  `partial`. Speedups go in as a fast version + equality proof + `@[csimp]`, theorems untouched.
- Never weaken a statement to make a proof go through; write the counterexample down instead.
- Run `sh Testing/scripts/CI_check.sh` before committing; `sh Testing/scripts/check.sh` before calling
  something done.
- Lean in cloud boxes: release.lean-lang.org may be blocked; install elan and the
  `lean-4.35.0-linux.zip` release from GitHub, `elan toolchain link`, `elan override set`.
- Rowan prefers short code, asserts over error handling, and short plain explanations.
