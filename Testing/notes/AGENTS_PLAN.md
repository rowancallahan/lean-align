# Overnight proof push: agent plan

Written 2026-10-27. The five cloud routines first created for this were deleted before they ran;
this file is what the next agent starts from.

## For the next agent (start here)

You are the coordinator. Your job: get the five tasks below running, keep them inside the budget,
and merge finished work.

1. Read, in order: this file, `Proofs/README.md` (tasks, old→new names, rules),
   `Proofs/Bridge.lean`, `Proofs/Aligner.lean`, the end of `SESSION_SUMMARY.md`.
2. Check the starting point: `lake build Proofs` succeeds, and
   `#print axioms Spec.alignPairs_correct` shows `sorryAx` (the open lemmas). `sh scripts/check.sh`
   passes on `main`.
3. Start the five tasks below, each on its own branch from `main`. Ways to run them, best first:
   - subagents in the cloud (the Agent tool's `isolation: "remote"`), if your session has it;
   - cloud routines / cloud sessions on github.com/rowancallahan/lean-align, one per task;
   - local subagents in this session (fine if the machine stays awake).
   Before starting cloud work, make sure `main` on GitHub is up to date with this folder.
4. Budget (Rowan): at most 3 Opus, 6 Sonnet, 10 Haiku agents in total; at most 5 cloud boxes at
   once (agents share boxes). Prefer Opus and Sonnet; Haiku for chores (builds, grep, axiom audits).
5. When a task's branch builds (`lake build Proofs`) and `sh scripts/check.sh` passes, merge it into
   `main`. Resolve conflicts in `Proofs/Bridge.lean` by keeping both sides' proofs. After each merge,
   rerun the build and `#print axioms Spec.alignPairs_correct`.
6. Collect every `Proofs/BLOCKERS_*.md` into one summary for Rowan. He may hand stuck lemmas to
   another prover, so each blocker must stand alone.
7. Update `SESSION_SUMMARY.md`. Commit selectively. Ask Rowan before any push to `main` other than
   merging green proof branches.

## Rules every agent follows

- Never edit anything under `Spec/` (frozen; `Spec/FROZEN.sha256`). Statements in `Proofs/` that
  mirror `Spec/` stay identical (comparator will check this after the Lean 4.35 bump).
- No new axioms. No `sorry`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `partial` in
  finished work. Relying on another task's still-open lemma (as `sorry`) is allowed until it merges.
  Check with `#print axioms` (only propext, Classical.choice, Quot.sound).
- Internet: none, except installing the Lean toolchain / Lean packages (elan, lake dependencies)
  and, only if index work truly needs one, downloading a reference genome. No web searches.
- Work on your own branch only. Commit each proved lemma as you go and push the branch. Never push
  to `main`, never merge, never force-push (the coordinator merges).
- If a statement is false as written: stop on it, write the counterexample and the exact
  restatement needed in `Proofs/BLOCKERS_<task>.md`. Never weaken anything to make it go through.
  Also write down anything you are stuck on, precisely enough for another prover to pick it up.
- Build with `lake build Proofs` (the first build compiles dependencies and takes a while). Run
  `sh scripts/check.sh` before finishing.
- Finish with a short report: proved, not proved and why, final commit hash, and the output of
  `#print axioms Spec.alignPairs_correct`.

## The five tasks

### 1. B6: what each router tier proves gives a correct answer (Opus)

Branch `proofs/tiers-b6`. Subagents: up to 1 Opus, 1 Sonnet, 3 Haiku.

Prove `answerOf_correct` in `Proofs/Bridge.lean`: from
`MapSpec.Fast.TierOk usl lo hi (oldGenome genome) mate1 mate2 (some bytes1) (some bytes2) t`
show `(answerOf t).Correct insertSettings genome mate1 mate2`. `answerOf` reports no pair and
`.unknown` (milestone M1), so only the bound has content: every proper pair scores at most
`boundOf t`. Do not change `answerOf`, `boundOf`, `tierOf`. Per tag (TierOk: mapper/TierRouter.lean
near line 555; specs: old_spec/PairSpecU.lean, old_spec/PairSpecTier.lean, mapper/PairDispatch.lean
for `pairSpecT`, mapper/PairLadder.lean for `PairTieOk`):
- t1: each mate's unique best at its cap (`mapSpecBoth`) is its global best, so `x.2 + y.2` bounds
  every pair.
- t1g / t1u: `pairSpecUT` = some (x, y) for every cap ≥ g0; for a competitor pick caps low enough
  to include its placements, then use `bestPairD`'s `find?` property.
- t2b: direct.
- t2 / t3: `FloorOk` (per-mate floors; with `pf = some G0` every proper pair is < −G0).
- t0: impossible (both mates are `some`).
- t1gm / t1um: bound 0 (`GenomicAlignment.score_nonpos`, Proofs/Mapping.lean).
Uses `hit_of_alignment` (B2) and `isProper_iff` (B3) as stated. May move into a new
`Proofs/Tiers.lean` imported by Bridge.lean. Commit per tag case.

### 2. B5: the index layer (Opus)

Branch `proofs/index-b5`. Subagents: up to 1 Sonnet, 3 Haiku.

In `Proofs/Aligner.lean`, define `buildLoaded`, `saveIndex`, `loadIndex`, `indexOk`, `roundTrips`
and prove `loadIndex_empty`, `roundTrips_load`, `indexOk_sound`. Do not change `buildIndex`,
`alignPairs`, `alignPairs_correct` (already proved from these).
- `LoadedIndex := MapSpec.Mz.MzIdx × MapSpec.Fast.PGen × Array Nat × Array Nat` (minimizer index,
  packed genome, chromosome offsets, chromosome lengths).
- `buildLoaded`: pure functions only, the builders the frozen harness uses: bench/WholeGenome.lean
  `build` mode (Mz.buildWV / Mz.buildW with k=22, B=26, c=0, w=5, t=6) and the packing of `pmap`
  mode (`cutOk`, `cutAll` in mapper/PairConcatPacked.lean).
- `saveIndex` / `loadIndex`: one ByteArray (magic header, sizes, parts) so
  `loadIndex ByteArray.empty = none`.
- `roundTrips saved loaded : Bool`: decidable check that `loadIndex saved = some loaded`; runs once
  at build time, may be slow.
- `indexOk byteGenome loaded : Bool`: `cutOk && Mz.check2P ix G && unpacked chromosomes = the
  genome's bytes`; `indexOk_sound` gives `cutOk`, `MapSpec.GenomeBytes ((cutAll G offs ns).map
  MapSpec.Mz.unpack) (oldGenome byteGenome.decode)`, and `check2P`.
Uses `encodes_decodeRead` (B4). Test on a tiny synthetic genome written in Lean. Report any
per-call copying in `loadIndex` (alignPairs calls it once per chunk) for the later speed pass.

### 3. B1 + B4: paths are old walks; bytes decode (Sonnet)

Branch `proofs/bridge-b1-b4`. Subagents: up to 1 Haiku.

- B1 `walk_of_path`, `score_eq_walkScore`: a `Path` (Spec/Alignment.lean, `List.count`
  conditions) is an old `AlignmentSpec.IsMonotoneWalk` (sums of `xConsumed` / `yConsumed`) on
  `path.steps.map oldStep`, with the same score. The two `scoreWalk`s are written identically;
  `oldDefaultScoring` = `MapSpec.sc0` = ⟨0, −4, −6, −2⟩ = `defaultScoring`. Prove a general lemma by
  induction on the steps, then specialize.
- B4 `encodes_decodeRead`: `MapSpec.Encodes` (kernels/mapper_band/MapperBandKernel.lean) holds for
  `decodeRead` (Proofs/Answer.lean, `Char.ofNat byte.toNat`); a byte is < 256, a valid Char.

### 4. B2: hits are the placements' best alignments (Sonnet)

Branch `proofs/hits-b2`. Subagents: up to 1 Sonnet, 1 Haiku.

Prove `hit_of_alignment` and `alignment_of_hit` in `Proofs/Bridge.lean`, relating
`MapSpec.hitsBoth oldDefaultScoring T (oldGenome genome) read` (old_spec/MapSpec.lean,
old_spec/PairSpec.lean) to `GenomicAlignment` (Spec/Mapping.lean). A window's score is the best
walk score from `getBestAlignment`; use `getBestAlignment_returns_a_maximum_score`,
`getBestAlignment_returns_a_valid_walk`, `mem_allPaths_iff_isMonotoneWalk`, and B1. Prove the
converse of B1 as a helper (old valid walk → new `Path`, same score). Facts: `fits` gives
start ≤ stop ≤ chromosome length; `oldPlacement` uses `stop − start`; `oldGenome` keeps each seq;
`reverseComplement` = old `revComp`; `Strand.orient` matches `hitsBoth`'s strand cases; every
window is in `allWindows`.

### 5. B3: proper pairs match, then a statement review (Sonnet)

Branch `proofs/proper-b3`. Subagents: up to 1 Haiku.

Prove `isProper_iff` in `Proofs/Bridge.lean`: new `PairAlignment.IsProper range dovetailSlack`
(Spec/Mapping.lean) vs old `MapSpec.properPairU sl lo hi` (old_spec/PairSpecU.lean on
`properPair`, old_spec/PairSpec.lean) at `oldPlacement` of each mate. Each mate's `fits` gives
start ≤ stop. Unfold, split on strands, `omega`.
Then a read-only review: check every other statement in `Proofs/Bridge.lean` and the `sorry`
definitions in `Proofs/Aligner.lean` are provable as written (off-by-one, Nat subtraction, strand
or order mismatches between old_spec and Spec). Write suspected problems with concrete
counterexamples to `Proofs/BLOCKERS_review.md`.

## After all five merge

- `#print axioms Spec.alignPairs_correct` shows only propext, Classical.choice, Quot.sound: M1 done.
- Next (one Opus agent): M2, report the found pair with a checked CIGAR and `unique` /
  `multimapper` (notes/NEW_SPEC_ADAPTERS.txt R1, R2; T1 needs the dovetail check; the router must
  report one tied pair).
- Then: Lean 4.35 bump on a branch, comparator (Spec/ = challenge, Proofs/ = solution), and
  `lake check --paranoid`.
