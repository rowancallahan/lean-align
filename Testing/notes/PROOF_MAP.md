# Proof map: Spec claim -> theorem -> how to check -> hypotheses -> gaps (for Rowan, 2026-11-03)

Verification-oriented, not for publication. Spec lines are from this branch's base (festive-fermi `791462a`, your Spec `main 38a5676`).
**Proof lines are from `origin/speed/floor-real-spec` @ `61e4daa`**, because that is the only branch whose `Proofs/` cover your current Spec.
I built it and ran `Testing/scripts/CI_check.sh`: `ALL CHECKS PASSED` (frozen checksums ok, mirrors ok, standard axioms only).
Lean 4.35.0, no network needed. Axiom lines below were printed by me (`lake env lean` on a scratch file), not copied from notes.

## 0. Read this first: three gaps

1. **On `claude/festive-fermi-mf9mo6` (791462a) the proofs do NOT prove your Spec.** `Proofs/Answer.lean` there is the old copy (`junkScore := -16`,
   no `requiredMapBound`, no `repetitiveUnknown`); `lake build` passes but `CI_check.sh` has the new mirror check that fails
   (commit message says so). `speed/floor-real-spec` fixes it (`Proofs/Answer.lean mirrors Spec/Aligner.lean`).
   `speed/report-floor-proofs` is an older round: it proves the `spec/report-floor` revision (`requiredMapBound` as a *field* of `InsertSettings`,
   no `repetitiveUnknown` / `highlyRepetitiveIn`), so it is NOT your current Spec either. Its note `REPORT_FLOOR_PROOFS.md` still says
   `junkScore -50` / `hNoLeftover` in the header; the round-3 section (and the code) say `-100`, `SettingsOk`, no `hNoLeftover`. The header is stale.
2. **`alignPairs_correct` / `alignPairs_end_to_end` are not exactly your statements: they carry one extra hypothesis `SettingsOk insertSettings`
   (`junkScore ≤ -16`).** See 2.1.
3. **No `#print axioms` for the two headline theorems exists anywhere in the repo**, so `CI_check.sh` never checks their axioms
   (it greps `depends on axioms` lines in the build log; a `sorry` would still show as a warning). I printed them, see 2.1. Suggest adding the two lines to `Proofs/Aligner.lean`.

## 1. Spec claims that are not the main theorem (`Spec/*.lean` `sorry`s)

Check: `lake build Proofs`; each file ends with `#print axioms`. `Proofs/*.lean` states the same theorem as `Spec/*.lean` (comparator would check; not run here, repo is not on the comparator yet).

| Spec | Proof | axioms (as printed) |
|---|---|---|
| `Spec/Alignment.lean:69` `cigar_decodes` | `Proofs/Alignment.lean:86` | `[propext]` |
| `:98` `allPaths_ne_nil` | `Proofs/Alignment.lean:116` | `#print axioms` at file end (:247), CI-checked; not re-run by me |
| `:102` `allPaths_complete` | `Proofs/Alignment.lean:125` | `#print axioms` at :248, CI-checked; not re-run by me |
| `:110` `alignSpec_optimal` | `Proofs/Alignment.lean:170` | `[propext, Classical.choice, Quot.sound]` |
| `Spec/Mapping.lean:73` `exists_best` | `Proofs/Mapping.lean:92` | `[propext, Classical.choice, Quot.sound]` (printed by me) |

Hypotheses: as in Spec (none extra; `exists_best` has `genome ≠ []` in Spec too). Gap: none seen. `Spec/Alignment.lean` and `Spec/Mapping.lean` are frozen by checksum (`Spec/FROZEN.sha256`).

## 2. Spec/Aligner.lean

### 2.1 `alignPairs_correct` (Spec:216) and `alignPairs_end_to_end` (Spec:232)

- Proofs: `Proofs/Aligner.lean:693` and `:753`. Target: `lake build Proofs` (lib `Proofs`, root `Proofs.Aligner`).
- Check (my scratch file, `import Proofs.Aligner`):
  `#print axioms Spec.alignPairs_correct` -> `[propext, Classical.choice, Quot.sound]`; same for `Spec.alignPairs_end_to_end` and `Spec.alignOne_correct`. No `sorryAx`.
- Hypotheses, literally. `alignPairs_correct`: `insertSettings`, `genome`, `trimmedPairs`, `byteGenome`, `hGenome : byteGenome.decode = genome`,
  `index`, `hIndex : index = buildIndex byteGenome`, `bytePairs`, `hMates : bytePairs.map decodePair = trimmedPairs`, **`hSettings : SettingsOk insertSettings`**
  where `def SettingsOk (s) : Prop := s.junkScore ≤ -16` (`Proofs/Aligner.lean:528`). `alignPairs_end_to_end`: `hGenome : GenomeIsDNA genome`,
  `hPairs : ∀ mates ∈ trimmedPairs, MatesAreDNA mates`, **`hSettings`**.
- **Flagged weaker than Spec:** the extra `SettingsOk`. Not a cheat: without it some reads have no correct answer (best pair -12, junk -10, required -16:
  the pair cannot be printed and no bound below -16 is true). Consequence: for `junkScore > -16` the theorem says nothing; the shim uses the default `-100`
  and never sets it, so the shipped binary is inside the hypothesis. Spec fix, if you want the statement exactly as in the Spec: add `junkScore ≤ -16` as a hypothesis in the Spec, or make `junkScore` ≤ `requiredMapBound` an invariant of `InsertSettings`.
- Not required by the theorem (checked in the signature): no `Fits`, no length minimum on mates (short mates go through a slow total window search), no bound on `range`
  (`range.1 > range.2` is handled in `finalize`), no `InsertSettings.dovetailSlack` condition.
- `alignPairs` as compiled is `alignPairsC` via `@[csimp] alignPairs_eqC` (`Proofs/Aligner.lean:473`); the equality is a proved theorem, so the proved function and the executed one agree (trust: Lean's `csimp`, see section 7).

Route (what each clause rests on):
- `length = trimmedPairs.length`: `alignPairs_eq_map` (`:479`), a `parMap` equals `map` (`ParMap.parMap_eq_map`).
- `alignOne_correct` (`:544`) cases: a mate `none` -> `.trimmedAway`; no index (build check failed) -> `noIndexAnswer` + `finalize` (window-by-window search, total, slow);
  index -> router `tierPair`, then `Report.answerOfPair` (re-checked CIGARs), then `LastResort.finalize`.
- Router soundness: `MapSpec.Fast.tierPair_sound` (`Aligner/mapper/TierOpt.lean:310`, printed at its `#print axioms`, standard): every tier tag's claim holds (`TierOk`, `TierRouter.lean:1140`).
  Tiers: `t1*` exact unique/tie pair searches at caps `P`; `t2/t3` bounds from a floor (`pairFloor_ok`, `t2Opt_sound`); `t2b` best from the full hit lists.
- Completeness (the "no pair" bounds): seed pigeonhole. If a placement scores at least `-c` (c ≤ 16), some seed of the read is error-free in its window
  (`exists_clean_seed_amongE`, `Aligner/mapper/lemmas/MapperEvents.lean:166`), so the minimizer lookup finds it. `hitsKPF_mem`
  (`Aligner/mapper/PairLadder.lean:469`, `c ≤ 16`) says the hit list is exactly the hits `hitsBoth` of the Spec within the cap. Lookup soundness/completeness of the index: `Mz.lookupSeed_mem` (`MzIndex.lean:1125`).
- Moving to real chromosomes: the router runs on the genome as one sequence (`Proofs/Whole.lean`: `correct_of_whole`, `alignment_shift`), proper pairs stay proper.
- Reported pair: CIGAR from an unproved fast aligner, **re-checked** by the proved `chkCand_sound` (`Aligner/mapper/TierRouter.lean:1454`); a failed check -> no pair from that path (`Proofs/Report.lean:998 answerOfPair_correct`).
- Fallbacks: `LastResort.finalize` (`Proofs/LastResort.lean:170 finalize_correct`) and the second look `lookAt` (`:421 look_not_leftover`; `pairsAt_mem` `:481`, cap ≤ 16;
  CIGAR from `bandDoublingAlign = getBestAlignment`, `cigarOk_of_hit` `:261`). A mate without enough seeds is searched window by window (total, extremely slow, not reached with the 25-letter minimum).
- Round-3 results from the branch note: chr21, 200k pairs, 13 s (mason) and 7 s (low); `none` answers 2,229 / 520.

### 2.2 `PairAnswer.Correct` clause by clause (Spec:122-157)

| clause | Spec | where proved | note |
|---|---|---|---|
| `found = some r` -> real proper pair, printed exactly, `score ≥ junkScore` | :124-130 | `Report.answerOfPair_correct`, `LastResort.finalize_correct` (drops pairs below `junkScore`), `Floor.lean:16 score_of_report` | the `junkScore` conjunct is why `SettingsOk` is needed |
| `bestPossibleScore ≥` every proper pair | :131-133 | `tierPair_sound` (`TierOk`), `Whole.correct_of_whole`, `finalize_correct` | |
| `.unique` | :136-139 | router `t1/t1g/t1u` (`TierOk`: `pairSpecUT` unique), re-printed by `answerOfPair_correct` | hyp: index passed `indexOk` (see 3) |
| `.multimapper` | :140-146 | router `t1gm/t1um` (`PairTieOk`) | |
| `.unknown`: `found = none -> bestPossibleScore < requiredMapBound` | :147-149 | `finalize_correct`, `look_not_leftover`; `lookCap_default` (`Proofs/Aligner.lean`, cap = `min 16 (-req)`) | bound limited to `-16 ≤ requiredMapBound`: the default formula satisfies it; a different `requiredMapBound` would break the method, not the Spec |
| `.repetitiveUnknown`: `found = none ∧ highlyRepetitiveIn` | :150-156 | `Proofs/GaveUp.lean:224 repeatMate_sound`; counting `count_le_occurrences` `:78` | **flag:** the proof counts only forward occurrences (reverse-complement ones are ignored): a lower bound on `Genome.occurrences`. Sound (claim is `≥`), but the tag fires less often than the Spec allows. Axioms of `repeatMate_sound`: standard (printed) |

`Tier` is "no claim" in the Spec (the comment on `inductive Tier`) and not proved; `Sam` prints it as `XT`.

### 2.3 `PairResult.Correct` (Spec:159)

Same theorem (`alignOne_correct`): `.trimmedAway .one` iff mate 1 is `none` etc.; `aligned` needs both mates. Note `alignOne` returns `.trimmedAway .one` if both are `none`; Spec accepts it (`trimmed1 = none`).

## 3. `buildIndex`

- Spec:206 is a hole. Implementation: `Proofs/Aligner.lean` `def buildIndex` (builds, `saveIndex`, `loadIndex`, runs `indexOk`; on failure writes a record of chromosome lengths instead).
- **Correctness does not depend on the index being good**: `readIndex_buildIndex` (`:487`) says the result is either the length record (-> window search) or an index that passed `indexOk`
  (`indexOk_sound`, `:69`: `cutOk`, genome bytes equal the chromosomes, `Mz.check2P`). So a wrong builder would give slow answers, not wrong ones.
- `Spec.IndexFinal.buildIndex_eq_saveIndex` (`Proofs/IndexFinal.lean:263`; lib `Proofs`): `buildIndex g = saveIndex (buildLoaded g)` **when `Fits g`**
  (`letters g + (wBytes (letters g)+4)/5 < 2^32 ∧ g.size < 2^64`, about 4.07e9 letters). This is the non-vacuity theorem ("the fast path is really taken").
  `#print axioms` -> `[propext, Classical.choice, Quot.sound]` (printed by me and at `IndexFinal.lean:279`). Also `buildIndex_ne_empty`.
  Chain: `check3P_buildLoaded` (`IndexBuild.lean:111`, needs `(Pack.catG g).length < 2^32`), `check_buildW` (`Aligner/index/minimizer/MzBuildOk.lean:1641`, `G.size ≤ 2^32+23`), `loadIndex_saveIndex` (`SaveLoad.lean:463`), `check2_sh` (`Shift.lean`).
- Hypotheses: `Fits g` only for the non-vacuity theorem. Gap: hg38 (3.1e9) is under the limit; a genome over 4.07 Gbp silently takes the slow path.
- Trusted: that the file you read back is the bytes you wrote (IO), and that `index = buildIndex byteGenome` for the genome the SAM claims (`hIndex`): nothing ties the index to the FASTA file at run time (finding 11 of the audit; sidecar).

## 4. The trimmer

The aligner theorems take already-trimmed mates (`hMates`); trimming itself is **outside** `alignPairs_correct`. What is proved about it (separately):

| claim | theorem (file:line) | check |
|---|---|---|
| window trimmer = frozen contract `get_best_window` (6 implementations) | `ReadWindow.getBestWindow*_equals_frozen_get_best_window`, certificate `Aligner/trimmer/Certificate.lean` (first at `Faster.lean:476` for Packed) | `lake env lean Aligner/trimmer/Certificate.lean`; `lake build ReadWindowTrimmer`; contract checksum `Aligner/trimmer/FROZEN_CONTRACT.sha256` |
| shipped `trimRead` = contract | `ReadTrim.trimRead_eq_contract` (`Aligner/mapper/ReadTrim.lean:407`), hyps `Q ≤ 93`, `seq.size ≤ 10000`; `trimRead` is `trimReadQ 25` | printed standard |
| every kept letter is A/C/G/T | `ReadTrim.trimRead_acgt` (`ReadTrim.lean:397`), hyp `Q ≤ 93`; `trimRead_def_acgt` (:432) | printed standard |
| adapter cut: prefix, first match, no match before, none if not cut | `AdapterTrim.cut_prefix` (:731), `cut_matches` (:739), `cut_first` (:746), `cut_none` (:751), `dropShort_size` (:759); scan = spec `fastMatchesAt_eq`; compiled = `cutPos_eq_cutPosF` | `#print axioms cut_first` standard; the file has its own `#print axioms` block (:771-778) |

Flags:
- `Spec/Fastq.lean:71 trimRecord` (glue) is unproved: it applies `cutTruSeq` (TruSeq, 13 letters, `minLen 6`, `maxErr 1`), then `trimRead`, then `dropShort minLength(25)`. The theorems above are about each piece; **their composition and the `extract` indices are checked by nobody**, and the claim "an empty result is `none`" is `Shim.chunkPairs`.
- `trimRead` returns `none` for reads over 10 000 letters, and `trimRead_eq_contract` needs `seq.size ≤ 10000`. Reads that long are trimmed away silently.
- The adapter is TruSeq only; other kits are not cut. No theorem says a trimmed mate is "good".

## 5. Kernels (`Aligner/kernels/*/Certificate.lean`)

Each Certificate file is not a build module (shared name): run `lake env lean <path>`; `CI_check.sh` does and requires `depends on axioms` lines to be standard. All ran ok here (counts from CI: band 8, gotoh 7, wfa 16, wfa_fast 26, wfa_offsets 30, wfa_runs 17, wfa_small_errors 13, wfa_u32 80, core 6, trimmer 6, Cli 4, Run 4).
Reference: `getBestAlignment` (`Proofs/core/AlignmentSpec.lean`: `_returns_some` :277, `_returns_a_valid_walk` :287, `_returns_a_maximum_score` :302; `AlignmentLexicographic.lean:105 _lex_least`, `:143 _characterization`), over `Proofs/core/Certificate.lean`.

| kernel | headline theorem (file:line) | says |
|---|---|---|
| band | `bandDoublingAlign_equals_getBestAlignment` (`kernels/band/AlignmentWavefront.lean:1251`) | equal to the reference |
| gotoh | `gotohFusedAlign_equals_getBestAlignment` (`gotoh/AlignmentAlgorithms.lean:464`) | equal |
| wfa | `wfaAlign_score` (`wfa/AlignmentWfa.lean:5073`), `_sound` (:3527), `_isSome` (:5107) | optimal score, valid path, total |
| wfa_fast | `wfaAlignI_eq` (:190), `wfaAlignF_eq` (:276), `wfaAlignL_eq` (:363) in `wfa_fast/AlignmentWfaFast.lean` | equal to `wfa` |
| wfa_offsets | `wfaAlignCA_score` / `_sound` (`wfa_offsets/AlignmentWfaArray.lean:87,91`) | score/soundness of the certified array version |
| wfa_runs | `wfaAlignK_score` / `_sound` (`wfa_runs/AlignmentWfaRuns.lean:58,70`), `wfaAlignKF_sound` (`...RunsFast.lean:49`) | runs-encoded CIGARs, checked |
| wfa_small_errors | `wfaAlignHC_score` / `_sound` (`wfa_small_errors/AlignmentCompact.lean:55,60`) | small-error fast path |
| wfa_u32 | `wfaAlignU_score` / `_sound` (`AlignmentWfaU32.lean:150,162`), `wfaAlignU3_*` (`WfaU3.lean:27,55`), `certifiedRunsU_spec` (:107) | 32-bit offsets |

Flags:
- The certificates are about the **old internal spec** (`AlignmentSpec`, `Proofs/core`), not `Spec/Alignment.lean`'s `AlignmentKernelCorrect` (`Spec/Alignment.lean:145`). The translation is `Proofs/Bridge.lean`/`Hits.lean`; no theorem instantiates `AlignmentKernelCorrect` for a shipped kernel by name (grep: it is only defined, never applied). The `Spec` kernel slot is the weak one in audit finding 7 (`.unaligned 1` satisfies it); the real guarantee is the exact-equality certificates.
- Which kernels run in the shipped binary: from code reading, the router's CIGAR comes from `TierHeur.bandDP` (unproved) and is re-checked (`chkCand_sound`); the second look uses `bandDoublingAlign`. I did not trace every call site. The `wfa*` kernels are certified but I did not verify that `Main` uses them.
- `ReadWindowProofAudit.lean` contains the forbidden-token strings on purpose (it audits them).

## 6. FASTA / FASTQ / SAM shim (`Spec/Fasta.lean`, `Fastq.lean`, `Sam.lean`, `Shim.lean`)

Nothing is proved about these. `Proofs/Fasta|Fastq|Sam.lean` are byte copies (`CI_check.sh`: "mirrors"), `Main.lean` mirrors `Spec/Shim.lean` (first line differs). Frozen: `Spec/Shim.lean` only (`FROZEN.sha256`); Fasta/Fastq/Sam are not frozen.
The theorem's interface to the shim: `bytePairs`, `index`, `byteGenome`, `hMates`, `hGenome`, `hIndex` are *assumed* to be what the shim passes. Specifically trusted:
- FASTA parse (`readFasta`): names, letters, no case/alphabet check (audit 6, 10; `audit/medium-fixes` has a fail-fast patch).
- FASTQ parse and `trimRecord` composition (4).
- `.chromosomes` sidecar (names/lengths): not tied to the index (audit 11).
- `samChunk` zips pairs with results: relies on the proved length equality (`alignPairs_correct` first conjunct); everything printed (flags, TLEN, MAPQ stand-in, tags) is unproved formatting; `reverseMapBytes` complement table equals `Spec.complement` only by reading.
- `chunkPairs` (`Spec/Shim.lean:12`): empty letters -> `none`.
- Chunking (20000 pairs) and threading: `ParMap.parMap_eq_map` is proved; the shim's own IO tasks are not.

## 7. Trusted base, complete list

1. `Spec/*.lean` definitions (frozen files `Spec/Alignment|Mapping|Aligner|Shim.lean`): that they say what you mean (audit 1-13). The theorems prove "Spec-correct", not "good".
2. Shim IO and formatting (section 6); the command line; `hGenome`, `hIndex`, `hMates` hold for the real files; the sidecar.
3. End-to-end hypotheses: `GenomeIsDNA`, `MatesAreDNA` (A, C, G, T, N only; the shim does not check them), `SettingsOk`.
4. Lean 4.35 kernel + compiler + runtime: `@[csimp]` replaces functions at compile time (72 `@[csimp]` theorems in `Aligner/`, `Proofs/`; each is a proved equation, so the replacement is justified in Lean, but codegen/the C compiler/`lean.h` runtime are not verified), `USize`/`UInt64` arithmetic in the compiled code, GMP, memory allocation, the OS. Parallelism: `Task`s.
5. Resource use: nothing bounds time or memory of `alignPairs` (slow total fallbacks exist for tiny seeds / unfittable genomes).
6. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry` outside Spec; no `native_decide`/`extern`/`unsafe`/`implemented_by` in the shim files (CI greps; `partial` is not in the CI grep list; I grepped `partial def` / `unsafe` / `@[extern` / `implemented_by` / `native_decide` over `Aligner/ Proofs/ Spec/ Main.lean`: only `Aligner/trimmer/ReadWindowProofAudit.lean` matches, as text).

## Reproduce

```
git checkout origin/speed/floor-real-spec          # proofs for the current Spec (61e4daa)
PATH=$HOME/.elan/bin:$PATH lake build              # ~7 min cold, 429 jobs
sh Testing/scripts/CI_check.sh                     # ALL CHECKS PASSED
echo 'import Proofs.Aligner
#print axioms Spec.alignPairs_correct
#print axioms Spec.alignPairs_end_to_end' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```
