# CODEMAP: the code below Spec/, for a language model (agent-facing; humans read Spec/)

Purpose: find the right file and name fast, with the fewest tokens. `Spec/` is the contract (Rowan's; frozen files in
`Spec/FROZEN.sha256`). Everything here is implementation + proof that the implementation meets `Spec/`. Proof route by
Spec clause, with hypotheses and gaps: `Testing/notes/PROOF_MAP.md` (read that for "why is this correct").
Generated parts (module table) come from `Testing/scripts/codemap_table.py`; rerun it after moving code.

## 1. The pipeline (what runs, in order)

Executable `lean-align` = `Main.lean` (mirror of `Spec/Shim.lean`, frozen):
- `build GENOME.fa INDEX`: `Spec.Fasta` reads → `Spec.buildIndex` (= `Proofs/Aligner.lean` `buildIndex`: minimizer index
  `MzIndex` over a 2-bit packed genome `PGen`, the heavy 25-mer table `Proofs/HeavyBuild.lean`, checked by `indexOk`) → bytes.
- `map INDEX R1 R2 OUT min max`: `Spec.readChunk` (FASTQ, `Spec/Fastq.lean`) → `Spec.trimChunk` → `Spec.trimRecord`
  (`AdapterTrim.cutTruSeq`, then `ReadTrim.trimRead` best quality window, then `dropShort`) → `Spec.alignPairs` →
  `Spec.samChunk` (`Spec/Sam.lean`).

`Spec.alignPairs` (hole in Spec) = `Proofs/Aligner.lean` `alignPairs`, compiled as `alignPairsC` (`@[csimp] alignPairs_eqC`):
`readIndex` once, then per pair (`ParMap.parMapS`, 16 tasks) `alignOneP`:
1. `tierPairBP.tierPairBQ` (Aligner/mapper/TierRouter.lean): the router. Seeds of both mates looked up in the minimizer index
   (`mzLookSP`, `MzWord.lean`), pass kernels `routeGS` → `passGSF` (gapless `hamWU`, one-indel `ilG*`, band `ker16KWG`/`kerGKG`),
   tiers `t1*` exact unique/tie, `t2/t3` floors, `t2b` best from full hit lists. `tierUp` (TierOpt.lean) lifts tiers.
2. `Report.answerOfPairP` (Proofs/Report.lean): turns the router's placements into a printed pair, every CIGAR re-checked
   (`chkCand*`, `checkMove`); no pair → the walk `fallbackOfKP` → `walkAt` → `nearAt` → `nearOf` → `TierHeur.nearY`
   (seed vote `seedVote`/`voteD`, gapless `hamW`, banded DP `bandAln`/`bandDPg`/`bandCellsJ`).
3. `LastResort.finalize`: drops pairs below `junkScore`, fixes the answer's bound.
4. `orElse` chain (`afterRouter`), each stage only if the answer so far is a leftover (`LastResort.Leftover`):
   `joinAt` (rarest-seed join, `tierNo`) → short mates `lookAt` → `gaveUp` (heavy 25-mer witnesses, Proofs/GaveUp.lean,
   `Heavy.heavyMate`) → `lookAt` (Proofs/LastResort.lean: the second look `pairsAt` → `hitsKPF` (PairLadder.lean) →
   `hitsAtKP` → `hitsSK` → `hitsCKT` (PairHitsKP.lean) → diagonal filter `kfiltVF` / `wordFilterPacked` (was `kfiltVP`) (FastGenWordFilt.lean,
   FastGenSupp.lean) → kernels `kerHKG`).

The diagonal filter (second look and router stage K): support count `suppCntC` (sweep), unlooked 25-mer seeds `unseenSeedsOkWords`
(`seedAnyRoll` rolling window), 8-letter pieces `piecesEnough` (compiled `piecesEnoughWord` → `wordPieces` → `laneScanRoll`, lane test `laneZeros`).

## 2. Proof architecture (how the code is tied to Spec)

- `Proofs/*.lean` (top level) state exactly the Spec theorems (mirrors checked by CI: `Proofs/Answer.lean` ↔ `Spec/Aligner.lean`,
  `Proofs/{Fasta,Fastq,Sam}.lean` ↔ `Spec/…`). Headline: `Spec.alignPairs_correct`, `Spec.alignPairs_end_to_end`
  (`Proofs/Aligner.lean`, extra hypothesis `SettingsOk`: `junkScore ≤ -16`, see PROOF_MAP §2.1).
- `Proofs/core/` (lib `Core`): the internal model the kernels are proved against (`AlignmentSpec`, `MapSpec`, `PairSpec*`),
  translated to Spec in `Proofs/Bridge.lean`.
- Every fast executed function is an exact `@[csimp]` equality `slow = fast` (`_eq*` theorem next to the fast def). Proofs are
  about the slow/simple definition; the compiler runs the fast one. To change speed: add a fast def + prove `@[csimp]`.
- Heuristic code with no value theorem (re-checked downstream instead): `TierHeur.*` (walk partner search, band DP),
  router CIGARs (re-checked by `chkCand_sound`). Changing it can change output but not soundness.
- WFA kernels (`Aligner/kernels/wfa*`): proved, mostly not on the current path; kept for longer reads.

## 3. Invariants and conventions (true everywhere unless a comment says otherwise)

- Genome letters: bytes `A C G T` = 65 67 71 84; other bytes never match a read letter. Packed: 2 bits per letter
  (`PGen`, `dig`), non-ACGT runs stored apart (`PGen.slow`, 64-letter blocks flagged; `winOk` = window all-ACGT).
- Reads: `ByteArray` of ACGT after trimming (`trimRecord_correct`), length 25..~250; `Rr` = reverse complement.
- Scores: `sc0` = match 0, mismatch −4, gap open 6 + 2 per letter (penalties as `Nat`, scores as `Int ≤ 0`).
  `lim`/`Q`/`P` = penalty caps; `gapBound sc0 (-Q)` = most gap letters within `Q`; `sbound Q = Q / 4` = seeds a window within `Q` can spoil.
- Seeds: 25-letter grid seeds `j * Ls` (`Ls = n / (n / 25)`), looked up via minimizers; anchors are `16 * diagonal + flags`
  (`a / 16` = diagonal `D`, start of the read on the genome + n). Pieces: 8-letter (`pl`), 4 per 64-bit word (16-bit lanes).
- Machine-word loops run only under explicit bounds (`< 2^30`/`2^31`), checked by the `F` wrapper; otherwise the slow copy (`S`).
- Determinism: SAM must be byte-identical across speed changes; test = `Testing/repro/ir.sh` subsets + `cmp`, CI `FUZZ=1`.

## 4. Where to look for X

| X | file : name |
|---|---|
| the main theorem | Proofs/Aligner.lean : `alignPairs_correct`, `alignOne_correct` |
| what `alignPairs` runs | Proofs/Aligner.lean : `alignOneP`, `afterRouter`, `alignPairsC` |
| tuning constants (caps, budgets, flags) | Proofs/Aligner.lean : `capOfLen`, `gateBudget`, `joinBudget`, `walkK`, `lookCap`, `deepCaps` |
| index build / load / check | Proofs/Aligner.lean : `buildIndex`, `saveIndex`, `loadIndex`, `indexOk`; Aligner/index/minimizer/MzIndex.lean |
| seed lookup | Aligner/index/minimizer/MzWord.lean : `lookupPW`, `mzLookSP`; MzIndex.lean : `lookupSeed_mem` |
| packed genome | Aligner/index/packed_genome/MapperPGen.lean : `PGen`, `rawU` |
| router tiers and their claims | Aligner/mapper/TierRouter.lean : `TierOk`, `tierPairBP`; TierOpt.lean : `tierPair_sound` |
| pigeonhole (a clean seed exists) | Aligner/mapper/lemmas/MapperEvents.lean : `exists_clean_seed_amongE` |
| diagonal filter | Aligner/mapper/FastGenWordFilt.lean : `wordFilterPacked`, `piecesEnough_eqC`; FastGenSupp.lean : `kfiltVF`, `suppCntC` |
| second look | Proofs/LastResort.lean : `lookAt`, `pairsAt`; PairLadder.lean : `hitsKPF`; PairHitsKP.lean : `hitsCKT` |
| printed pair re-check | Proofs/Report.lean : `answerOfPairP`, `checkMove`; TierRouter.lean : `chkCand_sound` |
| walk / partner search (heuristic) | Proofs/Report.lean : `fallbackOfKP`, `walkAt`; Aligner/mapper/TierHeur.lean : `nearY`, `bandDPg` |
| repeat give-up (`repetitiveUnknown`) | Proofs/GaveUp.lean : `repeatMate_sound`; Proofs/Heavy.lean : `heavyMate` |
| trimming | Aligner/mapper/ReadTrim.lean : `trimRead`, `wl_eq_wlF`; Aligner/trimmer/AdapterTrim.lean : `cutTruSeq_eqF` |
| alignment kernels | Aligner/kernels/k250 (word kernels), gapless, mapper_band, band, gotoh; wfa* (kept) |
| parallel map | Aligner/mapper/ParMap.lean : `parMapS`, `parMap_eq_map` |
| CI | Testing/scripts/CI_check.sh (`FUZZ=1` adds the output fuzz) |
| speed measurement | Testing/repro/ir.sh (callgrind Ir on 2k pairs); Testing/notes/NEW_FILTER.md (recent levers) |

## 5. Glossary of name fragments (verified in code; capital = suffix on a def name)

Suffixes on a def: `F` compiled (fast) version, target of a `@[csimp]`; `S` slow path copy (not rewritten); `U` machine words
(`USize`/`UInt64`); `V`, `W` word/vector version; `R` rolling window; `C` compiled wrapper / with counts; `P` packed genome
or given a precomputed value; `N` variant with an extra precomputed argument; `T` tabled/specialised; `K` packed read (`RP`)
or kernel; `G` generic over `GRead`; `B` bytes / band; `L`/`M` list/merge variants; `2`,`3` successive rewrites.
Theorem suffixes: `_eq`, `_eqF`, `_eqC`, `_eqT` … `@[csimp]` or equality with the slow def; `_sound`, `_mem`, `_correct`
claims against the model; `_iff`, `_bit`, `_dig` bit-level lemmas.
Fragments: `pk` packed index `PkMz`; `ix` index; `Mz` minimizer; `pgs` packed chromosomes; `gbs` chromosome bytes; `offs`/`ns`
chromosome offsets/lengths; `R` read bytes, `Rr`/`Rs` strand; `K` packed read `RP`; `acc` anchor arrays per looked-up seed;
`J` looked-up seeds, `us` the others; `Ls` seed spacing; `D` diagonal; `sb` spoil bound `sbound`; `fJ` failed seeds;
`lim`/`Q`/`P` caps; `ker*` kernel; `ham` Hamming; `il` one-indel; `kfilt` diagonal filter; `fine` the 8-letter piece filter;
`unlook` the not-looked-up seeds; `sv` seed word; `gs`/`GW` loaded genome words; `gAt` 32 fields at an offset; `dig` 2-bit
digit; `comb` two words shifted into one; `lane` 16-bit lane of a word; `zt` lane-zero test; `supp` seed support of a diagonal;
`rc` reverse complement; `tb` traceback; `wl` window fold (trimmer); `sa` shift-and (adapter); `t1/t2/t3` router tiers;
`walk` fallback walk; `near` partner near an anchor; `look` lookup / second look; `floor` report floor; `heavy` 25-mer with ≥200 copies.

## 6. Proposed naming scheme (token-efficient; pilot: §8)

Goal: every identifier piece is a common English word (1 BPE token) or a fixed one-letter suffix; no invented 2-4 letter
abbreviations (they cost 1-3 tokens each and need this glossary).
- Words, camelCase: `wordFilter` not `kfiltV`; `seedAny` not `svAny`; `laneZeros` not `zt`; `windowAt` not `gAtW`.
- Fixed suffix words instead of letters: `…Fast` (the `@[csimp]` target), `…Slow` (not rewritten), `…Word` (machine-word
  loop), `…Roll` (rolling window). Theorems: `<def>_eq` (`@[csimp]` or slow = fast), `<def>_spec` (vs Spec/model),
  `<def>_bit` (bit-level). Successive rewrites get a word (`Hoist`, `Swept`), not a digit.
- One prefix word per layer only when names would clash (`index…`, `route…`, `report…`, `trim…`); namespaces stay.
- Keep the math: single letters for bound variables in proofs (`i j k n`), and Spec names unchanged.
- Rename mechanically: a script maps old → new on identifier boundaries across the tree (code, comments, notes),
  one module per commit, CI + SAM check per commit; optional `@[deprecated] abbrev old := new` for external notes.

## 7. Size (below Spec: every `.lean` under Aligner/, Proofs/, Testing/)

Token proxy (no tokenizer installed): identifiers split at camelCase / `_` / digits; a piece that is a dictionary word
(lowercase words of ≥ 3 letters used ≥ 3 times as prose in the repo's comments and notes, 2.6k words) = 1 token, any other
letter piece = ⌈len/2⌉, a digit run = ⌈len/3⌉, a punctuation run = 1. Same dictionary for before and after.

| | files | lines | chars | proxy tokens |
|---|---|---|---|---|
| festive e7ecb81 | 274 | 94,931 | 4.45M | 1.48M |
| exp/codemap (dead code removed) | 221 | 70,841 | 3.27M | 1.09M (−27%) |

Liveness: module reachability from `Main`, the `Proofs` library and every CI-run file; then a constant-level pass over the
elaborated environment (types, values, `@[csimp]` targets; roots `Main`, `Spec.*`, `Proofs.*`, names in CI-run files, WFA
modules). At the start: 63 unreached files (16.8k lines) and 1,804 unreached declarations (~12.5k lines) in live files.
Removed: 49 files and ~9.6k lines of declarations. Left on purpose: the WFA kernels; `ReadWindowTrimmer/` (frozen contract);
`UniqueGenome` (separate research proofs, built by CI), `BandCellsJProof`, `CheckFastestEquivalence`, `AuditAlignPairs`
(checks of live code); ~1,000 unreached declarations that something still mentions (unused `simp` arguments, structures,
instances), and ~90 the last sweep did not finish.
Where the tokens are now: proofs (theorem bodies) 72%, executable definitions 24%, other 4%; comments ~10% overall; the kept
WFA kernels 22% of all tokens. Median file 188 lines; 4 files over 1,500 lines (`AlignmentWfa.lean` 5,131).

## 8. Naming pilot: FastGenWordFilt.lean

50 definitions renamed (map in commit d8597bb, e.g. `kfiltVP`→`wordFilterPacked`, `fineE`→`piecesEnough`,
`lanesAnyR`→`laneScanRoll`, `svAny`→`seedAny`, `gAtW`→`windowAt`, `zt`→`laneZeros`, `GPk`→`PackedOf`), with the theorems
named after them, across 8 files; CI + SAM identical. `RInv` was skipped (also defined in `MzBuildOk`).
Proxy for the file: 33,905 → 34,147 tokens (+0.7%), chars +4.6%; dictionary-word pieces 5,862 → 6,892 (+18%), abbreviation
fragments 12,253 → 11,514 (−6%). So whole-word names do not save tokens (the short abbreviations were cheap); they buy
readability per token (an agent can guess `laneScanRoll`, not `lanesAnyR`) and remove the need for the §5 glossary.
Script lesson: a rename must skip local variables with the same short name (`wf` was also a `Bool` parameter in `TierHeur`).

## 9. Recommendations for keeping more of the code in an LLM's context

1. Split executable code from proofs (biggest lever: proofs are 72% of tokens). One file with the definitions an agent
   reads to know what runs, one companion file with the theorems; fast defs and their `@[csimp]` lemmas must stay before the
   code that uses them, so keep those in the code file and move every other lemma out. All executed code (~250k proxy
   tokens) then fits in one context.
2. One module per pipeline stage (§1 numbering): router, report/walk, second look, give-up, trimmer, index; today a stage is
   spread over 5-15 files (`PairLadder`, `PairHitsKP`, `FastGenSupp`, `FastGenWordFilt`, …).
3. A fixed 5-line header per file: purpose; the definition that runs; the theorem tying it to Spec/model; csimp pairs;
   status (live / heuristic / kept). The generated table (§11) stays in CODEMAP.
4. Remove historical comments ("was 83M", measurements, old branch names) from code; keep them in notes; keep the one-line
   doc per definition.
5. Files under ~800 lines; split `AlignmentWfa.lean` (5.1k) and the 1.3-1.9k-line mapper files along the code/proof seam.
6. Move the WFA kernels (22% of tokens, mostly unused today) under a clearly named `kept/` subtree so searches can skip them.
7. Delete superseded csimp chains: keep one slow def and one fast def per function (e.g. `laneScan` still carries
   `laneScanWord`/`laneScanMask`/`laneScanCached` only for its slow path).
8. Regenerate CODEMAP's table (`Testing/scripts/codemap_table.py`) and re-run reachability before each cleanup.

## 10. Estimate for a full below-Spec refactor

- Remaining dead code (~1,000 kept declarations): 0.5-1 day with the error-driven pruner (each build resolves a few names;
  most of the cost is waiting for builds); low risk.
- Rename everything to the scheme (~3,000 project definitions): mechanical with the boundary-aware script plus a
  local-variable check, ~40 module-sized commits (CI ~10 min + SAM check each): 1-2 days of machine time, plus ~1 day
  reviewing the maps for clashes. Risk medium-low (compile errors are loud; SAM identity is the safety net).
  `@[deprecated] abbrev` aliases are only needed for names cited in notes or other branches; generate them from the map.
- Code/proof split and one module per stage: 3-5 days; risk medium (import cycles, csimp order, `private` defs used by
  proofs). File by file, CI + SAM per commit; never change a definition body in the same commit as a move.
- Proof updates: none for pure renames and moves (statements unchanged); only where a definition body is simplified.
- Total about 1-1.5 weeks of agent time, mostly build/CI waiting; parallelisable by area once the scheme is fixed.
- Keeping output identical throughout: every commit builds, `FUZZ=1 CI_check.sh` passes, and `cmp` of SAM on the 2k NovaSeq +
  HiSeq subsets against one fixed reference binary built from the starting commit (as done on this branch).

## 12. Further levers (measured with the §7 proxy; % of the 1.09M below-Spec tokens)

| lever | measured | saved | notes |
|---|---|---|---|
| WFA kernels out of the default context (`kept/`, not read unless asked) | 239k in `kernels/wfa*` | **21.9%** | no code change; largest lever |
| Non-doc comments (`--`, `/- -/`) moved to CODEMAP/notes | 51k non-WFA | **4.7%** | docstrings kept |
| Docstrings cut to their first line | 37k → 29k | 0.7% | |
| Proof compression (combinators, `simp_all`, `<;>`, no restated goals) | prototype below | **~5% (3.6-7%)** | 15% (10-20%) of the 391k non-WFA proof-body tokens |
| Repeated hypothesis lists bundled (`variable` or one `Prop` def) | 173k non-WFA statement tokens; e.g. `hchr`/`hslice` lists 14-15x | ~1-2% (not prototyped) | changes theorem statements, so callers change |
| `open` for project namespaces (`MapSpec.Fast.`, `U32Proof.`, …) | 6.1k prefix tokens − 1.6k for the `open` lines | 0.4% | library prefixes (`List.`, `Nat.`, 13.5k) cannot be dropped: root-name clashes (`add_comm`, …); `R.`/`G.` are local structure variables |
| Boilerplate | `#print axioms` 3.3k, `variable/omit/include` 3.6k, `import`/`namespace`/`end` 3.5k, `set_option` ~0 | ~0.3% | only the `#print axioms` lines can move (to one checker file); the rest is needed |
| Fewer, longer whole-word names | §8 pilot | ~0% (+0.7%) | readability, not size |

Proof-compression prototype (`codemap/proof_compression_FastGenSupp.diff`, compiled with `lake env lean`, file restored afterwards):
7 of the 19 theorems of `FastGenSupp.lean` rewritten (`advP_eqF`, `modify_eq`, `getD_modify`, `stageKSP_eq`, `sortedL_pw`,
`incA_pw`, `suppA_cons`): 1,248 → 949 tokens (−24%) for those theorems, module 6,908 → 6,609 (−4.3%), its proofs −6.7%.
Typical moves: `by_cases … <;> simp_all`, `split <;> first | rfl | …`, `simpa … using` instead of `have`+`rw … at this`,
`(try subst_vars; rw [h0]) <;> rfl` instead of a restated `have hs : (if … ) = …` (the biggest single cut). The 7 were the easy
ones; long induction proofs (`sweepA_spec`, `flag_eq`) shrink less, hence 10-20% of bodies tree-wide. Cost: 1-3 compiles per
theorem (≈1.7 min each). Downsides: `simp_all` / `<;>` scripts are harder for an agent to repair and break more often on a
Lean or core-lemma change; elaboration time not measured.

Projection: default context today 1.09M (festive 1.48M). WFA out → 852k; comments + docstrings −59k; proofs −59k;
bundled hypotheses −10-20k; `open` + boilerplate −8k ⇒ **≈ 710-720k (−34% vs now, −52% vs festive)**. Without moving WFA:
≈ 950k (−13%). Separately, the code/proof split (§9.1) gives an executed-code-only view of ~250k.

Proxy vs a real tokenizer (none available here: no network for `pip`, no API key for token counting): (a) dots are free
in the proxy, so qualified prefixes are undercounted (lever 1 maybe 0.5% instead of 0.4%); (b) Unicode symbols
(`→ ≤ ∀ ⟨ ⟩ ·`) and punctuation runs count 1, while BPE tokenizers often spend 1-3 tokens per symbol, so symbol-dense proofs are
undercounted (real proof share higher, comment share lower than shown, e.g. 8% not 10%); (c) unknown abbreviations at
⌈len/2⌉ is a guess (BPE: 1-3 per fragment); (d) indentation counts 0 (real: ~1 per line, ~70k for the tree).
Expected: real totals 1.0-1.4× the proxy; per-lever percentages within about ±30% relative; the ranking (WFA ≫ comments ≈
proof compression ≫ the rest) should hold. Calibrating needs one real count (e.g. the API's token counting on 3-4 files).

## 11. Modules (generated by `python3 Testing/scripts/codemap_table.py`; lines in parentheses; Key = most-referenced defs)

### Aligner/LeanAlign/

- `Cli.lean` (24) Command line (pure) Key: `parse`, `Config`.
- `Run.lean` (89) Bytes in, bytes out (pure) Key: `run`, `scoring`, `mergeRuns`, `alignPair`, `alignLines`, `stepLetter`.

### Aligner/index/csr/

- `CsrIndex.lean` (129) Codec `CsrIndex`: compact k-mer index with a certified completeness checker Key: `getU32`, `setU32`, `CsrIndex`. csimp: `getU32`→`getU32F`.

### Aligner/index/kmer/

- `MapperFastIndex.lean` (777) Codes -/ Key: `c2N`, `MatchAt`, `LookOk`, `Good`, `Run`, `MIXINV`.

### Aligner/index/minimizer/

- `MapperMzWords.lean` (329) Letters -/ Key: `acgt`, `wcGo`, `firstOdd`, `allA`, `eqRun`, `wcU`.
- `MzBuildOk.lean` (1645) The minimizer-index builder passes its checker Key: `ix0`, `RInv`, `runStep`, `runsOf`, `flat`.
- `MzCheckFast.lean` (163) A faster `Mz.check`: rolling window code in the completeness pass Key: `check2`, `compR`, `rollTo`, `roll`.
- `MzCheckPar.lean` (90) Codec `checkAllMzPar`: the minimizer-index checker on several cores Key: `checkSoundPar`, `soundChunk`, `check3`.
- `MzIndex.lean` (1323) Codec `MzIndex`: minimizer index of 25-letter seeds, certified by a checker Key: `MzIdx`, `check`, `zeros`, `slot`, `hsh`, `posOf`. csimp: `miniGo`→`miniGoF`.
- `MzView.lean` (341) Whole genome with one genome copy: the concatenation as a view of the chromosomes Key: `get`, `ofChroms`, `catOkV`, `buildWV`, `RepV`, `eqRunV`.
- `MzWord.lean` (1130) Bucket entries checked with one genome word Key: `lookupPW`, `lookupPWk`, `seedLE`, `okAtW`, `scanAW`. csimp: `seedLE`→`seedLEF2`, `slotW`→`slotWF`, `scanAWK`→`scanAWK3`, `lookupPW`→`lookupPWK`.

### Aligner/index/packed_genome/

- `MapperPGen.lean` (405) Compact genome: 2 bits per letter plus the exact non-ACGT runs Key: `PGen`, `push`, `code`, `letter`, `get`, `view`. csimp: `exFind`→`exFindF`, `PGen.raw`→`rawF`.
- `MapperPacked.lean` (218) Nat layer: base-4 digits -/ Key: `dig`, `rep`, `cntNZ`, `cnt64`.
- `MzBuildP.lean` (86) The packed-genome and view builders pass the packed checker
- `MzPacked.lean` (245) Minimizer index checker and builder over a packed genome Key: `unpack`, `check2P`, `buildWP`, `foldMinsP`, `wcGoP`, `allAP`.
- `WgPacked.lean` (791) Codec `pairDispatchKP`: whole genome held once, 2-bit, word kernels, length dispatch Key: `kerHKG`, `insN`, `check3P`, `mapChromsGBKG`, `foldUpN`, `isortN`. csimp: `gappedLG`→`gappedLGF`, `GS.advFG`→`GS.advFGL`, `ilGFG`→`ilGFGW`, `mapChromsGBFG`→`mapChromsGBFGK`.

### Aligner/kernels/band/

- `AlignmentWavefront.lean` (1217) An adaptive, wavefront-style alignment algorithm with an UNCONDITIONAL Key: `ReasonableScoring`, `bandLo`, `bandHi`, `bandDoublingAlign`, `walkStats`, `statsScore`. csimp: `bMkMain`→`bMkMainF`, `bandedRun`→`bandedRunK`.
- `Certificate.lean` (35) Proof certificate: codec folder `band`

### Aligner/kernels/gapless/

- `MapperGapless.lean` (158) A gapless walk scoring at least `T` has a clean seed at its own offset -/ Key: `hamming`, `agree`, `gapCost1`.
- `MapperOneIndel.lean` (14) Soundness: a one-letter deletion gives a walk scoring `gapOpen + gapExtend` -/

### Aligner/kernels/gotoh/

- `AlignmentAlgorithms.lean` (483) Fast implementations of the frozen alignment specification, each proved to Key: `bellmanAux`, `lastRow`, `gapYCost`, `gapXCost`, `diagCost`, `gotohFusedAlign`.
- `Certificate.lean` (33) Proof certificate: codec folder `gotoh`

### Aligner/kernels/k250/

- `FastGenK250.lean` (794) Codec `pairFastGBK`: `pairFastGB` with the word kernels Key: `revCompK`, `Ker`, `prepGK`, `advF`, `mapChromsGBK`, `kerHK`. csimp: `revCompLoop`→`revCompLoopF`, `stageKF`→`stageKFN`, `revCompK`→`revCompKF`.
- `MapperK250.lean` (1201) Word kernels for short reads (≤ 256 letters) over the packed genome Key: `packRP`, `pre`, `gword`, `fold`, `lowF`, `getU`. csimp: `gword`→`gwordF`, `hamW`→`hamWF`, `fwdW`→`fwdWF`, `bwdW`→`bwdWF`….
- `MapperK250Bits.lean` (133) Bit lemmas for the word kernels
- `MapperK250Chunk.lean` (204) Chunks: packed read against the packed genome
- `MapperK250Loops.lean` (400) Word loops = byte loops Key: `WOk`, `WOkB`.
- `MapperK250Seed.lean` (216) Seed hashes from the packed read Key: `seedHashK`, `revF`, `beCode`.
- `MapperK250Sel.lean` (347) Selecting set fields Key: `Bin`.
- `MapperK250Spec.lean` (170) `gappedPen3` and `kerG3` (byte level)
- `MapperK250Words.lean` (177) Word kernels = byte kernels

### Aligner/kernels/mapper_band/

- `BandScore.lean` (127) Codec `bandScore`: capped banded score-only window scorer Key: `GenomeBytes`, `bandScore`.
- `MapperBandBytes.lean` (304) The pruned banded pass on bytes (default scoring `sc0`). Key: `bandRowsCB`, `bandEndCB`, `toIntRow`, `bandLoopB`, `cellB`.
- `MapperBandFast.lean` (255) Proof -/ Key: `bandLoop`, `bandEnd2`, `bandRows2`, `CellRelP`, `RowShape`.
- `MapperBandKernel.lean` (194) The grid of true values -/ Key: `Encodes`, `cellVals`, `bandRow`, `bandEnd`, `DeadRow`, `seg`.
- `MapperBandProof.lean` (266) The row loop -/ Key: `pOf`, `Valid`, `CellDead`.
- `MapperBandPrune.lean` (576) The pruned pass -/ Key: `bandRowsC`, `bandEndC`, `blocksAbove`, `ExactAt`, `prefCnt`, `bandEndP`.
- `MapperBandSpec.lean` (198) Optimal suffix score -/ Key: `bandOf`, `Rel`, `thr`, `BandOK`.

### Aligner/kernels/wfa/

- `AlignmentExchange.lean` (505) The greedy match-extension lemma: on a matching head pair, the frozen
- `AlignmentWfa.lean` (5131) TRUE WFA: furthest-reaching wavefronts over penalty levels. Key: `WCell`, `wfaPo`, `wfaPx`, `wfaPe`, `TFront`, `stepWith`.
- `Certificate.lean` (58) Proof certificate: codec folder `wfa`

### Aligner/kernels/wfa_fast/

- `AlignmentWfaFast.lean` (385) Executed-path variants of the proven WFA, each proven EQUAL (as a Key: `wfaAlignL`, `wfaAlignI`, `wfaAlignF`.
- `AlignmentWfaFused.lean` (413) Fused banded wavefront step. Key: `mapTake`, `zipMapExt`, `padMapK`, `nextLevelF`, `zipPadRK`, `zipPadR`.
- `AlignmentWfaLazy.lean` (105) Lazy candidate selection for the gap fronts. Key: `stepPairY`, `stepPairX`, `stepDiag2`.
- `AlignmentWfaLazyLevel.lean` (338) The fused level (`nextLevelF`) with the overlap combine made a Key: `nextLevelL`.
- `Certificate.lean` (106) Proof certificate: codec folder `wfa_fast`

### Aligner/kernels/wfa_offsets/

- `AlignmentWfaArray.lean` (103)  Key: `walkCheckA`, `wfaAlignCA`, `wfaRunArray`.
- `AlignmentWfaCertified.lean` (274) Offsets-only WFA with a checked traceback. The forward recurrence is proved Key: `traceJoff`, `rgetI`, `wfaAlignC`, `wfaRunR`, `wfaLoopR`, `certifiedTraceR`.
- `AlignmentWfaDirect.lean` (72) Generated by generate_wfa_direct.py. Three materialized arrays, scalar
- `AlignmentWfaLcp.lean` (52) 
- `AlignmentWfaOff.lean` (655) Offsets-only view of the proven wavefront (layer O) Key: `joffOf`, `lcp`, `OLevelW`, `cornerO`, `betterO`, `nextLevelO`.
- `AlignmentWfaOffLoop.lean` (185) Layer O, the loop: the corner level determines the optimal score Key: `wfaLoopO`, `wfaRunO`.
- `AlignmentWfaOffR.lean` (892) Banded, array-backed offsets-only wavefront level (layer R) Key: `rget`, `BLevel`, `RFront`, `betterR`, `pushYR`, `pushXR`.
- `AlignmentWfaPoint.lean` (169) Pointwise wavefront recurrences with exactly the same stored bands. Key: `pointY`, `pointX`, `nextLevelP`, `pointM`.
- `AlignmentWfaView.lean` (261) Deferred array expressions. Only final wavefront arrays are materialized. Key: `viewR`, `packV`, `mapV`, `zipV`, `VFront`, `shiftUpV`.
- `Certificate.lean` (115) Proof certificate: codec folder `wfa_offsets`

### Aligner/kernels/wfa_runs/

- `AlignmentCigarCheck.lean` (136)  Key: `checkRuns`, `checkRepeatFast`, `WalkCursor`. csimp: `checkRepeatFast`→`checkRepeatFastI`.
- `AlignmentCigarCheckFast.lean` (342) A faster run checker, proven equal to `checkRuns` Key: `checkRunsFast3`.
- `AlignmentTraceRuns.lean` (75) Generated by generate_run_trace.py. Offset traceback emits whole diagonal Key: `traceRuns`.
- `AlignmentWfaRuns.lean` (102)  Key: `wfaAlignK`, `certifiedRuns`.
- `AlignmentWfaRunsFast.lean` (62) `wfaAlignKF`: the proven kernel `wfaAlignK` with its runtime run checker Key: `wfaAlignKF`.
- `AlignmentWfaRunsVsWfa.lean` (31) Function-level equality of the fast kernels with the proven `wfaAlign`, on
- `Certificate.lean` (77) Proof certificate: codec folder `wfa_runs`

### Aligner/kernels/wfa_small_errors/

- `AlignmentCompact.lean` (77) Compact tracebacks. Expansion occurs in the theorem, not in the fast path. Key: `expandCigar`, `compactSmall`, `wfaAlignHC`, `unitCigar`.
- `AlignmentSmallErrors.lean` (163) An exact shortcut for equal-length inputs with at most two substitutions. Key: `wfaAlignH`, `smallDiag`, `diagCheckA`.
- `Certificate.lean` (60) Proof certificate: codec folder `wfa_small_errors`

### Aligner/kernels/wfa_u32/

- `AlignmentWfaU32.lean` (203) `wfaAlignU`: the padded UInt32 kernel, proven Key: `wfaAlignU`.
- `AlignmentWfaU32Ext.lean` (184) `uext2 = uext`
- `AlignmentWfaU32Fill.lean` (495) Hot cell loop of the second UInt32 kernel (definitions) Key: `srcBase`, `srcArr`, `cellY2`, `cellX2`, `cellS`, `cellM2`.
- `AlignmentWfaU32Fill3.lean` (199) Block-layout level builder (definitions) Key: `toU`, `BLevel`, `srcSh3`, `srcArr3`, `srcOf3`, `blockOf`.
- `AlignmentWfaU32FillS.lean` (81) Single-source level builder (definitions) Key: `uLoopS`, `uLevelS`, `uLevelSBody`.
- `AlignmentWfaU32FillSSpec.lean` (200) Functional specification of the single-source cell loop `uFillS`: after the
- `AlignmentWfaU32FillSpec.lean` (142) Functional specification of the cell loop `uFillGo2`: after the loop, index
- `AlignmentWfaU32FillSpec3.lean` (154) Functional specification of the block-layout cell loop `uFillGo3`
- `AlignmentWfaU32Kernel2.lean` (341) `wfaAlignU2`: the second UInt32 kernel, proven
- `AlignmentWfaU32Kernel3.lean` (209) Optimality of the executed block-layout run and the checked kernel. -/
- `AlignmentWfaU32Lattice.lean` (379) Lattice property of the offsets-only run Key: `gcdU`, `wfaRunOP`.
- `AlignmentWfaU32Level.lean` (315) UInt32 arithmetic foundations for padded wavefronts Key: `ULevel`, `ubetter`, `uEmpty`, `upushD`, `upushY`, `upushX`.
- `AlignmentWfaU32Level2.lean` (362) The hot-loop level builder computes the proven builder's arrays
- `AlignmentWfaU32Level3.lean` (351) Refinement of the block-layout builder to the proved three-front builder. -/ Key: `BWF`.
- `AlignmentWfaU32LevelS.lean` (357) The single-source level denotes `nextLevelR`'s M front
- `AlignmentWfaU32Loop.lean` (207) The padded UInt32 run equals the proven offsets-only run Key: `seedU`, `udenL`, `uRun`, `uLoop`.
- `AlignmentWfaU32Loop3.lean` (217) Block-history bookkeeping
- `AlignmentWfaU32Run2.lean` (188) The second UInt32 kernel: loop, run, traceback, kernel (definitions) Key: `wfaAlignU2`, `ucode2`, `uRunS`, `certifiedRunsU2`, `uRunD`, `uRun2`.
- `AlignmentWfaU32Run3.lean` (133) The third UInt32 kernel: general path in the block layout (definitions) Key: `certifiedRunsU3`, `acceptRuns`.
- `AlignmentWfaU32Single.lean` (143) Equal penalties: the X and Y fronts come from the M front alone
- `AlignmentWfaU32Step.lean` (941) The padded UInt32 level step denotes `nextLevelR` Key: `uget`, `frontAtU`, `WFA`, `pushZeros`, `uLevel`, `ugetA`.
- `Certificate.lean` (248) Proof certificate: codec folder `wfa_u32` — PARTIAL FOUNDATIONS, NO ALIGNMENT OPTIMALITY CLAIM
- `ProbeU32.lean` (290) SPEED PROBE — NOT A KERNEL, NOT PROVEN, NOT IN THE HARNESS. Key: `uget`, `ULevel`, `pushZeros`, `uLevel`, `ubetter`, `uEmpty`.
- `WfaU3.lean` (116) Codec `wfaAlignU3` Key: `wfaAlignU3`.

### Aligner/mapper/

- `BandCellsJProof.lean` (263) `bandCellsJ` = `bandCells` (so `bandDPg true = bandDPg false`)
- `EarlyStopMapper.lean` (62) Codec `mapEarly`: seed lookups in any order, stopping early Key: `seedCands`.
- `FastGen.lean` (66) Codec `mapFastTG`: the general fast mapper, any read length and threshold Key: `LookAllG`.
- `FastGenAlgo.lean` (479) The general fast mapper: any read length, any threshold `T = −P` Key: `sbound`, `fastT`, `ordG`, `dst`, `wlen`, `suppA`. csimp: `diags`→`diagsM`, `suppA`→`suppAC`.
- `FastGenCover.lean` (38) Coverage for the general fast path
- `FastGenCoverE.lean` (149) Coverage with the event-based pigeonhole (`exists_clean_seed_amongE`): a window
- `FastGenCoverL.lean` (17) `cover` for any lookup length `l` (`MatchAtL`: `l` letters match), for seeds Key: `MatchAtL`.
- `FastGenMz.lean` (68) The general fast mapper through a minimizer index Key: `mzLookS`.
- `FastGenPair.lean` (925) Codec `pairFastGB`: the general path on both strands, one concatenated index Key: `cwB`, `prepG`, `decB`, `cwS`, `mapChromsGB`, `live`. csimp: `sliceG`→`sliceGE`.
- `FastGenPairPacked.lean` (400) Codec `pairFastGBP`: the general pair mapper over a packed genome Key: `PkMz`, `mzLookSP`, `SameA`, `mapFastGBP`.
- `FastGenProof.lean` (1284) Proof of the general fast mapper (part 1: windows) Key: `cwT`.
- `FastGenSupp.lean` (446) Seed support of all diagonals in one sweep (`suppCntC`) Key: `advF`, `suppCntC`, `stageKSS`, `kfiltVF`, `incA`. csimp: `sweepA`→`sweepAF`, `stageKSP`→`stageKSPW`.
- `FastGenWordFilt.lean` (1852) The diagonal filter by words (`wordFilter = kfilt`) Key: `get`, `PackedOf`, `stageWordFilter`, `getU`, `wordFilter`, `packedFor`. csimp: `loadWords`→`loadWordsWord`, `windowAt`→`windowAtFast`, `seedAny`→`seedAnyFast`, `laneScanMask`→`laneScanCachedStart`….
- `FastMapper.lean` (101) Codec `mapFast`: the fast proved read mapper Key: `decodeGenomeB`, `checkAll`, `scanLookup`.
- `FastMapperMz.lean` (253) Codec `mapFastMz`: the fast mapper through a minimizer index Key: `MzP`, `mzPrep`, `anc`, `checkAllMz`, `mzSize`, `scanA`.
- `LowErrorMapper.lean` (62) Codec `mapLowError`: exact Hamming fast path for near-perfect reads
- `MateFloor.lean` (91) Mate floors from seeds with no exact copy
- `PairBnB.lean` (105) Branch and bound on the pair score (`pairSpecUT`) Key: `ScoreFun`.
- `PairBox.lean` (73) Box certificates for `bestPairD` (pair-level uniqueness)
- `PairConcat.lean` (208) Codec `pairFastC`: one index over the concatenated genome Key: `next`, `catOk`, `adv`, `lbA`, `sliceA`, `IncA`.
- `PairConcatPacked.lean` (67) Codec `pairFastCP`: one packed concatenated genome, one index Key: `cutAll`, `cutOk`.
- `PairDispatch.lean` (51) Codec `pairDispatch`: each mate at a threshold set by its length Key: `penOf`, `pairSpecT`, `pairDispatch`.
- `PairExact.lean` (126) `pairGXE`: the best proper pair at pair score `≥ −Gc`, `Gc ≤ 16` (gapped mates) Key: `pairGXE`.
- `PairGuarFast.lean` (448) The fast pair-level guarantee (`pairGF`), proved Key: `scanW`, `partnerK`, `hitsS3`, `hitsAtKP3`, `pairsGF`, `hitsAtB3`.
- `PairGuarQ.lean` (848) The fast pair-level guarantee at `pairGX`'s speed (`pairGQ`), proved Key: `goP`, `chromOf`, `pairGQC`, `stopP`, `PkMzR`, `InvQ`. csimp: `rawLookP`→`rawLookPD`, `pscanC`→`pscanD`.
- `PairGuarQB.lean` (75) `pairGQ`, part (b): the word reject keeps the partner scan
- `PairGuarQC.lean` (268) `pairGQ`, part (c): the early-stop fold, proved
- `PairGuarQD.lean` (55) `pairGQ`, part (d): the pair-level guarantee
- `PairGuarQE.lean` (514) `pairGQC`: the fast `pairGQ` (cached partner words, global diagonal X hits)
- `PairGuarantee.lean` (43) Codec `pairGK`: the pair-level guarantee at total penalty `G`
- `PairHits.lean` (456) Every hit of a read within a cap (`hitsC`, one chromosome, one strand) Key: `slicesAt`, `hitsAtB`, `hitsS`, `hitsC`.
- `PairHitsKP.lean` (410) `hitsAtKP`: every hit of a read within a cap, packed genome, word filter, word kernels Key: `hitsAtKP`, `hitsSK`, `hitsCK`. csimp: `hitsCK`→`hitsCKT`, `hitsSK`→`hitsSKV`.
- `PairHybrid.lean` (31) Mode H: the region pipeline first, the cap ladder on what it leaves
- `PairInterleave.lean` (29) Codec `pairFastI`: both strands interleaved, one lookup at a time
- `PairJoin.lean` (607) Codec `noPairJ`: no proper pair of hits, from the seed anchors of both mates Key: `noPairJ`, `noPairJS`. csimp: `noPairJS`→`noPairJSA`.
- `PairJoint.lean` (33) Codec `pairFastJ`: joint strand search (one shared `Best`) and proper pairs
- `PairLadder.lean` (135) Codec `pairUKP`: pair-level uniqueness (`pairSpecUT`), fast path + cap ladder Key: `hitsKPF`, `topW`, `PairTieOk`, `topStep`.
- `PairLadderF.lean` (173) `pairUKPF`: the proper-pair mode with linear pairing Key: `properPairsF`, `bestOfPairs`.
- `PairMapper.lean` (115) Codec `pairFast`: both strands and proper pairs, through the proved fast mapper Key: `revCompB`, `strandScore`, `complB`.
- `PairNear.lean` (383) The ladder with the second mate searched near the first only Key: `hitsKPFN`, `keepN`, `NearOk`. csimp: `hitsCKN`→`hitsCKNT`, `hitsKPFN`→`hitsKPFNG`.
- `PairPacked.lean` (184) Codec `pairFastIP`: the interleaved pair mapper over a 2-bit genome Key: `okAtP`, `scanAP`, `lookupPP`, `lookupSeedAP`, `lookupCodeAP`, `LookPk`.
- `PairReason.lean` (143) Why a pair is not reported: reasons, proved against the specification Key: `sel`, `other`, `Mate`, `searched`, `Reason`, `ReasonOk`.
- `PairRegion.lean` (747) Codec `pairRegionKP`: the second mate is first searched only near the first Key: `prepMate`, `PrepM`, `costP`, `RgMz`, `regionB`, `regionNoHitKP`. csimp: `costP`→`costPK`.
- `PairRouter.lean` (738) Codec `routeKP`: pass kernels in sequence, unmapped pairs with a reason Key: `swap`, `MateR`, `routeG`, `regionPenKP`, `mateKP`, `cap2Of`.
- `PairUnique.lean` (103) Codec `pairFastU`: pair-level uniqueness (DRAFT spec `pairSpecU`)
- `ParMap.lean` (112) Codec `parMap`: map an array in parallel Key: `parMap`, `batch`, `parMapS`.
- `ParStream.lean` (53) Codec `streamTasks`: map in batches, write while mapping
- `ReadTrim.lean` (570) Codec `trimRead`: the proved read-window trimmer on FASTQ bytes Key: `rtGet`, `trimRead`, `isACGT`. csimp: `wl`→`wlF`.
- `SeedMapper.lean` (218) Codec `indexMapper`: seed-and-index read mapper Key: `Index`, `lookup`, `buildIndex`, `LookupComplete`, `mapWith`, `candidates`.
- `SeedMapper2.lean` (77) Codec `indexMapper2`: seed-and-index read mapper with sharper bounds Key: `shapes`, `KeepComplete`.
- `TieCut.lean` (609) Tie cut: after a tie at penalty `p`, the gapped stage runs at cap `p − 1` Key: `mapChromsGBT`, `mapChromsGBKGT`, `mapChromsGBFGPOT`, `mapChromsGBFGT`. csimp: `ilGFGT`→`ilGFGWT`.
- `TierHeur.lean` (1000) Router helpers the tier router is run with (moved from Testing/benches/WholeGenome.lean, mode RTX). Key: `bandCells`, `hamW`, `rowStart`, `bandCellsJ`, `bandDPg`, `nearY`. csimp: `winL`→`winLF`, `smallK`→`smallKF`.
- `TierOpt.lean` (328) The tier router's last step: tier 2 pairs promoted to `T1u`, `T1um` or `T2b` (`tierPair`) Key: `tierPair`, `tierNo`, `tierUp`.
- `TierRouter.lean` (1845) The tier router (`tierPairB`): mode RTX's decisions, proved Key: `TierOut`, `MateX`, `TierOk`, `TierCfg`, `prepMz`, `strandRead`. csimp: `rescoreRuns`→`rescoreRunsA`, `emptyCnt`→`emptyCntS`, `tierPairB`→`tierPairBS`.

### Aligner/mapper/lemmas/

- `MapperBytes.lean` (219) Bytes ↔ letters -/ Key: `byteCode`, `decodeBytes`, `decodeGenome`, `codeOfWord`, `codeNat`, `encodeGenome`.
- `MapperDefs.lean` (25) Shared definitions for the seed-and-index mapper. -/ Key: `ValidScoring`, `errBound`, `wordsOf`, `buildTable`.
- `MapperEvents.lean` (253) Event-based pigeonhole.  `errReps` charges every inserted read letter (a Key: `seedBoundE`.
- `MapperFastAlgo.lean` (748) Fast mapper: the executable code (definitions only) Key: `Best`, `acgt`, `cap`, `result`, `BIAS`, `u32`. csimp: `hamming`→`hammingF`, `fwdMis`→`fwdMisF`, `bwdMis`→`bwdMisF`.
- `MapperFastBest.lean` (120) The running best window (`Best`) and its invariant. Key: `Inv`, `win`, `Dom`.
- `MapperFastBytes.lean` (150) The byte-level penalty -/ Key: `cntP`, `gapLen`, `misB`, `skipOf`, `preB`, `penGap`.
- `MapperFastKernel.lean` (270) `gappedPen2`: first and last mismatches -/
- `MapperFastLazy.lean` (777) Anchor arrays for a partial set of seeds -/ Key: `bit`, `LoopState`.
- `MapperFastLoop.lean` (113) One-gap windows -/ Key: `cwG`, `GapL`.
- `MapperFastMerge.lean` (287) The anchors of a read -/ Key: `seedBit`, `maskAt`, `Fits`, `SortedA`.
- `MapperFastScore.lean` (446) Walk shapes -/ Key: `sc0`, `penOf`, `minUpTo`, `misIns`, `misDel`.
- `MapperFastSupport.lean` (310) Seeds and penalties (lemma (d) of the plan): which anchors a hit window has.
- `MapperGRead.lean` (25) Genome letter access Key: `GRead`.
- `MapperGen16.lean` (578) Penalty exactly `16` (scoring `(0, −4, −6, −2)`). Key: `twoGapB`, `filt16`, `twoGapAt`.
- `MapperGenBest.lean` (193) `Best` and its invariant for any penalty cap `P` (`MapperFastBest` is `P = 12`). Key: `InvP`, `initP`, `resultP`.
- `MapperGenLook.lean` (183) Seed lookups at any read offset `s`, writing `(p + base)·16 + bit` for each Key: `LookG`, `seedHashAt`, `LookOkS`.
- `MapperGenScore.lean` (361) Window penalties capped at any `Q`, exact up to `lim = min Q 15`. Key: `kerG`, `penQ`.
- `MapperGenSearch.lean` (109) Near-linear helpers for the general mapper's stages. Key: `anyNear`, `dedupAdj`.
- `MapperGenShare.lean` (123) Mismatch profiles shared across window shapes. Key: `twoGapBP`, `fwdProf`, `bwdProf`, `filt16P`, `gappedPen2P`.
- `MapperInterleave.lean` (87) Interleaved lazy lookups of two reads (the prototype's `mapStreams`) Key: `next`, `adv`.
- `MapperLists.lean` (154) List and table membership lemmas for the seed-and-index mapper. -/
- `MapperSeedsAmong.lean` (22) Clean seed among any chosen seeds.  `exists_clean_seed2` with the seeds
- `MapperWalk.lean` (285) A walk scoring at least `T` leaves one of `errBound + 1` seeds untouched. -/ Key: `errCoords`.
- `MapperWalk2.lean` (377) Sharper bounds for the seed-and-index mapper, using the affine gap cost. Key: `cnt`, `runs`, `gapBound`, `mism`, `gapBound2`, `seedBound`.

### Aligner/trimmer/

- `AdapterTrim.lean` (878) Adapter trimming Key: `scan`, `mismatches`, `st1`, `dropShort`, `cutTruSeq`, `st0`. csimp: `cutPos`→`cutPosF`, `cutTruSeq`→`cutTruSeqF`.
- `Certificate.lean` (26) Proof certificate: read-window trimmer
- `CheckFastestEquivalence.lean` (66) The contract theorem for the fastest current trimmer
- `ReadWindowProofAudit.lean` (45) 
- `ReadWindowTrimmer.lean` (1) 

### Aligner/trimmer/ReadWindowTrimmer/

- `Contract.lean` (198)  Key: `baseScore`, `get_best_window`, `quality_score_greater10`, `window_score`.
- `Faster.lean` (492)  Key: `result`, `PackedFoldState`, `getBestWindowPacked`, `packedFoldStep`, `initialPackedFoldState`, `getBestWindowFoldr`.
- `Fused.lean` (133)  Key: `getBestWindowFused`, `fuseBestWindowsFrom`, `FusedResult`.
- `Incremental.lean` (119)  Key: `scoreWindowsStartingAt`, `scoredWindowsIncremental`, `getBestWindowIncremental`.
- `Linear.lean` (374)  Key: `extendPrefixSummary`, `getBestWindowLinear`, `bestCandidatesSpecification`, `scoredWindowsLinear`, `bestPrefixSummary`.
- `Reference.lean` (82)  Key: `Window`, `allWindows`, `scoredWindowsExhaustive`, `getBestWindowExhaustive`, `scoreWindow`, `getWindow`.

### Proofs/

- `Aligner.lean` (841) 3. The aligner, proved. `Spec/Aligner.lean`'s types are in `Proofs/Answer.lean` (unchanged); Key: `limOf`, `saveIndex`, `buildLoaded`, `buildIndex`, `indexOk`, `loadIndex`. csimp: `reqOf`→`reqOfF`, `alignPairs`→`alignPairsC`.
- `Alignment.lean` (249) 1. Alignment, proved. Same statements as `Spec/Alignment.lean`, with the proofs filled in. -/ Key: `Step`, `Scoring`, `score`, `scoreWalk`, `Read`, `allPaths`.
- `Answer.lean` (204) 3. The aligner: what each answer proves. Statements only. Key: `decodeRead`, `Mate`, `InsertSettings`, `report`, `report`, `MateReport`.
- `Bridge.lean` (339) Bridge: the existing router proofs (old spec: windows, hits, thresholds) → the new spec. Key: `oldGenome`, `oldPlacement`, `newPlacement`, `CorrectU`, `answerOf`, `newStrand`.
- `Build.lean` (400) What the minimizer builder makes (`Index.buildMz` with k=22, B=26, c=0, 5-byte slots, t=6) Key: `ix0`, `runStep`, `cnt1`.
- `Fasta.lean` (53) The genome FASTA and the saved chromosome list. Unproved (trusted) plumbing for the shim; Key: `ChromosomeList`.
- `Fastq.lean` (149) Paired FASTQ reading. Unproved (trusted) plumbing for the shim: the file is read in 4 MB blocks Key: `line`, `trimRecord`, `FastqRecord`, `minLength`, `trimChunk`, `parseRecord`. csimp: `allBytes`→`allBytesF`.
- `Floor.lean` (53) The report floor: pairs below `junkScore`, and proofs that no good proper pair exists Key: `repScore`.
- `GaveUp.lean` (400) Giving up on repeats (Spec's `.repetitiveUnknown`) Key: `chromGo`, `seedPlaces`, `seedCount`, `inChrom`. csimp: `repeatMate`→`repeatMateF`, `decodeRead`→`decodeReadF`.
- `Heavy.lean` (349) The heavy 25-mer table: an O(log n) `highlyRepetitiveIn` witness Key: `entryOk`, `heavyMask`, `heavyMate`, `heavyOk`. csimp: `capCount`→`capCountF`, `heavyMask`→`heavyMaskP`, `heavyOk`→`heavyOkP`.
- `HeavyBuild.lean` (86) Builder of the heavy 25-mer table (NOT proved: `Proofs/Heavy.lean`'s check `heavyOk`, run at build time in Key: `code`, `letter`, `table`, `hidx`, `thr`, `pass2`.
- `Hits.lean` (186) Helpers for B2 (hits ↔ alignments), independent of `Proofs/Bridge.lean`. Key: `newStepOf`, `pathOfWalk`, `oldStrandOf`.
- `Index.lean` (169) The index layer: build, save, load, check (helpers for `Proofs/Aligner.lean`). Key: `pad`, `putNat`, `putNats`, `putBytes`, `putU64`, `offsOf`.
- `IndexBuild.lean` (117) The built minimizer index passes the router's check
- `IndexFinal.lean` (288) The index builder is right: `buildIndex g = saveIndex (buildLoaded g)` when the genome fits Key: `letters`, `Fits`.
- `LastResort.lean` (792) The last step: the report floor Key: `noPair`, `runsOf`, `readLens`, `fitNs`, `finalize`, `lookAnswer`.
- `Mapping.lean` (148) 2. Mapping, proved. Same statements as `Spec/Mapping.lean`, with the proofs filled in. Key: `score`, `score`, `Placement`, `Genome`, `empty`, `reference`.
- `Pack.lean` (870) The genome packer is right (`Proofs/Index.lean`'s `packAll`, `offsOf`) Key: `cnt`, `Inv`, `catL`, `catG`, `offL`, `wBytes`.
- `Report.lean` (1192) M2: reporting the found pair (placements and CIGARs) Key: `chromOf`, `mergeRuns`, `chromGo`, `mateReportOf`, `monoOk`, `answerOfPairP`. csimp: `chromOf`→`chromOfL`, `diagPen`→`diagPenH`.
- `Sam.lean` (154) SAM output: two lines per pair, with the pair answer in custom tags (XB best possible pair Key: `stepLetter`, `cigarText`.
- `SaveLoad.lean` (553) Save, then load (`Proofs/Aligner.lean`'s `saveIndex` / `loadIndex`) Key: `obOf`, `mOf`, `bigOf`, `Pre`, `MzFits`.
- `Shift.lean` (311) The loaded minimizer index passes the checker when the built one does Key: `Shifted`.
- `Tiers.lean` (48) Tiers: facts about the old router's tier specs used by `answerOf_correct` (B6)
- `TrimRecord.lean` (263) `trimRecord` composes: what the FASTQ glue's trimming guarantees
- `Whole.lean` (150) The whole genome as one chromosome Key: `shift`, `wholeOf`.

### Proofs/core/

- `AlignmentLexicographic.lean` (160) The tie-break characterization theorem: the path returned by the frozen
- `AlignmentSpec.lean` (322)  Key: `Step`, `Scoring`, `scoreWalk`, `yConsumed`, `xConsumed`, `IsMonotoneWalk`.
- `Certificate.lean` (30) Proof certificate: frozen alignment specification
- `Cli.lean` (45) What is proved about the command line
- `MapSpec.lean` (70) Read-mapping specification (DRAFT, for Rowan to rewrite; not frozen) Key: `Genome`, `Window`, `windowScore`, `windowSeq`, `Chromosome`, `mapSpec`.
- `PairSpec.lean` (93) Both strands and proper pairs (DRAFT, for Rowan to review/rewrite; not frozen) Key: `Placement`, `hitsBoth`, `Strand`, `mapSpecBoth`, `revComp`, `properPair`.
- `PairSpecTier.lean` (43) Tier-1 mapping: the cap from the read length (DRAFT, for Rowan to review/rewrite; not frozen) Key: `capOf`.
- `PairSpecU.lean` (84) Pair-level uniqueness with per-mate caps (`pairSpecUT`; DRAFT for Rowan, not frozen) Key: `pairScoreD`, `PairHit`, `dcost0`, `properPairs`, `properPairU`, `pairSpecUT`.
- `Run.lean` (56) What is proved about the computation