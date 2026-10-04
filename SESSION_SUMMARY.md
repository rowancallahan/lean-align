# Session summary — lean-align (last updated 2026-10-04)

Working notes for picking the work up in another session. Not a README.

## State of `main`
- `sh scripts/check.sh` prints `ALL CHECKS PASSED` (build, certificates, axioms, cross-codec check).
- Layout:
  - `spec/` — `AlignmentSpec.lean` (frozen, checksum), `MapSpec.lean` (draft mapping spec, Rowan to rewrite), `Cli.lean`, `Run.lean` (theorems about the tool).
  - `codecs/WfaU3.lean` — pairwise codec: algorithm, theorem against the spec, proof.
  - `codecs/SeedMapper.lean` — seed-and-index read mapper: algorithm, theorems, proof.
  - `pool/` — supporting definitions and lemmas (old codec folders + `pool/mapper/`).
  - `trimmer/` — read-window trimmer (frozen contract + proved chain). Library only.
  - `Main.lean`, `LeanAlign/` — the tool (`lean-align <input.seq> <output.tsv>`, pairwise only so far).
  - `bench/MapBench.lean` (`lake exe map_bench`), `scripts/gen_test.py`, `tests/`.
- No `.md` files other than this one are committed (Rowan writes the README; codec READMEs and `notes/` are untracked on disk).

## Proved about the mapper (`codecs/SeedMapper.lean`, standard axioms)
- `mapWith_eq_mapSpec`: the mapper over any lookup and scorer equals `mapSpec`, given `ValidScoring sc`, `LookupComplete g l0 lookup` (lookup returns at least every place a word occurs) and a scorer equal to `windowScore`.
- `indexMapper_eq_mapSpec`: build index + map one read = `mapSpec` (genome and read).
- `mapWithIndex_eq_indexMapper`, `mapWithIndex_eq_mapSpec`: any index equal to `buildIndex l0 g`.
- `mapReads_eq_mapSpec`: one index, many reads.
- Indels and affine scoring are covered. `ValidScoring`: match ≤ 0, mismatch < 0, gapOpen ≤ 0, gapExtend < 0.

## Baseline speed (`map_bench`, 200 reads of 100 bases, T = −12, l0 = 12)
| Genome | Index build | Mapping | Reads/s |
|---|---|---|---|
| 5 × 1 kb | 0.005 s | 1.9 s | 104 |
| 5 × 20 kb | 1.1 s | 8.9 s | 23 |

Every mapped read is at its true position. Slow because everything is `List Char` and each seed hit scores (2k+1)² = 169 windows.

## Speed work in progress (branches, each must prove `= mapSpec` and pass `scripts/check.sh`)
- `speed/arrays` — array-backed genome, integer-hash index (collisions allowed; only `LookupComplete` needed). New file `codecs/SeedMapperArray.lean`, theorem `mapReadsArray … = reads.map (mapSpec …)`.
- `speed/bounds` — fewer seeds and windows using affine gap costs (separate bounds for spoiled seeds and for shift/length). New `pool/mapper/MapperWalk2.lean`, `codecs/SeedMapper2.lean`.
- `speed/dedup-parallel` — score each window once, drop out-of-bounds windows before scoring; `mapReadsPar` with `Task.spawn`, theorem `= reads.map f`.
See the branch tips' commit messages for what is finished on each.

## Rules for all work here
- No `sorry`, `native_decide`, `axiom`, `@[extern]`, `unsafe`, `partial`, `implemented_by` in `codecs/`, `pool/`, `spec/`.
- Do not edit `spec/AlignmentSpec.lean` (frozen) or weaken existing theorem statements.
- Do not write READMEs. New work goes on a branch; merge to `main` only when `scripts/check.sh` passes.

## Next steps
1. Finish and merge the three speed branches; re-measure.
2. Grow the test genome toward human chromosome 1; the index layout will need a compact form at that scale.
3. Wire genome + reads → partial SAM through `Main.lean` (`LeanAlign/Mapper.lean` has the parser and `partialSamLine`); produce the CIGAR for the chosen window.
4. Compare with minibwa.
5. Rowan: rewrite `spec/MapSpec.lean`; decide whether overlapping windows tying for best count as one locus.
