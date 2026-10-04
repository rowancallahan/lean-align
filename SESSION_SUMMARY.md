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

## Speed work, session of 2026-10-04 (branch `claude/upbeat-goldberg-kizkfd`)
Merged here and passing `scripts/check.sh` (not yet on `main`):
- `codecs/SeedMapper2.lean` (+ `pool/mapper/MapperWalk2.lean`): 4 seeds, 19 windows per seed hit, optional full-seed filter; `mapWithK_eq_mapSpec`, `mapWith2_eq_mapSpec`, `mapWith2V_eq_mapSpec`.
- `codecs/BandScore.lean` (+ `pool/mapper/MapperBand*.lean`): `ScoreFaithful` (exact at scores ≥ T), banded capped score-only kernel over ByteArray, `bandMapper_eq_mapSpec`.
- `codecs/CsrIndex.lean` (+ `pool/mapper/MapperBytes.lean`): byte genome, CSR 2-bit index, runtime `checkIndex … = true → LookupComplete` (a saved/loaded index needs no trust), `mapWithCsr_eq_mapSpec`.
Still on branches: `speed/fast-proved` (proving the tuned prototype end to end), `speed/low-error` (gapless / one-gap lemmas), `speed/parallel` (`parMap_eq_map`), `speed/proto-tune` (unproved prototype), `speed/research` (`bench/research_notes.txt`: minibwa, SIMD, Lean vs C). Old WIP branches `speed/arrays`, `speed/bounds`, `speed/dedup-parallel` are superseded.

Data (not in repo; NCBI/UCSC blocked, GCS works): chr21 cut from the hg38 FASTA on `storage.googleapis.com/gcp-public-data--broad-references` by byte range; reads from `scripts/sim_reads.py` (forward strand, Illumina-like errors). Lean installs from the GitHub release tarball + `elan toolchain link` (release.lean-lang.org is blocked).

Measured on full chr21, 100k reads, idle 4-core box, index build excluded:
| | 1 thread | 4 threads |
|---|---|---|
| minibwa (both strands, SAM output) | ~32k reads/s (~34k excluding index load) | ~88k |
| `bench/Proto.lean` first prototype (unproved) | 512 | 1.9k |
| `speed/proto-tune` prototype (unproved, forward only, no output) | 145–155k | not measured yet |
Tuned prototype answers = first prototype answers on all 100k reads. Repeats are kept (no masking).
Stringency: wgsim reads mapped by minibwa, fraction within T = −12 (our scoring): 99.9% at 0.2% error, 99.5% at 0.5%, 97.2% at 1%.

## Speed ideas not yet tried (Rowan, 2026-10-04)
- Reverse strand: map the reverse complement too (~2× cost); needs `MapSpec` strand support.
- Repeats / whole genome: masking exact duplicates is provable (a window in an exact copy ties → unmapped), but the mapper must still see the masked hit; diverged repeats (Alu, L1) are not multi-mappers under the spec and need a spec decision. Whole-genome 25-mer index memory (~8 bytes per position, ~25 GB) needs sampling/minimizers or a compact layout.
- Read grouping: bucket reads by their first ~10 bases (parallel sort in ~100k chunks, bins of ~1000 reads per thread) so identical or trimmed-but-identical reads share work (identical read ⇒ identical answer; a prefix-trimmed read can reuse the anchors of its untrimmed twin).
- Output: one extra writer thread collects finished batches from a queue and writes them, in input order, while worker threads keep mapping (small startup cost; fine unless disk bandwidth limits). Proof shape: the pure part is "bytes written = concat over batches, in order, of format (map read)"; the queue/IO stays in `Main.lean`.
- Threads: oversubscribe (more tasks than cores) to overlap memory stalls; batch size tuning; better multi-core scaling.
- Pre-filter by downstream flags: users filter afterwards (proper pair, MAPQ, …); a CLI filter option could skip reads that cannot pass (e.g. mates whose seeds cannot form a proper pair) — needs a paired-end spec and a theorem that skipped reads are exactly the filtered ones.
- Multi-mappers / low MAPQ can be dropped (goal is genotyping), already what `mapSpec` does on ties.
- Kernel: plain banded DP (Smith-Waterman/Gotoh-style loop) may compile better than WFA in Lean; low-error Hamming fast path already removes most DP.

## Specs Rowan plans to write
- FASTQ input spec, SAM output spec (CIGAR for the chosen window), CLI with filter options; later SAM→BAM with BAM checked as the inverse of SAM (fuzzing over BAM instead of a full BAM spec).

## Rules for all work here
- No `sorry`, `native_decide`, `axiom`, `@[extern]`, `unsafe`, `partial`, `implemented_by` in `codecs/`, `pool/`, `spec/`.
- Do not edit `spec/AlignmentSpec.lean` (frozen) or weaken existing theorem statements.
- Do not write READMEs. New work goes on a branch; merge to `main` only when `scripts/check.sh` passes.

## Next steps
1. Merge `speed/fast-proved`, `speed/low-error`, `speed/parallel` when they pass `scripts/check.sh`; re-measure proved speed on chr21 vs minibwa at equal thread counts.
2. Grow the test genome toward chr1 / whole genome; compact index layout.
3. Wire genome + reads → SAM through `Main.lean` (`LeanAlign/Mapper.lean` has the parser and `partialSamLine`); produce the CIGAR for the chosen window.
4. Rowan: rewrite `spec/MapSpec.lean` (strand, repeats, paired-end); decide whether overlapping windows tying for best count as one locus.
