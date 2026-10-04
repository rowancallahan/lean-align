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
- `codecs/LowErrorMapper.lean` (+ `pool/mapper/MapperGapless.lean`, `MapperOneIndel.lean`): exact gapless (Hamming) fast path with fallback, `mapLowError_eq_mapSpec`, `mapReadsLowError_eq_mapSpec`; gap lower bounds, single-1-letter-indel structure.
- `codecs/ParMap.lean`, `codecs/ParStream.lean`: read-batch parallel map `parMap_eq_map`, `mapReadsParArray_eq_mapSpec`; streamed batches for an overlapped writer `streamTasks_text` (joined batch texts = format of the whole result) and `streamTasks_text_mapSpec`. Writer driver: `bench/StreamBench.lean` (1M items, 4 threads: 5.3 s / 46 MB vs 7.1 s / 538 MB map-then-write).
- `codecs/EarlyStopMapper.lean` (+ `pool/mapper/MapperSeedsAmong.lean`): seeds looked up in any order, stop after seedBound(best)+1 seeds, `mapEarly_eq_mapSpec`.
- `codecs/PreFilterMapper.lean`: location filters applied before scoring give the same filtered output (`mapPreFiltered_eq`, `mapWithPreFiltered_eq`); paired-end version only sketched in a comment (no paired spec yet).
- `codecs/RepeatMask.lean`: a window with an exact copy is never reported (`mapSpec_ne_of_duplicate`); masking is safe under `DupSound` + `MaskCover` (`mapMasked_eq_mapSpec`); no index-level masked lookup proved yet.
- `codecs/ParGroup.lean`: sort reads into bins / dedup identical reads / parallel bins / restore order, all proved = `reads.map mapSpec` (`sortMap_eq_mapSpec`, `dedupMap_eq_mapSpec`, `pipelineTasks_bytes_mapSpec`). Measured: dedup and sorting do NOT pay at ~25 µs/read (distinct+table+lookup ~2.3 µs/read, in-chunk dedup misses spread duplicates); oversubscription 8 vs 4 tasks ≈ 5–10% at best. Keep as options, off by default.
- **`codecs/FastMapper.lean` (+ `pool/mapper/MapperFast*.lean`): `mapFast_eq_mapSpec` — the fast mapper (design of the tuned prototype) equals `mapSpec` for scoring (0,−4,−6,−2), T = −12, given byte-encoded genome/read and an index that passes the runtime checker `checkAll` (no trust in the builder). Reads of 100–103 letters take the fast path, others a slow proved path. v2 (lazy seed lookups, smallest bucket first, early stop, closed-form gapped penalty). chr21, 100k reads, 1 thread, this box: 254–285k reads/s vs minibwa ~30k (≈ 8×) and prototype 228–238k; answers byte-identical to the prototype. Index as little-endian ByteArrays; rolling index check 12–13 s, one-time. `codecs/FastMapperPar.lean`: `mapFastPar_eq_mapSpec` (n tasks). Same box, 4 tasks: 500–690k reads/s vs minibwa -t4 ≈ 100k (≈ 5–7×); answers identical at 1/4/16 tasks. (Fixed a 0.6 s lean_mark_mt walk by storing the index's odd-letter lists as flat ByteArrays.)**
- `codecs/FastMapperMz.lean`: the same proved fast mapper over the minimizer index (`mapFast` is generic over the seed lookup: `mapFastG_eq_mapSpec`), `mapFastMz_eq_mapSpec`, `mapFastMzPar_eq_mapSpec`. chr21, k=22 B=22: index 141 MB vs 406 MB hashed (≈ 35%); this box 190–210k reads/s 1 thread, 378k at 4 tasks, answers identical; rolling index check 17 s (`check2_eq`: same as the proved checker). Whole genome ≈ 9–10 GB at this density (smaller k/B down to ~119 MB per chr21 ≈ 8 GB). Remaining gap to hashed is per-lookup cost (~1.7k instructions per Mz lookup vs a hashed bucket scan; an oracle seed order gave no gain). Build-time fix not done: `Mz.build`'s `foldMins` rebuilds the 2^50−1 mask via `lean_cstr_to_nat` on every letter (~13% of build) — hoist it or use UInt64 (untrusted builder, checker unaffected).
- `codecs/MzIndex.lean` (+ `MapperMzWords`): minimizer index of 25-letter seeds with proved runtime checker (`lookupSeed_mem`, `mapWithMz_eq_mapSpec`).
- `codecs/SketchMapper.lean` (+ `MapperSketch`): generic sketch theorem (`mapWithSketch_eq_mapSpec`) — k-mers, minimizers (any order), closed syncmers (`closedSyncmer_hits`), variable-length keys; analysis in `bench/seed_schemes_notes.txt`: (19,7)/(17,9) minimizers + stored context = 20–25% of the every-25-mer index (≈ 4.5–5.6 GB whole genome vs ≈ 22 GB) at 85–90% of the speed.
- Index layout (final, `speed/index-layout` e8e37a5): Mz index 8 B per minimizer place, density 0.34/0.41/0.51 for k = 21/22/23; chr21 191 MB vs 743 MB, chr1 1.02 GB vs 3.82 GB; whole genome ≈ 9.3–10.7 GB (k = 21) vs ≈ 47 GB. Sorting reads by index bucket does not help (−5…−18% on chr21). A 2×50 second-pass minimizer index would cost ≈ 2.5–3 GB extra whole genome (estimate, not built); exact 50-mers at every place ≈ 23.5 GB (not viable).
- Prototype (`speed/proto-tune`, unproved), other box: ~300k reads/s 1 thread, ~620k 4 tasks, 750–930k 16 tasks; reverse strand too: ~153k 1 thread. ByteArray index removes a 3.3 s Lean `lean_mark_mt` walk when tasks share the index. Dedup is a net loss; learned seed order / 2×50 pass save ~nothing (1.54 lookups/read vs 1.53 minimum).
Still on branches: `speed/fast-proved` (proving the tuned prototype end to end), `speed/index-layout` (index memory/compression/locality), `speed/proto-tune` (unproved prototype), `speed/research` (`bench/research_notes.txt`: minibwa, SIMD, Lean vs C). Old WIP branches `speed/arrays`, `speed/bounds`, `speed/dedup-parallel` are superseded.

Data (not in repo; NCBI/UCSC blocked, GCS works): chr21 cut from the hg38 FASTA on `storage.googleapis.com/gcp-public-data--broad-references` by byte range; reads from `scripts/sim_reads.py` (forward strand, Illumina-like errors). Lean installs from the GitHub release tarball + `elan toolchain link` (release.lean-lang.org is blocked).

Measured on full chr21, 100k reads, idle 4-core box, index build excluded:
| | 1 thread | 4 threads |
|---|---|---|
| minibwa (both strands, SAM output) | ~32k reads/s (~34k excluding index load) | ~88k |
| `bench/Proto.lean` first prototype (unproved) | 512 | 1.9k |
| `speed/proto-tune` prototype (unproved, forward only, no output) | 145–155k | not measured yet |
Tuned prototype answers = first prototype answers on all 100k reads. Repeats are kept (no masking).
Stringency: wgsim reads mapped by minibwa, fraction within T = −12 (our scoring): 99.9% at 0.2% error, 99.5% at 0.5%, 97.2% at 1%.

## Baselines still to benchmark (Rowan, 2026-10-04)
minibwa is the only comparison so far. Before claiming "faster than the fastest", also run, same reads, same thread counts, idle box, index build excluded: URMAP (Edgar), BWA-MEM3 (check the name; bwa-mem2 is the known successor of bwa-mem), strobealign, minimap2 `-x sr`, Bowtie2, SNAP. Needs network access to fetch them (GitHub clones worked from the cloud environment). strobealign does not give the same guarantees (heuristic) — speed reference only, not like for like. For an exact/full-sensitivity comparison, research suggests Yara or RazerS 3. "BWA-MEM3" not known to the research session (bwa-mem2 or minibwa?). Compare only numbers taken on the same machine: on the research session's box minibwa maps 54–62k reads/s single-thread vs ~31k on this one. Online research on all of these is planned with Rowan; no downloads until then.

## Speed ideas not yet tried (Rowan, 2026-10-04)
- Reverse strand: map the reverse complement too (~2× cost); needs `MapSpec` strand support.
- Repeats / whole genome: masking exact duplicates is provable (a window in an exact copy ties → unmapped), but the mapper must still see the masked hit; diverged repeats (Alu, L1) are not multi-mappers under the spec and need a spec decision. Whole-genome 25-mer index memory (~8 bytes per position, ~25 GB) needs sampling/minimizers or a compact layout.
- Read grouping: bucket reads by their first ~10 bases (parallel sort in ~100k chunks, bins of ~1000 reads per thread) so identical or trimmed-but-identical reads share work (identical read ⇒ identical answer; a prefix-trimmed read can reuse the anchors of its untrimmed twin).
- Output: one extra writer thread collects finished batches from a queue and writes them, in input order, while worker threads keep mapping (small startup cost; fine unless disk bandwidth limits). Proof boundary: chunk → map each chunk (parallel) → de-chunk is proved equal to mapping the whole input, and the byte stream equal to format of the whole result; only the file writes are outside the proofs.
- Index (built once, cost not counted in mapping time, so spend computation there): whole genome ~30 GB at 8 bytes/position — try bit-packing positions (32-bit or fewer bits per entry, implicit bucket bits), compression that keeps lookups cheap, smaller layouts that improve cache hits; sort/lay out the index for locality.
- Seed order + early stop: with best gapless penalty P found so far, any tie-or-better window has ≤ P/4 errors, so it shows up in the hits of any P/4 + 1 seeds: stop after that many lookups (P = 0 → 1 seed). Try likely seeds first (smallest bucket, or a learned table of which seed of a pair usually hits; remember where reads map) — order is free for correctness, only the stop rule needs proof.
- Two-pass seeding: a second index of 50-letter seeds (2 per read; a read with ≤ 1 error has a clean half) settles most reads with few hits even in repeats; unsettled reads fall back to 4 × 25. Costs extra index memory.
- Seed schemes (branch `speed/seed-schemes`): minimizers, syncmers (context-free, easier proofs), skipmers, variable-length seeds (short where information-dense, long in low complexity), all behind one abstract property "exact match of length ≥ L ⇒ shared key at a computable offset" so the mapper's completeness proof only uses that property.
- Rust via Aeneas (Rust → Lean translation, proofs about the Rust code): possible 1.5–2× from no RC/boxing and bounds-check elision; parallelism and IO would sit in a trusted Rust CLI. Rowan would write the Rust CLI.
- Cache locality from read sorting: sort reads into buckets by seed code so each core works on a region of the index (fewer cache misses); optionally order the index to match.
- Threads: oversubscribe (more tasks than cores) to overlap memory stalls; batch size tuning; better multi-core scaling.
- Pre-filter by downstream flags: users filter afterwards (proper pair, MAPQ, …); a CLI filter option skips reads that cannot pass. Exact because the final position is always among the seed candidates (`LookupComplete`): if no (read-1 candidate, read-2 candidate) combination has proper-pair orientation/distance, the pair cannot be proper → drop both before any alignment. Same pattern for any filter decided by location; for multi-mapper/MAPQ filters, stop as soon as a tie between different windows is proved. Needs a paired-end spec; theorem: filtered output with pre-filter = filtered output without it.
- Two-pass (tentative): map repeat-prone / likely multi-mapping regions in a second pass.
- Multi-mappers / low MAPQ can be dropped (goal is genotyping), already what `mapSpec` does on ties.
- Kernel: plain banded DP (Smith-Waterman/Gotoh-style loop) may compile better than WFA in Lean; low-error Hamming fast path already removes most DP.

## Direction (Rowan, 2026-10-04)
- Goal now: WGS with cheap paired-end short reads (≤ 250 bp), as fast as possible. Output users keep: uniquely mapped reads in proper pairs; algorithms may exploit that (proved pre-filter: `PreFilterMapper`), with fallbacks later.
- Long run: guarantee that any placement whose surrogate-score errors are ≤ ~3% of the read length is found, so it extends to long reads. Several fast algorithms switched by read length are fine if they share the same/similar index. Note: 25-letter seeds give n/25 = 4%·n disjoint seeds, so ≤ 3%·n spoiling coordinates leave ≥ 1%·n clean seeds (≥ 1 for n ≥ 100) — the 25-mer index's pigeonhole guarantee holds up to ~4% errors at every length.
- Long-read mapping is a later goal, not now.

## Read lengths (Rowan, 2026-10-04)
Must work for reads up to ~250 bp. Fast path today: 100–103 letters only (`fastOk`), others take the slow proved path. In progress on `speed/fast-proved`: m = ⌊n/25⌋ disjoint 25-letter seeds (≥ m − 3 clean), multi-word Hamming. Rowan's decision: allow T = −16 (≤ 4 spoiling coordinates: 4 mismatches, two 1-bp indels, one gap ≤ 5, …) so ~250 bp reads at 0.5% error mostly map (reads will be trimmed). Being generalized on `speed/fast-proved`: fast path parameterised by T; two-gap windows go through the proved banded scorer (`BandScore`); ≥ 5 seeds needed at −16 (n ≥ 125 with 25-letter seeds). Builders, IO and the both-strand combine stay trusted.

## Specs Rowan plans to write
- FASTQ input spec, SAM output spec (CIGAR for the chosen window), CLI with filter options; later SAM→BAM with BAM checked as the inverse of SAM (fuzzing over BAM instead of a full BAM spec).

## Rules for all work here
- Every proof must close. If something is not provable as written, rewrite the code into a form that can be proved correct, even if slower; correctness by proof beats raw speed.
- No `sorry`, `native_decide`, `axiom`, `@[extern]`, `unsafe`, `partial`, `implemented_by` in `codecs/`, `pool/`, `spec/`.
- Do not edit `spec/AlignmentSpec.lean` (frozen) or weaken existing theorem statements.
- Do not write READMEs. New work goes on a branch; merge to `main` only when `scripts/check.sh` passes.

## Next steps
1. Merge `speed/fast-proved`, `speed/low-error`, `speed/parallel` when they pass `scripts/check.sh`; re-measure proved speed on chr21 vs minibwa at equal thread counts.
2. Grow the test genome toward chr1 / whole genome; compact index layout.
3. Wire genome + reads → SAM through `Main.lean` (`LeanAlign/Mapper.lean` has the parser and `partialSamLine`); produce the CIGAR for the chosen window.
4. Rowan: rewrite `spec/MapSpec.lean` (strand, repeats, paired-end); decide whether overlapping windows tying for best count as one locus.
