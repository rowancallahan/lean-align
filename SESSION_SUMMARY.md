# Session summary — lean-align (last updated 2026-10-05)

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
minibwa is the only comparison so far. Before claiming "faster than the fastest", also run, same reads, same thread counts, idle box, index build excluded: URMAP (Edgar), BWA-MEM3 (check the name; bwa-mem2 is the known successor of bwa-mem), strobealign, minimap2 `-x sr`, Bowtie2, SNAP. Needs network access to fetch them (GitHub clones worked from the cloud environment). strobealign does not give the same guarantees (heuristic) — speed reference only, not like for like. For an exact/full-sensitivity comparison, research suggests Yara or RazerS 3. "BWA-MEM3" exists (bioconda package bwa-mem3); minibwa paper: arXiv 2606.15357 (~4× BWA-MEM, >2× bwa-mem2). Compare only numbers taken on the same machine: on the research session's box minibwa maps 54–62k reads/s single-thread vs ~31k on this one. Online research on all of these is planned with Rowan; no downloads until then.

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

## Merge status (2026-10-04, late)
`claude/upbeat-goldberg-kizkfd` holds all verified work: every proof branch plus `speed/proto-tune` (bench/Proto.lean = tuned unproved prototype, Proto0 = first prototype, bench/check.sh, map_dump) and `speed/research` (bench/research_notes.txt, Proto2). `scripts/check.sh` passes; all lean_exe targets build. Proved mapper after `Look` class / shared per-seed prep (6653355), chr21 100k reads, 1 thread, this box: hashed 376k reads/s, Mz (k=22, 141 MB) 349k, answers identical to the prototype. Also merged: both-strand check `fast_bench FAST_BOTH=1` (bench-level strand combine, proved mapper per strand): chr21.both.r100k hashed 50.7k / 159k reads/s (1/4 tasks), Mz 42.5k / 134k; 90,669 mapped, 90,539 at true position + strand; byte-identical to PROTO_BOTH; symmetry 100,000/100,000. Both strands cost ~6× one strand (the wrong strand runs all lookups + gapped stage). Mod-minimizer (`modMinimizerMapper_eq_mapSpec`, SketchMapper): (19,7,t=5) 0.152 entries/base, (15,11,t=4) 0.113/base, ≈ 3.1–4.2 GB whole genome at 8 B/entry; literature lower bound for such schemes ≈ 0.115–0.154/base at L = 25. Left out on purpose: `speed/arrays`, `speed/bounds`, `speed/dedup-parallel` (old WIP, superseded) and the last two `speed/csr-index` commits (parallel/low-memory CsrIndex checker; they change `MapperBytes.lean` on an old base and break MzIndex; CsrIndex itself is superseded by the fast mapper's checked index).

## Direction (Rowan, 2026-10-04)
- Goal now: WGS with cheap paired-end short reads (≤ 250 bp), as fast as possible. Output users keep: uniquely mapped reads in proper pairs; algorithms may exploit that (proved pre-filter: `PreFilterMapper`), with fallbacks later.
- Long run: guarantee that any placement whose surrogate-score errors are ≤ ~3% of the read length is found, so it extends to long reads. Several fast algorithms switched by read length are fine if they share the same/similar index. Note: 25-letter seeds give n/25 = 4%·n disjoint seeds, so ≤ 3%·n spoiling coordinates leave ≥ 1%·n clean seeds (≥ 1 for n ≥ 100) — the 25-mer index's pigeonhole guarantee holds up to ~4% errors at every length.
- Long-read mapping is a later goal, not now.
- Speed target (Rowan): faster than BWA-MEM3 (Fulcrum fork of bwa-mem2; ~48k reads/s/thread with --fast per its own benchmark) and minibwa (~8× bwa-mem, so likely near URMAP). Some modes accept only proper pairs: that removes most of the both-strand cost (mates on opposite strands within the insert range → seed both mates together, score only anchor pairs that can form a proper pair; exact by the proved pre-filter). Prototype in progress on `speed/proto-tune`. First step merged (c28f833): both strands searched jointly (shared best, next lookup goes to the strand with fewest) — chr21.both.r100k 127–154k reads/s, 3.08 lookups/read (was 50–55k, 4.25), output byte-identical; `sim_reads.py SIM_PAIRED=1` for pairs. Paired proper-pair prototype merged (737beed, `PROTO_PAIR=<mate2>`; exact = per-mate mapSpec on both strands, then proper-pair filter; checked byte-identical to `bench/pair_ref.py` brute reference on 100k chr21 pairs, 88,794 kept): this box 1 thread 83–101k pairs/s = 165–202k reads/s; minibwa paired -t1 ≈ 3.8 s mapping for 100k pairs ≈ 26k pairs/s (minibwa also does mate rescue/SAM). Still unproved; proved path needs Rowan's strand + pair spec. General-length/T fast path stages 1–3 proved on `speed/fast-proved` (merged). Not merged yet: `speed/index-layout` be0d6f8 (context width c in the Mz tag) — breaks `FastMapperMz.lean` until its lookup section is updated.

## Read lengths (Rowan, 2026-10-04)
Must work for reads up to ~250 bp. Fast path today: 100–103 letters only (`fastOk`), others take the slow proved path. In progress on `speed/fast-proved`: m = ⌊n/25⌋ disjoint 25-letter seeds (≥ m − 3 clean), multi-word Hamming. Rowan's decision: allow T = −16 (≤ 4 spoiling coordinates: 4 mismatches, two 1-bp indels, one gap ≤ 5, …) so ~250 bp reads at 0.5% error mostly map (reads will be trimmed). Being generalized on `speed/fast-proved`: fast path parameterised by T; two-gap windows go through the proved banded scorer (`BandScore`); ≥ 5 seeds needed at −16 (n ≥ 125 with 25-letter seeds). Builders, IO and the both-strand combine stay trusted.

## Paired proper-pair mode — PROVED (codecs/PairMapper.lean, 2026-10-04)
`mapFastBoth_eq_mapSpecBoth`, `pairFast_eq_pairSpec` against the draft `spec/PairSpec.lean` (fast path 100–103 bp, sc0, T = −12; strands searched one after the other). Proof fanned out: skeleton with 4 sorry lemmas, one subagent each. `lake exe pair_bench` (proved `pairFast`), chr21.pe100k, this box: 1 thread 35.6k pairs/s (71k reads/s), 4 threads 130k pairs/s; byte-identical to `bench/pair_ref.py` (88,794 kept). minibwa paired: ~20–26k pairs/s 1 thread, ~84k at 4. Prototype with joint strand search: ~105k pairs/s 1 thread. Joint search PROVED (codecs/PairJoint.lean: `mapFastJ_eq_mapSpecBoth`, `pairFastJ_eq_pairSpec`; strands = virtual chromosomes sharing one Best; fanned out to 2 subagents): `PAIR_JOINT=1 lake exe pair_bench` 55k pairs/s 1 thread, 178k at 4, identical to brute reference. Strand order proved (`mapChromsJ rf`: any order is exact; `pairFastJ` searches mate 2's opposite strand first): 76k pairs/s 1 thread, 237k at 4, still identical (88,794 kept). General fast mapper MERGED (2b06a0e, codecs/FastGen.lean `mapFastT_eq_mapSpec`: any read length, any T = −P, only GenomeBytes/Encodes/checkAll hypotheses): chr21.r100k T=−12 254k reads/s 1 thread (tuned 100-bp mapFast 359k), answers identical to ptv.tsv. Whole genome TODO: one concatenated index (per-chromosome indexes force ≥1 lookup per chromosome per strand). Smaller minimizer index MERGED (index subagent + speed/index-layout incl. MzCheckPar): `Mz.buildW G k B c sw t` (4/5/6/8-byte slots, stored key cut to fit with genome check of the k-word, mod-minimizer t); PAIR_MZ_C/W/T, FAST_MZ_C/W/T, FAST_CHECK_PAR. chr21 interleaved: 191 MB index 84–89k pairs/s, 77 MB (k22 B23 c0 sw4 t6) 79–82k, outputs identical. chr1 bytes/letter: 3.28 (current) → 1.20 (22/23/0/4/6, ~10% slower) → 0.74 (17/23/0/4/8, ~35% slower). Whole-genome projection: 3.7 GB / 2.3 GB index. The byte genome (3.1 GB) must become 2-bit for < 4 GB total; one global index needs 32-bit positions (5-byte slots). PAIR_MZ=19 failed before because tag+position exceeded 64 bits; B=48 allocated 4·2^48 bytes. Strand interleaving MERGED (92f0fd8, codecs/PairInterleave.lean `pairFastI_eq_pairSpec`, `pairFastI_mz_eq_pairSpec`; PAIR_INTERLEAVE=1): chr21 97–102k pairs/s 1 thread, identical output. Packed scoring for speed DROPPED (subagent profile: scoring ≤26% of map time, exact packed path 1.7× slower than hamSeeds; packed genome still matters for whole-genome memory). Bigger chromosomes (hg38 chr1/chr2 from iGenomes S3, /home/user/data/chr1.1l.fa, chr12.1l.fa, *.pe100k): PAIR_JOINT PAIR_MZ=22 chr1 16.8k pairs/s RSS 1.74 GB index 818 MB; chr1+2 6.1k pairs/s RSS 3.2 GB — slowdown being diagnosed; concatenated single index in progress. Target (Rowan): whole genome < 4 GB RSS, 2–3× minibwa. Rowan's fallback design: proper-pair/unique filter mode = proved fast path only; unfiltered mode additionally runs a slower fallback function (closer to minibwa speed) for reads that don't map well. Minimizer index for pairs PROVED (`pairFastJ_mz_eq_pairSpec`, `PAIR_JOINT=1 PAIR_MZ=22 pair_bench`): chr21.pe100k 1 thread 62k pairs/s, RSS 0.51 GB (index 191 MB) vs hashed 69k pairs/s, RSS 1.85 GB (index 406 MB); identical output. k=19 fails the index checker (B=24). Packed genome (pool/mapper/MapperPacked.lean, proved: `hamPacked_eq`, `packGenome_ok`, `allAcgt_iff`, `cnt64_eq`): 2 bits/letter, 32 letters/word, XOR + SWAR count; `lake exe packed_bench` 100-letter counts 180–193 ns vs 811–881 ns byte loop (random), 60–69 ns vs 724–811 ns cached; memory-bound at random positions. NOT yet wired into the mapper, and the comparison is against a plain byte loop, not the mapper's current Hamming kernel. Tried and dropped: batched lookups across reads (proto-tune 8652baf, PROTO_GROUP=G, pure reordering): no gain at 1 thread, worse at 4 (pairs 103k/284k → 77–91k/185–213k); not proved, not merged. Remaining gap to the prototype (~105k): per-lookup interleaving of the two strands (prototype alternates lookups; proved version finishes one strand first).

## Several chromosomes: one concatenated index — PROVED (codecs/PairConcat.lean, 2026-10-04)
Diagnosis (`PAIR_DIAG=1 pair_bench`, Mz k=22, per mapped read): chr21 3.09 lookups / 2.4 anchors / 1.1 gap-stage anchors; chr1 3.09 / 13.8 / 9.2 (82% of anchors from the 0.8% of lookups returning > 64; gap stage 29% of map time vs 11% on chr21); chr1+chr2 with per-chromosome indexes 8.69 / 125 / 130: a read's wrong chromosome has no best yet, so both strands look up all 4 seeds there, huge repeat buckets included. `pairFastC` (`pairFastC_hashed_eq_pairSpec`, `pairFastC_mz_eq_pairSpec`): one index over the concatenation (checked by `catOk` + the index checker), each seed looked up once, anchors sliced per chromosome by binary search, every chromosome takes one proved `lzStepA` step; global seed order and stop. Windows are scored on the chromosomes' own bytes (a separator-padded single chromosome is NOT exact: a window 1–3 letters into the separator can score ≥ −12). `PAIR_CONCAT=1 PAIR_INTERLEAVE=1 [PAIR_MZ=22]`, 1 thread, shared box: chr1+chr2 31.2k pairs/s (RSS 3.6 GB) vs 6.3k; chr1 40.9k vs 37–40k; chr21 identical to the reference dump. Early stop after two penalty-0 hits would save ≤ 2% of anchors; incremental gap passes ≤ 8% of gap work — not done.
## Packed genome — PROVED (branch `speed/packed-genome`, 2026-10-04)
- `pool/mapper/MapperPGen.lean`: `PGen` = 64-letter blocks of 17 bytes (flag byte: 1 = block inside the genome and all ACGT; then 2-bit codes A0 C1 G2 T3), so a random letter costs one cache line; other bytes from an exact run list `ex` (start, stop, byte; binary search, slow path only). 17/64 = 0.266 B/letter. Builder `PB` (streaming, untrusted; `pack G` uses it). `Rep P G` (same size, `P.get i = G.get! i` for all i); runtime check `checkPG_ok`; `tailOk` = no flag 1 past the end.
- Design: copies of the genome-reading code with `G.get!`/`G.size` → `PGen.get`/`PGen.n` (hamming, fwdMis, bwdMis, eqRun, the gapped/same-length steps, lzStep, ilLoop, mapChromI(s), pairFastI, Mz okAt…mzLook), each proved equal to the byte version under `Rep` (induction, mechanical). Existing files untouched (merges cleanly).
- `codecs/PairPacked.lean`: `pairFastIP_eq` (RepAll → `pairFastIP = pairFastI`), `pairFastIP_eq_pairSpec`, `pairFastIP_mz_eq_pairSpec` (byte genome present: `checkAllPG`, `checkAllMz`), `pairFastIP_mzP_eq_pairSpec` (no byte genome: `GenomeBytes (pgs.map Mz.unpack) g`, `checkAllMzP` = `tailOk` + Mz checker on the PGen; `unpack` is never run).
- `codecs/MzPacked.lean`: `check2P_eq` (Mz checker over PGen = `check2` under Rep), `buildWP` (builder over PGen, untrusted).
- `PAIR_PACKED=1 PAIR_INTERLEAVE=1 PAIR_MZ=… pair_bench`: FASTA packed while read (no byte genome ever), index built and checked on the PGen. Prints peak/current RSS (VmHWM/VmRSS).
- Measured (this box, 1 thread, 100k pairs, Mz k22 B23 c0 sw4 t6; box noise ±10%): chr21 bytes 72–74k pairs/s, RSS 224 MB; packed 62–66k, RSS 147 MB (peak 181 during index build). chr1 bytes 26.4–27.8k, RSS 627 MB; packed 24.2k, RSS 452 MB; packed k17 B23 c0 sw4 t8 (index 183 MB vs 300 MB) 16.6k, RSS 343 MB. Dumps byte-identical to the byte mapper (chr21 88,743 kept, chr1 91,725). Index build+check on the PGen: ~30 s chr21.
- Whole-genome projection (×12.45 from chr1): packed genome 0.82 GB; index k22 3.7 GB → ~4.6 GB; index k17 2.3 GB → ~3.1 GB, plus reads/batches. Per-chromosome B=23 offsets (32 MB each) are counted; a concatenated index changes that.
- Runtime pitfall (Lean 4.33 bundled mimalloc): freed blocks > ~64 MB are never reused or returned to the OS (shown with plain `mi_malloc`/`mi_free`; 60 MB blocks are reused). Freeing chromosome-size ByteArrays therefore does not lower RSS, which is why packed mode never builds them. Same trap for any builder that copies or frees > 64 MB arrays (e.g. a whole-genome index's offsets when the fill array is shared and copied).
- Concatenated genome (merged 280e148 / pairFastC): `PGen` now has an offset `o` (a window `[o, o+n)` of the blocks; `get` has a bounds test again), `view G o n` shares the arrays. `codecs/PairConcatPacked.lean`: `pairFastCP_eq` (= `pairFastC` under Rep), `pairFastCP_mz_eq_pairSpec` (hypotheses: `cutOk G offs ns`, `Mz.check2P ix G`, `GenomeBytes ((cutAll G offs ns).map Mz.unpack) g`). The genome is held once, packed; the index is built (`buildWP`) and checked on it. `PAIR_PACKED=1 PAIR_CONCAT=1 PAIR_INTERLEAVE=1 PAIR_MZ=22 PAIR_MZ_B=23 PAIR_MZ_C=0 PAIR_MZ_W=4 PAIR_MZ_T=6`: chr21+chr22 46.7k pairs/s RSS 244 MB vs bytes 50.2k / 457 MB; chr1+chr2 12.0k pairs/s RSS 782 MB (genome 130 MB, index 577 MB) vs bytes 14.1k / 1,598 MB; dumps identical. kf is only 3 bits at W=4 for 491M letters (many key false positives); the whole genome needs 32-bit places, so W=5 (index ≈ 1.45 B/letter at k22) or smaller k.
- Whole-genome projection with one concatenated index: genome 0.82 GB + index 3.6–4.5 GB (k22, W=4/5) → over 4 GB; k17 W=5 ≈ 2.8 GB + 0.82 → ~3.6 GB. Not measured.
- Not done: word-at-a-time compare (eqRun/hamming over packed words); the packed path costs ~10–15% map time today.

## Packed genome on the general / tier-1 pair mapper (speed/packed-genome, 2026-10-05)
- `pool/mapper/MapperGRead.lean`: `class GRead` (get/size); the genome-reading kernels and stages of the general path (hamming…eqRun, kerG(P), filt16(P), twoGap*, fwd/bwdProf, cellVals/band*, bandScore, FastGenAlgo stages, advC/GS.adv/ilG/mapChromsGB, FastGenShort scans) take `{Gt} [GRead Gt]`; theorems unchanged at ByteArray (one `simp -zeta only [GRead.get_bytes, GRead.size_bytes]` bridge after some unfolds). Byte path speed unchanged (gen_pair_bench chr21+22 T=−12: 23.9k pairs/s before and after). Sent to speed/fast-proved for merge.
- `codecs/FastGenPairPacked.lean` `pairFastGBP_mz_eq_pairSpec`, `codecs/FastGenTierPacked.lean` `pairTier1P_mz_eq` (= pairSpecTier1): PGen views + Mz index bundled with its packed genome (`PkMz`), transfer lemmas `*_same` per generic def. `gen_pair_bench GP_PACKED=1 [GP_TIER1=1] GP_MZ=…`: chr21+22 100k pairs T=−12 same index: bytes 23.9k pairs/s, packed 18.9k, RSS 361 MB, identical dump.
- Whole genome (hg38, 25 seqs, 3.09 G letters): packed genome 820 MB (packing 105 s). pairFastCP 100-bp run, Mz k22 B26 C0 W5 T6: index 4.49 GB, RSS 5.67 GB, 90,081/100k kept, 2.3k pairs/s (shared CPU; slowness not diagnosed). Estimate for the packed general/tier-1 mapper: ≈ 5.7 GB at k22 W5; ≈ 4 GB with a k17 t8 W5 index (≈ 2.9 GB, ~30% slower on chr1). The tier-1 whole-genome 2×150 run was stopped at wrap-up (not measured).
- PGen.get: USize arithmetic in `raw` (packed general mapper −21% vs bytes).

## Short-read word kernels — PROVED (branch `speed/kernels250`, 2026-10-05)
Scope: scoring kernels for reads ≤ 256 letters, each proved equal to the kernel it replaces; the general pair mapper with them swapped in (`pairFastGBK`) is proved equal to `pairFastGB`, hence to `pairSpec` (`pairFastGBK_hashed_eq_pairSpec`, `pairFastGBK_mz_eq_pairSpec`; extra hypothesis `checkPGs pvs gbs = true`: the packed chromosomes spell the byte ones, runtime-checked). Standard axioms only; check.sh passes.
- `pool/mapper/MapperK250.lean`: read packed once per strand (`packRP`: 32 letters per UInt64, plus an all-ACGT/≤256 flag); genome words gathered from the PGen blocks (`gword`, 8 code bytes = 32 letters, aligned word carried along the scan); XOR, field fold, SWAR count (`cnt64`), k-th lowest/highest set field (`selLow` via `cnt64 (m ^^^ (m-1))`, `selHigh` via smear). Scans: `hamA` (= `hamming`), `fwdA`/`fwdK`/`fwdL` (= `fwdMis`), `bwdA`/`bwdK`/`bwdL` (= `bwdMis`); the `…L` versions scan 8 letters with bytes first and check the PGen block flags only when that does not decide (random diagonals stop there). `gappedPen3` = `gappedPen2` plus a third level (F3/E3), exact up to cap 17 (`gappedPen3_spec`); `kerG3` (`kerG3_eq`: `min fB (lim+1)` for `lim ≤ 17`, `= kerG` for `lim ≤ 15`); word kernel `kerGK = kerG3` (`kerGK_eq`, only `Rep P G`).
- Proof files: `MapperK250Bits` (digits of fold/masks/xor/comb/gword), `MapperK250Sel` (selection), `MapperK250Chunk` (`packRP_ok`, `chunk_dig`), `MapperK250Loops` (word loops = byte loops), `MapperK250Spec`, `MapperK250Words`, `MapperK250Seed` (`seedHashK_eq`: seed hashes from the packed words via field reversal `revF`).
- `codecs/FastGenK250.lean`: `ker16K = ker16` (`ker16K_eq`): penalty 16 in closed form — `kerGK` at cap 16 is exact for one gap (`min fB 17`), so the banded kernel only runs for two-gap candidates (`twoGapC`, the necessary part of `filt16`; lengths n, n±2). `kerHK = kerH`. `revCompK = revCompB` (table, 4.5× faster: `complB`'s branches mispredict). Search copied with the kernel as a parameter (`ilGF`, `chromKBF`, `mapChromsGBF` …; with `kerH` they are the originals, `rfl`/induction), prepared seeds passed in (`prepGK_eq`), shape lists memoized (`shapesM_eq`, `shapesNZ_eq`).
- Microbench `lake exe k250_bench <chr.fa> <mate.reads.txt> <truth.tsv> [1|2]` (chr21, 20k reads, 0.5% error, ns/window, bytes → words, all results asserted equal). 2×250 mate 1: penalty 16 (`ker16`→`ker16K`): true same-length 1098→462, random same-length 656→551, true one-gap shapes 5743→589, random shapes 154→92. Cap 15 (`kerG`→`kerGK`): true same-length 754→339, random same-length 241→230, true shapes 150→99, random shapes 45→55. Cap 12: 824→371, 271→253, 103→73, 37→39. One hot 250-letter window: `hamming` 825 ns → `hamA` 228 ns. Per read: `revCompB` 2.8 µs → `revCompK` 0.6 µs; `packRP` 0.7 µs.
- End to end `lake exe k250_bench pair <chr.fa> <m1> <m2>` (`K_T=P`, `K_OLD=1` also runs `pairFastGB` and asserts identical output), chr21, 100k simulated pairs, hashed index, 1 thread (box noise ±10%):

| | `pairFastGB` | `pairFastGBK` | × |
|---|---|---|---|
| 2×250, T = −16 | 20.4k pairs/s | 39.1k | 1.92 |
| 2×250, T = −12 | 37.1k | 47.3k | 1.27 |
| 2×150, T = −16 | 14.5k | 20.1k | 1.38 |
| 2×150, T = −12 | 56.8k | 68.6k | 1.21 |

- Profile now (2×250, T = −16, gdb sampling; perf is not available): kernels ~20%, `ordG`'s bucket sizes (`ps.map (LookG.size ix)`, cache misses) ~10%, lookups ~10%, read packing ~9%, rest search/allocation. Tried and dropped: per-diagonal mismatch tables shared by all shapes of a diagonal (no gain at 2×150 T = −16: the cost there is the number of (diagonal, shape) pairs when phase 1 finds nothing ≤ 15, not the scans).
- Hooks for the search code (`speed/fast-proved`, not edited here): (1) take the window kernel as a parameter (`Ker := c → st → len → cap → pen`), then `kerHK` swaps in by `funext kerHK_eq`; (2) memoize `shapesAt` (~12% at 2×250 T = −16); (3) `revCompK`, `seedHashK`/`prepGK` for per-read prep; (4) stage K at T = −16 scores ~60 shapes on every anchor diagonal when phase 1 found nothing ≤ 15 (2×150: ~60% of map time) — fewer diagonals or best-first diagonal order would help more than faster kernels.
- Not done: deriving the reverse strand's packed words from the forward ones (saves one packing pass, ~5%); a whole-PGen (no byte genome) variant — the kernels already read the genome through the PGen; only fallbacks/lookups use bytes.

## Chromosome scaling (branch `speed/chrom-scaling`, 2026-10-05)
All in `codecs/PairSched.lean`, PROVED, standard axioms:
- `mapFastS_eq_mapSpecBoth`, `pairFastS_eq_pairSpec`, `pairFastS_mz_eq_pairSpec`: **one lookup scheduler over all chromosomes and both strands.** Slot `i < 2n` = (chromosome, strand), tag = `i`, own `LzS` state, one shared `Best`; each step looks up the next seed of the live slot with the smallest `key slot k size`. Any key is exact (the proof only uses `adv_ok`/`dead_cover`/`SOk.mono` from MapperInterleave); slots still live after the 8n-step loop are drained (never in practice). Seed routing (Rowan's idea 1) is this with key = bucket size: the globally rarest seeds are looked up first, so the best is found before huge buckets elsewhere are touched.
- `pairFastX_eq_pairSpec`, `pairFastX_mz_eq_pairSpec`: **exact early exits** on top (`schedLoopX` with a `stop` predicate; `amb0_final`, `target_final`, `decode_partner`): (a) a best that is ambiguous at penalty 0 stays so → read unmapped, stop; (b) mate 2: once the partner slot (mate 1's chromosome, other strand) is finished, the pair can only be kept if the current best is already a unique proper partner → otherwise stop, pair not kept. Mate 2 of non-kept pairs was 2.5% of mates but 21% of mate-2 time (chr1+2).
- `pair_bench`: `PAIR_MODES=I,S1,S2,X` (several mappers on one index; dumps `<dump>.<mode>`), `PAIR_STATS` (lookups/anchors per read), `PAIR_PROF` (time per read class). S1 key (k, size), S2 key (size, k), X = S2 keys + early exits; mate 2 searches the partner slot first. `bench/sched_scale.sh <dir> "1 2 3 4"`. Data: hg38 chr1..4 from iGenomes S3, g<n>.fa = chr1..n, 100k pairs each (`SIM_PAIRED=1`).

1 thread, this box (4 cores, 15 GB), Mz k=22 B=24, 100k pairs, index build excluded; dumps byte-identical (cmp) for I, S1, S2, X at every size. Run-to-run noise ≈ ±10% (S2 on chr1: 33.9k one run, 39.0k another).
| chromosomes | letters | index bytes | RSS | I (pairFastI) | S1 | S2 | X | lookups/read (S2) | anchors/read (S2) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 249 M | 818 M | 1.75 GB | 39.4k | 33.8k | 39.0k | 38.1k | 3.23 | 13.5 |
| 2 | 491 M | 1.67 G | 3.23 GB | 5.9k | 22.6k | 23.0k | 23.7k | 6.56 | 19.9 |
| 3 | 689 M | 2.37 G | 4.51 GB | 3.3k | 13.1k | 14.7k | 16.5k | 9.92 | 29.0 |
| 4 | 879 M | 3.07 G | 5.74 GB | 2.5k | 10.5k | 11.9k | 12.6k | 13.3 | 32.3 |
(pairs/s). Repeat on 4 chromosomes, one process alternating S2/X/S2/X/S2/X: S2 11.2k/11.5k/11.2k, X 11.5k/12.1k/12.0k → early exits ≈ +5% at 1 thread. 4 threads, 4 chromosomes (single run, order I, S2, X): I 8.1k, S2 28.0k, X 43.1k pairs/s, RSS 5.75 GB, identical; the S2→X gap there is larger than at 1 thread and was not repeated. The scheduler turns the 6–16× collapse into ≈ 3× from 1 to 4 chromosomes; S2 ≥ S1 from 2 chromosomes on.

Where the remaining drop comes from (`PAIR_PROF`, mate 1, S2):
- Normal reads (≤ 64 anchors, 97%): 12.5 µs/read at 2 chromosomes, 24.3 µs at 4 → ≈ 6 µs per added chromosome per read. Every slot needs ≥ 1 lookup (a tying window can hide in any chromosome) plus 4 bucket probes to order its seeds: lookups grow ≈ 3.1 per chromosome per read. **The concatenated single index subsumes this term** (8 probes per read whatever the genome size); extrapolated, per-chromosome indexes cost ≈ 140 µs/read at 24 chromosomes from this term alone.
- Repeat reads (> 64 anchors, 2–3% of reads): 43–46% of time at 2–4 chromosomes; those ending at penalty ≥ 12 cost ≈ 2 ms each (≈ 680 ns/anchor vs 145 ns at penalty < 4: the gap stage walks all anchors after lookup 3 and again after lookup 4). This term is the same with a concatenated index (its bucket is the union), so the early exits (X) carry over.
- Tried and dropped (unproved bench experiment `advF`, mode F, identical output): skip the gap stage after lookup 3 when the best is still ≥ 12 and do lookup 4 at once — slower (10.2k vs 12.5k pairs/s, 4 chromosomes): lookup 4 is the largest bucket and the lookup-3 gap pass often settles the slot.

## Tier-1 / short-read workhorse (branch `speed/fast-proved`, 2026-10-05)
Done (all proved, check.sh green on 58b0faf):
- Main-path speed (body changes, equality lemmas): shapes table (`shapesT_eq`/`shapesKT_eq`; the mergeSort was 1/3 of stage K), reverse complement by table (`complTab_get`), `sbound` table (`sbound_def`), best window not re-scored (`addK`, `inv_skipP`). chr21 1 task, 250 bp both strands: T=−16 35k → ~51k reads/s, T=−12 60k → ~90k.
- Merged speed/packed-genome (GRead), claude/upbeat-goldberg-kizkfd (word kernels), speed/pair-unique, speed/chrom-scaling. `PGen.raw` USize path guarded by `i < USize.size` (`raw_eq`); FastGenK250 copies aligned (addKF skip, shape tables); `RepAll` in FastGenK250 → `RepAllK`.
- `codecs/FastGenTierK.lean` `pairTier1K_{hashed,mz}_eq` = `pairSpecTier1` (+ `checkPGs`): word kernels at cap 16, bytes at cap 12. chr21 tier-1 pairs: 2×250 22–30k → 34–38k pairs/s; 2×100 76k. `gen_pair_bench GP_TIER1=1 GP_K=1 [GP_KCHECK=k]`.
- Tried and dropped: two-pass stage K (slower), USize seedCode (≈2%).
Event-based pigeonhole — PROVED (9fade4e, 7e0b05c; check.sh green on 7e0b05c):
- `pool/mapper/MapperEvents.lean` `exists_clean_seed_amongE`: with seeds of ≥ 2 letters a walk within `−T` leaves at most `seedBoundE sc T = (−T) / min(M, O, 2E)` seeds unclean (`errRepsL`: a gapY run charged at its start and per seed boundary crossed; `errRepsL_clean`, `errRepsL_length_le`, `cost_boundE`). `codecs/FastGenCoverE.lean` `coverLE`.
- `sbound x = x / 4` (was max(x/4, (x−6)/2)) in fastT, phase-1 stop rule and stage-K/B support filter; `chromKB_coverL` takes `2 ≤ Ls`; short path guard `2·(sbound P + 1) ≤ |R|`. No new search code; theorem statements unchanged.
- Deepest guaranteed cap: 100 bp 13 → 15, 150 bp 17 → 23, 250 bp 25 → 39. Indexed path = short scan on 300 slice reads at T = −16, −24, −39.
- Speed, chr21 2×250, 20k pairs, 1 task (GP_K=1 word kernels; K=0 bytes):

| error | T=−16 | T=−24 | T=−32 | T=−39 |
|---|---|---|---|---|
| 0.5% | 44.7k pairs/s | 4.1k | | |
| 1% | 28.6k (bytes 21.2k) | 1.24k | 238 | 48 |
| 2% | 28.5k | 0.53k | | |

  Above 16 the cost is stage B (banded DP for reads whose best stays above 16).

Fast deep caps — stage B pruning PROVED (de57fb5, 4b7b59b; check.sh green):
- `pool/mapper/MapperBandPrune.lean`: a read block of 25 letters with no exact copy in the band costs ≥ 4 for any window (`block_step`); the banded pass dies once row value + 4·(spoiled blocks still ahead) < −cap (`bandEndP`, `bandEndP_spec` = `bandEnd2_spec`'s guarantee; gap-state threshold +4 instead of +6). Spoiled blocks checked directly per diagonal (`spoiledArr`, `spoiled_ok`).
- Each pass capped at the current best `min best P` (`addBS_spec`/`stageBD_spec` for any cap with cap = P or best ≤ cap); end shifts nearest first.
- chr21 2×250, 20k pairs, 1 task, pairs/s bytes / words (after the container restart; T=−16 runs ~10–20% faster than earlier tables on this box):

| err | T=−16 | T=−24 | T=−32 | T=−39 |
|---|---|---|---|---|
| 0.5% | 32.4k / 45.4k | 7.8k / 8.2k | 3.18k / 3.26k | 627 / 623 |
| 1% | 22.4k / 30.2k | 3.02k / 3.02k | 1.05k / 1.04k | 203 / 202 |
| 2% | 23.7k / 29.2k | 1.63k / 1.69k | 426 / 416 | 76 / 77 |

  Before (1%, words): −24 1.24k, −32 238, −39 48.
- Then (69d22e1) thresholds from a per-diagonal count array (`bandRowsC = bandRowsP`, `prefCnt`), and (efd14c9) the pass on bytes (`pool/mapper/MapperBandBytes.lean`: penalties saturated at P + 1, `bandRowsCB_rel`, `bandPenE_B`). chr21 2×250 1% error, word kernels: T=−24 5.18k, T=−32 1.66k, T=−39 321 pairs/s (from 1.24k / 238 / 48).
- Tried, no measurable gain (not kept): skipping diagonals by support at the current best; ordering diagonals by support.
- Remaining cost at T=−24 (callgrind, stages K+B): band pass ~46%, stage K's ker16 band fallback ~12% (byte-kernel path), spoiled-block checks ~4%, per-pass shape filter ~5%.
- Next: group shapes by end shift once per stage; bit-parallel band pass; kernels exact past 16 for one-gap windows (roadmap).

## Rowan's ranked speedup list — status (2026-10-04)
Done and proved: 1 closed-form scoring; 2 rarest-seed exact shortcut (smallest bucket first + early stop); 3 tighter bound (4 × 25); 5 stored seed rest / context; 7 threads (mark_mt fix); 9 rarest-first + P/4+1 stop + gaps only ≥ 8; 10 non-ACGT (per-letter place lists, N = mismatch). Partly: 4 unboxed (proved code uses ByteArray/fixed-width/tail recursion, but not yet the 2-bit packed genome + popcount → `speed/seed-schemes` proving a packed-Hamming kernel); 6 sampled whole-genome index (minimizer / mod-minimizer proved, whole genome not built). Not done: 8 batch lookups across reads (→ `speed/proto-tune` prototype).

## Specs Rowan plans to write
- **minibwa vs spec vs truth** (`bench/mb_compare.py`, 100k simulated pairs, 0.5% error, minibwa proper-pair flag, MAPQ = min of mates; spec = proved pair dump T = −12): on every pair the spec maps, minibwa (any MAPQ) gives the same placement (chr21 88,794/88,794; chr1 91,723/91,725 — 2 differ; chr1+2 92,615/92,615); 12–20 of those are off-truth for both (simulation errors make another place strictly better). minibwa MAPQ≥20 maps 3.9–4.8k more pairs: ~2.3–2.4k beyond the T = −12 cap (97–98% at truth) and ~1.6–2.3k that the spec leaves unmapped as per-mate ties, nearly all at truth (pairing breaks the tie; pair-level uniqueness would recover them). Placements not at truth, MAPQ≥20: minibwa 85 / 92.7k (chr21), 53 / 96.5k (chr1), 67 / 97.1k (chr1+2); spec 20 / 88.8k, 13 / 91.7k, 14 / 92.6k (all shared with minibwa, not spec errors).
- **Real data:** GIAB HG002 (NA24385) NIST HiSeq 2500 2×250 bp, ~350 bp insert, PCR-free, public bucket https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads/ (D1_S1_L001_R{1,2}_00N.fastq.gz). First 1M pairs of _004 at /home/user/data/hg002/hg002_1M_R{1,2}.fq (not in repo): all 250 bp, 0.1% of reads contain N, some read through into adapter (AGATCGGAAGAGC…) → needs trimming. Needs the whole-genome index (memory: 2-bit genome) and the general-path pair mapper (250 bp) before our mapper can run on it. Note: minibwa's off-truth pairs at MAPQ≥20 include ones where the spec's (and truth's) placement differs — errors ours avoids.
- **Pair-level uniqueness** (pairSpecU: unique best proper pair by combined score) in progress on speed/pair-unique (cloud session_01YFFXp83fFC8jhHkxUW7jA8): fast case = current answer, exact all-hits fallback for ties / non-proper bests.
- **Speed metric now (Rowan):** end-to-end wall clock vs minibwa on the same adapter-cut FASTQ (cutadapt is a separate pre-step): read → proved trim → pair/prep → proved map → write, same threads, index load excluded for both. Any optimization allowed as long as the mapping result stays proved = spec and check.sh is green at the end of the day.
- **Short-read workhorse (Rowan):** reads ≤ 250 bp, T down to −16, must be as fast as possible; may assume length ≤ 250 and use proved byte/word/bit tricks. Long reads (500 bp–1 Mb) get a separate function later. Owners: speed/fast-proved (search: FastGenAlgo/FastGenPair, pairFastGB) and speed/kernels250 (cloud session_01KKoMYeXpn7VUHTPQEwdsEp: bit-parallel kernels proved equal to existing ones). Real HG002 reads after adapter cut + Q20-style trim: median ~248–249 bp, 10th percentile 204–232, <1% under 100 bp. Packed genome merged (c8c0dbd): pairFastCP_mz_eq_pairSpec; chr21 small Mz index 64k pairs/s vs 100k hashed/bytes on this box; chr1+2 (cloud box) 12.0k/782 MB packed vs 14.1k/1,598 MB bytes. Whole genome needs 5-byte Mz slots (W=5); k17 W5 ≈ 3.6 GB total projected. mimalloc pitfall: freed blocks > ~64 MB are never reused — don't free/copy large arrays in builders.
- **Short mates (Rowan):** dispatch kernels by length with a length-dependent cap: n ≥ 150 → T = −16 (sbound 16 = 5 → 6 seeds of 25); 100 ≤ n < 150 → T = −12; **n < 100 skipped for now — TODO: add them back later** (planned: proved batched genome scan with shorter seeds, option A; the 25-mer pigeonhole needs n ≥ 25·(sbound P + 1)). The raw-spec fallback in mapFastGB must never run on real genomes (it used 10 GB on chr1+2).
- **Reads < 30 bp are always excluded** (Rowan: acceptable spec hypothesis/rule). Batched exact short-read path (5–149 bp) exists on speed/fast-proved aeca30f (mapChunkGS_eq, pairChunkGS_*_eq) as an opt-in later tier.
- **Agent budget (Rowan):** keep about 5 Opus agents running in total; don't restart agents that finish. Everything gets merged into claude/upbeat-goldberg-kizkfd.
- **Trim→map pipeline MERGED** (bench/TrimMap.lean `trim_map`; codecs/ReadTrim.lean trimRead_eq_contract + trimRead_acgt (Q−20 score, non-ACGT −1e6, kept window ACGT-only); codecs/PairDispatch.lean pairDispatch_{hashed,mz} = pairSpecT (per-mate cap: ≥150 bp T=−16, 100–149 T=−12; <100 'too short'); ParMap.chunks_text ordered output). 1 thread: pipeline = mapping alone; 4 threads within ~5% (chunk 1024) except cheap 2×100 (~30% slower: prep competes). HG002 200k cut pairs vs chr1+2 (dispatch, after startup): ours 968 pairs/s 1 thr / 2.67k 4 thr; minibwa 774–830 / 2.25–2.48k. Agreement at MAPQ≥20: 27,764 same, 1 different; minibwa-only 15,134 beyond cap/soft-clipped, 432 ambiguous/non-proper under spec. chr12.pe250 sim (50k, dispatch): ours 45,509 mapped, 45,497 at truth, minibwa same placement on all of ours; minibwa MAPQ≥20 49,333. Startup: saved-index load 20–30 s + index check ~185 s (largest fixed cost). Off-target reads (84% here) make T=−16 the worst case.
- **Word kernels MERGED** (speed/kernels250 166114f; codecs/FastGenK250.lean pairFastGBK_{hashed,mz}_eq_pairSpec, extra hyp checkPGs): chr21 2×250 1 thread: T=−16 36.4k pairs/s vs pairFastGB 21.6k (1.69×), T=−12 50.8k vs 33.4k (1.52×). Not yet in trim_map / dispatch.
- **Deeper guarantees (queued on speed/fast-proved for tonight):** event-based pigeonhole (each mismatch or whole gap run spoils ≤ 1 seed, every event costs ≥ 4 → ≤ ⌊P/4⌋ spoiled seeds) instead of sbound = max(P/4,(P−6)/2): deepest guaranteed cap 100 bp −13 → −15, 150 bp −17 → −23, 250 bp −25 → −39 (≈ 3.6% mismatches). Goal: proof change only (stage B already scores every shape); stop and report if new search code is needed.
- **Optional clean-up tier idea (Rowan):** near-any-quality matches via a second, full-text index (FM-index: 2-bit BWT ~0.8 GB + occurrence counts ~0.2 GB + 1/16-sampled suffix array ~0.8 GB ≈ 2 GB whole genome) allowing short seeds (e.g. 12–16 letters → 15–20 seeds per 250 bp read, pigeonhole up to ~14+ errors). Total ≈ 5.7 GB (packed genome + minimizer index) + ~2 GB ≈ 7.7 GB, under the 8 GB limit. Proof concern: an FM-index can't cheaply be runtime-checked like the minimizer index — needs a proved builder (slow, ~1 h) or a checker over sampled positions.
- **Index trust plan (Rowan):** build every index (minimizer today, FM-index later) with a PROVED builder; at load time just check that the loaded index's hash equals the hash of the proved builder's output (replaces the slow runtime checker, ~15–20 min whole genome).
- **Pending (as of 2026-10-05 ~02:15 UTC):** local branch tmp-m has speed/pair-unique + speed/chrom-scaling merged but unverified (needs check.sh with free memory); still to merge: speed/packed-genome a8eeff5 and speed/fast-proved ≥ 7159d20 (+ word-kernel adoption). Whole-genome run (local agent): index at /home/user/data/wg/hg38.* (1.45 B/letter, built 1173 s, peak 7.7 GB); mapping + minibwa whole-genome pending.
- **Architecture idea (Rowan, note):** separate the two halves and optimize each on its own: (1) genome/index access — k-mer/minimizer lookups, index layout, memory; (2) local mapping — seed scoring, kernels, stage K, strands. One single interface for index access (the existing `Look`/`LookG` class is the natural boundary). Once both are individually optimized, co-optimize: whichever side is not the bottleneck (e.g. the index is faster than the mapper needs) gets traded for memory (smaller/slower index) so no point on the speed–memory Pareto frontier is left on the table.
- **Direction (Rowan, 2026-10-04):** eventually faster than minibwa AND map almost every read. Hard limit 8 GB RSS whole genome; goal 2×+ minibwa speed with less memory than minibwa (minibwa ≈ 2.6 B/letter RSS on chr1+2 → ~8 GB whole genome). Tiers as options: (1) close maps — current exact guarantee (T = −12/−16); (2) most likely — every read that isn't a multimapper, via iterative deepening (P = 12, 16, 24, …: answer = mapSpec at the smallest P with any hit; exact at each level by mapFastT_eq_mapSpec, cost only for stragglers); (3) everything — optional, proved but slow (slow proved path for stragglers; mostly ignored). DEFAULT (what most users run, must be fastest): proper pair + uniquely mapping + within the total error cap = tier 1. Mate rescue: not for the default; only as a speed aid for tier 3. Tier 3 should offer several user-chosen "slow options" (deeper caps / broader searches) so users can deepen as far as they like. Pair-level uniqueness (best proper pair by combined penalty) vs current per-mate uniqueness is Rowan's spec decision. Splitting seeding and scoring into separate thread stages is likely little gain (already parallel by read batch, memory-bound).
- **TODO Rowan: set up read trimming** — reads will always be trimmed (trimmer/ReadWindowTrimmer), so mapped reads are ACGT-only; then every genome N is a mismatch under the current spec (spec counts N=N as a match; hg38 is 5.33% N in 944 runs, no other non-ACGT) and fast paths may require ACGT-only reads.
- **TODO Rowan: redo `spec/PairSpec.lean`** — current file is a draft written by Claude so the paired proofs could start (both strands via reverse complement, unique best over placements, proper pair = same chromosome, opposite strands, facing, fragment in [lo, hi]). Proofs on `speed/fast-proved` target this draft for now.
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

### Whole genome (merged from speed/whole-genome, codecs/MzView.lean)
- `Mz.buildWV_eq` (view-based builder = in-memory `buildW`), `check3V_eq`, `pairFastGB_view_eq_pairSpec`. The genome is held once as a view of the chromosomes. `lake exe whole_genome`.
- hg38, 24 chromosomes (3.09 G letters), k22 B26 c0 W5 t6: 843.6M entries, 1.45 B/letter; build 1173 s, peak 7.72 GB. Saved at /home/user/data/wg/hg38.*. Index check (check3V, 4 tasks) 979 s.
- hg38.pe250 sim, 100k pairs, T = −16: 1,515 pairs/s at 1 thread, 5,401 at 4; 89,437 kept; RSS 7.6 GB (byte genome 3.07 GB; packing it would give ≈ 5.4 GB). The run then hit an IO error (HG002 step, not diagnosed).
- TODO: switch to the packed genome; whole-genome HG002; minibwa whole-genome index (OOM-killed so far; needs ~9 GB free); why it is ~25× slower per pair than chr21 (lookup hits per seed?).

### Whole genome, pair level (branch `speed/wg-speed`, 2026-10-05)
- **Mate-anchored absence — PROVED** (`codecs/PairRegion.lean`, `pairRegionKP_mz_eq` = `pairSpecT`, per-mate T): map the mate with the cheaper lookups (`seedCost`) over the genome; a proper partner of its hit lies on the same chromosome in `regionB` (fragment bounds + `len_le_of_score`: a hit at T = −P is ≤ `bandOf sc0 (−P)` letters longer than the read, from `sv_lt_thr`). The proved search on that region alone (one-chromosome view, `region_absent` via `mapChromsGB_inv`) ending above P proves the pair is `none` without the second whole-genome search. Most HG002 pairs end here (84% of reads are off-target / unmapped at the cap).
- Bench (`bench/WholeGenome.lean`, unproved IO): genome packed in parallel (block-aligned pieces, whole ACGT blocks at once, next file read ahead; same packed genome, hash equal) and overlapped with the index load: 65 s → 17–20 s. Tasks strided (item i on task i mod n), all `.dedicated`.
- Whole genome, `pmap` mode PR (pairRegionKP + word kernels + packed genome), `WG_NOCHECK` (hash printed and equal to the earlier value; `WG_CHECK=1` check3P does not fit the 2-minute run limit — hg38.hash not written):

| set | tasks | mapping s | pairs/s | kept | peak RSS | dump vs P |
|---|---|---|---|---|---|---|
| HG002 200k (cut) | 4 | 29.0 | 6,831 | 162,106 | 6.39 GB | identical |
| HG002 200k | 2 | 47.5 | 4,177 | 162,106 | 6.47 GB | identical |
| hg38.pe250 sim 100k | 4 | 7.55 | 13,237 | 89,437 | 6.10 GB | identical |
| sim 100k | 2 | 16.0 | 6,246 | 89,437 | 6.10 GB | identical |

  5k HG002 at 4 tasks: PK (both mates whole genome) 2,159–3,480 pairs/s vs PR 4,533–5,450. Target was 17.5 s for HG002 200k at 4 tasks (2× minibwa); not reached.
- Profile: lookups 25–40 µs per mate; the cost is verification (stage K/B) on reads with big buckets; a few pairs dominate (polyA mate with 6 seeds of 291k entries: 1.1 s in PK, 0.24 s in PR). Parallel efficiency at 4 tasks ~60% (tail pairs).
- **Region lookups cut to the region — PROVED** (`mzLookRP`, `RgMz`): places in a bucket increase (`Mz.check`), so the region search binary-searches each bucket to the region start (`lbSlot`, result re-checked at runtime in `startSlot`) and stops at the first place past the region; the region bytes alone are the genome (offset 0). `lookupPPR_eq` (= full scan cut by `cutAnc`), `lookOk_cut` / `lookOk_rg` (exact lookups on the region bytes), `pairRegionKP_mz_eq` still = `pairSpecT`.
- **hg38.hash written** (Rowan's call: check3V passed on these exact files earlier, wk/map.log "index check ... true"); every load verifies it.
- Bench: chunked work queue (`parChunk`, 16 pairs per grab from a shared counter, `WG_CHUNK`, `WG_TASKS=4/16,4/0` = tasks/chunk, 0 = strided); RESULT lines print process CPU time and host steal. Task use 93–97% (strided ~73%).
- After merging claude/upbeat-goldberg-kizkfd (stage-B cap, MapperBandPrune) + region lookups + queue: **HG002 200k, 4 tasks: 16.7 s mapping (11,864 pairs/s, CPU 64.9 s), kept 162,106, dump identical, peak RSS 6.54 GB** (target 17.5 s). Host noise is large: the same build measured 15.8 / 30.6 / 16.7 s; compare runs by CPU time or interleaved in one process (`WG_TASKS=4/0,4/16,...`). 2 tasks: 36.2 s.
- Profile now (50k, PR): region search is negligible; mate A's whole-genome search is ~90%: stage K kernels (gappedPen2Pk fwdMis/bwdMis, gapAll2P eqRun) ~1/3, phase-1 hamming ~12%, seed pre-filter (matchQ) ~7%, lookups (scanAP, lbound) ~8%.
- Clean A/B on a quiet box (one BIG.lock hold, 3× each, interleaved, HG002 200k cut, 4 threads/tasks): mapping ours 17.60 / 16.07 / 15.90 s (median 16.07) vs minibwa (Real − index loaded) 30.76 / 26.59 / 29.67 s (median 29.67) → 1.85×; mapping CPU ours median 62.6 s vs minibwa 112.9 s; peak RSS ours 6.21–6.79 GB vs minibwa 7.61–7.63 GB; kept 162,106 every run.
- **Piece fine filter in stage K — PROVED** (`fineOk` in `kfilt`): besides the 25-letter seeds, the read's `R.size/8` disjoint 8-letter pieces are checked near the diagonal (`pieceNear`, within `2·gapBound`); more than `sbound` failures drop the diagonal. Exact by the same event count (`coverLE` with l = 8): `fineOk_of`, `pieceNear_of`, the third conjunct in `chromKBS_cover`. On the slow 2% of reads 711k of 2.59M diagonals passed the seed filter but only 29k the piece filter. **HG002 200k, 4 tasks: 14.41 s mapping (13,770 pairs/s, CPU 56.4 s), kept 162,106, dump identical, peak RSS 6.05 GB.** 20k: 1.44 s.
- Quiet-box confirm after merging 23f209e: 13.37 / 13.45 / 13.35 s (median 13.37 s, CPU median 52.5 s), dump SAME every run; real 2× target is 14.8 s (29.67 / 2).
- **Seeds prepared once per mate — PROVED** (`prepMate`, `costP`, `mapFastGBKPp`; `mapFastGBKPp_prep` is `rfl`): the mate-order choice and the whole-genome search share the reverse complement, packed words and prepared seeds. Interleaved A/B (one lock hold): old 13.37 / 13.53 / 13.52 s (CPU 52.2 / 53.0 / 53.0) vs new 12.59 / 12.77 / 12.28 s (CPU 49.1 / 49.8 / 48.2): **median 12.59 s, CPU 49.1 s**, dump SAME.
- **Bucket entries checked with one genome word — PROVED** (codecs/MzWord.lean: `okAtW`, `scanAW`, `lookupPW`; PairRegion: `scanAWR`, `lookupPWR`; `okAtW_eq` for every `PGen` via `rep_unpack`): the seed's little-endian code is built once per lookup (`seedLE`); at each entry the 25 genome letters are one word (`gW`), XORed with it, and the three runs `okAtP` compared letter by letter are masked word checks (`eqW`); tag checks kept; non-ACGT seeds or unflagged windows use `okAtP`. No index change (storing the full key needs ~63 bits/slot, +2.5 GB). Profile on looked-up seeds: 75 → 39 µs/read. Interleaved A/B (noisy box): old 14.19 / 13.75 / 14.39 s (CPU 55.7 / 53.9 / 56.2) vs new 14.02 / 12.89 / 13.99 s (CPU 54.9 / 50.6 / 54.8): **median 13.99 vs 14.19 s**, new faster in every pair, dump SAME.
- Diagonals by merging each lookup's sorted list instead of one mergeSort (`diags_eq` proved via `Perm.eq_of_pairwise`): two interleaved A/Bs, new won 2 of 6 pairs (medians 14.63 vs 15.25 s, 14.19 vs 14.85 s). No gain, NOT kept.
- **Phase-1 kernel: word path before the 8-letter byte prefix — PROVED** (`kerGK` / `kerGKG`; `kerGK_eq` re-proved): when the window is flagged and the read packed, `hamA` (stops past `lim / 4`) runs directly; the byte prefix stays only on the byte path. Two interleaved A/Bs: old 15.22 / 14.60 / 13.18, 14.28 / 13.49 / 15.90 s vs new 13.63 / 12.86 / 15.05, 13.65 / 14.26 / 14.32 s; new won 4 of 6 pairs, **6-run median 13.96 vs 14.44 s**, dump SAME.
- 125–149 bp mates at T=−16 (dispatch only): 3 interleaved pairs, 12.19 → 16.32 s median (+34%), kept 162,106 → 162,230. NOT kept.
- Cap sweep for ≥150 bp mates (penOf = min T proved cap; HG002 200k cut, 4 tasks, one run each): full set T16 12.3 s, kept 162,106; T20 / T24 time out at 120 s. 20k pairs: T16 1.26 s, kept 16,274; T20 26.5 s, 16,614; T24 47.9 s, 16,840. 5k pairs: T16 0.38 s, 4,084; T28 21.3 s, 4,270; T32 60.4 s, 4,288. RSS 6.0–6.6 GB throughout. Each step past −16 is ~20–60× slower for +1–2% kept: the banded stage-B path dominates.
- **Trimmer neutral quality is a parameter — PROVED** (`trimReadQ Q`, `perBase Q v = v − Q`; `trimRead_eq_contract` / `trimRead_acgt` for every `Q ≤ 93`; `sum_le` bound `(93 − Q)·n`; `trimRead = trimReadQ defQ`, `defQ = 20`; bench env `WG_TRIMQ`). HG002 200k cut, 4 tasks, interleaved: Q20 kept 162,106, median of 4 runs 12.07 s (CPU ~47 s); Q23 kept 166,979, 12.69 / 13.36 s; Q25 kept 167,760 (+3.5%), median of 4 runs 12.54 s (+3.9%, CPU ~49 s). Q25 keeps more but is ~4% slower, so the default stays Q20 pending Rowan.
- Deep-cap profile (bench profRead, `WG_PROF=0:0` on a T=−20 / −24 build; first 3000 / 1500 HG002 pairs): stage B (banded) is ~96% of K/B time (T20: 20.9 s, stage K alone 0.87 s). It is reached by 8% of reads, mostly unmapped at P (411/492 at T20), in repeats (~4.7k anchors, 11–13 lookups): ~1,450 stage-B diagonals per read, of which only 0.35% (T20) / 0.9% (T24) pass the stage-K seed filter `kfilt` at Q = min P best. Prototype (`chromKBPf`, bench only, unproved): stage-B diagonals through `kfilt` at P: T20 5.1 vs 20.9 s, T24 3.7 vs 23.6 s. Same results at T20; at T24 13 of 2976 reads lose a tying second hit (24 ambiguous → unique), so kfilt as is is NOT sound above 16 / for ties.
- Packed genome loaded from `hg38.pgw` / `.pgx` (identical to the FASTA packing) plus `hg38.pgc` (n, o, chromosome cuts) with `WG_PKLOAD=1`; trusted via the same index hash (covers G.w, G.ex, n, o, cuts); `WG_PKSAVE=1` writes them after a hash-verified run. Load 6.6 vs 9.6 s, RSS after load 5.24 vs 5.91 GB, run peak 5.81 vs 6.00 GB; mapping dump SAME.
- Saved packed genome is now the pmap default (`WG_FASTA=1`, a missing `.pgc`, `WG_CHECK` or `WG_PACKONLY` pack the FASTA instead, so a written hash always comes from the FASTA).
- Word stage-B filter prototype (bench `kfiltW`: `unlookW` + multi-word 8-letter pieces), same subsets: T20 2.95 s vs byte kfilt 4.33 s vs stage B today 18.4 s; T24 3.34 / 3.69 / 22.0 s; same results as byte kfilt. Superseded by the proved stage-B kfilt (d410057), not pursued.
- After d410057 (stage B behind kfilt at lim = P; PR path uses it through `chromKBFG` in both the whole-genome and region searches): HG002 20k subset (Q20 trim) T16 1.23 s / T20 4.14 s / T24 8.59 s, kept 16,274 / 16,614 / 16,840 (unchanged); full 200k cut, Q25: T16 12.12 s, kept 167,760; T20 29.18 s (2.4×), 169,531; T24 68.13 s (5.6×), 170,449; RSS 5.8 GB.
- vs minibwa (Q25, T=−16, PR, 4 tasks, saved packed genome; interleaved, one lock hold): ours 12.47 / 11.84 / 11.89 s (median 11.89, CPU ~46 s, RSS 5.74–5.80 GB); minibwa mapping (real − index load) 24.29 / 23.72 / 23.50 s (median 23.72, CPU ~100 s, RSS 7.63 GB): **2.0×** (2.28× against the earlier 27.10 s median).
- **Overlap with minibwa** (bench/mb_overlap.py; denominator D = minibwa's non-multimapping proper pairs: primary, flag 0x2, both mapped, both MAPQ > 0 = 188,963 in mb_hg200k_cut_t4.sam). Q25, T=−16 PR dump (wgout/q25/PR_hg002.tsv): kept 167,760 = 88.78% of D; **same place (both mates' windows overlap minibwa's spans, same strand) 167,699 = 88.75% of D**; ours elsewhere 9 (8 with a better worse-mate penalty than minibwa's re-scored placement, 1 equal, none worse); ours mapped outside D 52 (43 minibwa not proper, 9 MAPQ 0). D pairs we do not report: mate < 100 bp after Q25 trimming 7,285 (3.86%), beyond cap 16/12 but within the proved cap 4,757 (2.52%), beyond the proved cap 5,766 (3.05%), within cap (tie / insert / other) 3,447 (1.82%). Penalties re-scored for our Q25-trimmed mates at minibwa's position. With both MAPQ ≥ 20 (D = 185,217): kept 90.57%, **same place 167,662 = 90.52%**; elsewhere 5 (4 better, 1 equal); mate < 100 bp 6,843 (3.69%), beyond cap within proved cap 4,209 (2.27%), beyond proved cap 4,374 (2.36%), within cap 2,124 (1.15%).

### Pass router, unmapped reasons, short mates (branch `speed/tiers`, 2026-10-05)
- **Unmapped reasons — PROVED** (codecs/PairReason.lean): `Reason` = trimmedAway / tooShort / noHit m / tie m / noPartner m / notProper, each with a spec-level meaning (`ReasonOk`: `hitsBoth = []`; hits but `mapSpecBoth = none`; other mate unique and no hit of m is a proper partner; both unique, not proper). `reasonOk_none`: a reason ⇒ `pairSpecT = none`. `mapSpecBoth_mono`: a read with a hit at T has the same answer at every deeper cap, so tie / notProper are final for deeper caps (`reasonOk_tie_mono`, `reasonOk_notProper_mono`); only noHit / noPartner / tooShort can change.
- **Pass router — PROVED** (codecs/PairRouter.lean): pass 1 = today's caps; pass 2 (option, default off) only on pairs whose reason passes `goOn` (default noHit, noPartner, tooShort; hook for ties / notProper later) at deeper per-length caps. noPartner reuses the known mate's pass-1 answer (`mapSpecBoth_mono`) and runs only the other mate's region (+ genome) search; noHit runs the no-hit mate as the region mate. `routeKP_ok`: each pair is `Settled` at the caps of the pass that settled it (mapped = `pairSpecT` there, reason = `ReasonOk` there, tooShort = `fastT` false there); output carries the pass and caps. The any-hit flag (`pen_le_iff`: best pen ≤ P ⇔ `hitsBoth ≠ []`) separates noHit from tie for free.
- **Pluggable pass kernel**: `PassKer` (prep, cost, whole-genome mate search with any-hit flag, region test) and its obligation `KerOk`; `routeG_ok` holds for any pass-1 / pass-2 kernels meeting `KerOk`. Today's kernel = `kpKer` (`kpKer_ok`). A faster proved deep-cap search (speed/fast-proved kfilt for stage B) plugs in as pass 2's kernel by proving `KerOk`.
- Bench: mode `RT` (router), `WG_PASS2=1`, `WG_T2=minLen:cap,…` (default `150:20`), `WG_SHORT=1`, `WG_REASONS=1` (tally of pass:reason), `WG_TRIMOUT=prefix` (write trimmed mates once as `>r`/sequence text; empty line = trimmed away).
- HG002 200k cut, Q25, 4 tasks, RT pass 1 = PR: dump identical (20k), kept 167,760. Reasons left: noHit 5,971 / 4,737, noPartner 1,498 / 2,269, tie 4,669 / 4,162, notProper 210, tooShort 2,385 / 6,304.
- **Pass 2, T2 = −20 for ≥150 bp mates** (20k pairs; the 200k residual does not fit the 2-min limit with today's stage-B kernel): pass 1 1.49 s, kept 16,814 → with pass 2 11.72 s, kept 16,987 (+173, +1.0%). ~1.4k residual pairs searched, ~29 ms CPU each (deep-cap stage B). Extrapolated to 200k: +~1.7k kept for +~100 s. Worth it only with a faster pass-2 kernel.
- **Short mates 50–99 bp** (cap 7 for 50–74, 11 for 75–99 bp; `fastT`: sbound(P) < len/25): HG002 200k, pass 1: kept 167,760 → 170,282 (+2,522, +1.5%), CPU 49.3 → 59.3 s (+20%), mapping wall 17.0 → 20.7 s (noisy box). tooShort left: 641 / 3,055 (mates < 50 bp).
- How B's uniqueness is proved in `pairRegionKP`: B's region search on a miss proves no proper partner (`regionNoHitKP_sound`); on a region hit B still needs the full whole-genome search (selectUnique over all hits), so a short B costs a whole genome search. Cheaper exact option (not implemented): when the region finds B's best at penalty p ≤ cap, `mapSpecBoth_mono` gives B's answer at the cap = answer at −p, so the whole-genome search can run at cap p (often 0–2: larger exact seeds, fast path from shorter reads).
- `pairSpecU` (pair-level uniqueness), not implemented: it can only rescue tie pairs, upper bound tie1 + tie2 = 8,831 pairs (5.3% of kept) at Q25 pass 1 (9,565 with short mates).
- **B-cap trick — PROVED** (`mateH`, `mateH_ok`; `PassKer.hint`, bench `WG_HINT=0` turns it off): after a region hit, mate B goes over the genome first at the cap of its best region hit (`regionPenKP`), and at the full cap only when that search finds no hit. Exact for any hint: a hit within cap h gives the answer at the full cap (`mapSpecBoth_mono`, `hitsBoth_ne_mono`). 20k: dumps identical on/off; CPU 5.87 → 5.27 s (short off), 6.28 → 6.11 s (short on). 200k short on: CPU 63.7 → ~57 s.
- Pass-1 mate order option `RouteCfg.ord1` (bench `WG_ORD=cost|short|long`; any order exact, `passLenG_ok`). 200k short on: cost 15.2 s / CPU 59 s, short mate first 26.5 s / CPU 101 s, long mate first CPU 61.5 s: keep `cost`. Bench `WG_CAP1=minLen:cap,…` overrides the pass-1 caps. Packed genome loaded with `WG_PKLOAD=1`.
- After merging the proved stage-B kfilt (d410057), pass 2 on 20k: T2=−20 11.7 → 6.2 s.
- **vs minibwa, one BIG.lock hold, 3 interleaved rounds** (HG002 200k cut, Q25, 4 tasks, saved packed genome; box shared with Lean builds, noisy). minibwa mapping (real − index load) 35.6 / 25.6 / 27.8 s, **median 27.8 s**, CPU ~106–119 s (whole run), peak RSS 7.6 GB. Denominators from mb_hg200k_cut_t4.sam: proper pairs, both mapped, primary, both MAPQ > 0: **D0 = 188,963**; both MAPQ ≥ 20: **D20 = 185,217**. "Same place" = both mates on minibwa's chromosome with overlapping reference intervals.

  | setting | mapping s (3 runs) | median | ×minibwa | CPU s | RSS GB | kept | % D0 / D20 | same place % D0 / D20 | not mb-proper |
  |---|---|---|---|---|---|---|---|---|---|
  | A short off (16/12, <100 too short) | 15.23 / 10.92 / 12.17 | 12.17 | 2.28 | 42–48 | 5.5 | 167,760 | 88.78 / 90.57 | 88.75 / 90.52 | 43 |
  | B short on (75–99 @11, 50–74 @7) | 19.74 / 14.74 / 15.03 | 15.03 | 1.85 | 56–59 | 5.5 | 170,282 | 90.11 / 91.94 | 90.07 / 91.87 | 47 |
  | C 75–99 @11 only | 13.29 / 13.59 / 13.96 | 13.59 | 2.04 | 52–54 | 5.5 | 169,243 | 89.56 / 91.38 | 89.53 / 91.32 | 44 |
  | B + pass 2, T2=−20 (≥150 bp) | 39.50 (1 run) | | 0.70 | 155 | 5.5 | 172,082 | 91.07 / 92.91 | 91.02 / 92.84 | 49 |
  | B + pass 2, T2=−24 (≥150 bp) | 49.37 (1 run) | | 0.56 | 190 | 5.5 | 172,799 | 91.45 / 93.30 | 91.40 / 93.22 | 52 |

  Full short mates miss 2× (1.85×): the default is unchanged. 75–99 bp only is on the line (2.04× median, 1.88× in one round). The extra cost is mostly proofs of absence for the newly searched pairs (noHit +985, noPartner +736, tie +734).
- **New default (Rowan, 2026-10-05): 75–99 bp mates at cap 11** (`WG_SHORT=75`; `50`/`1` adds 50–74 @7 opt-in, `0` off; pass 2 stays opt-in, cap 28 later). Commit 36b65d6, check.sh green (63 files, 405 theorems). Session 2 (quiet, one BIG.lock hold, 3 interleaved rounds): ours 13.74 / 13.35 / 13.31 s, **median 13.35 s**, CPU 51.5–53.4 s, RSS 5.5 GB; minibwa 28.34 / 29.94 / 25.06 s, **median 28.34 s**, CPU 103–109 s, RSS 7.6 GB → **2.12×**. Kept 169,243 = 89.56% D0 / 91.38% D20; same place 89.53 / 91.32%; 44 not minibwa-proper (identical dump to C).
- **Where absence proofs spend time** (20k, pass 2 at −20, short on, 1 thread, `WG_PPROF`): pass 2 total ~9.6 s; noHit→noHit pairs (673) ~7.05 s (74%): the genome-wide "no hit ≤ 20" proof costs ~10 ms/read vs ~1.6 ms at −16. noPartner→mapped is mostly the hinted B search (~1.3 s). Dead reads at −20, per read: lookups + phase 1 1.44 ms, stages K/B 11.0 ms; 271/300 reach stage B; 543k stage-B diagonals, 9.9k pass kfilt. Very skewed: the top reads take 1175 ms and 741 ms; they are repeat-heavy (buckets up to 281,474, 200k anchors), and at P=20 for 150–174 bp sbound ≈ m−1, so a single seed hit makes a candidate. Reusing pass-1 lookups can save at most ~1.4 of ~12 ms/read.
- **Pass-2 budget gate, 20k** (pass 2 at −20; pass 1 alone keeps 16,942; pass-2 time on 1 thread): no gate 17,116 / 6.36 s; both mates' costP ≤ 1000: 17,078 / 0.40 s; ≤ 3000: 17,092 / 0.58 s; ≤ 10000: 17,102 / 1.64 s; cheaper mate ≤ 1000 (`WG_P2GATE=min`): 17,106 / 1.37 s; ≤ 3000: 17,111 / 1.85 s. Slow pass-2 pairs (cost > 1000; 592 pairs, 6.0 s) end as: noHit 226 pairs 3.9 s (65%), mapped 40 / 1.38 s (hinted B search), tie 25 / ~0.6 s (10%), noPartner 145 / 0.15 s. A tie-tightened cap could save at most ~10% here.
- **Three benchmarks, one BIG.lock hold, 3 interleaved rounds** (2026-10-05; mapping = real − index load; G1 = pass 2 at −20 with gate both ≤ 3000; G2 = cheaper ≤ 1000, 1 run). The default is ≥2× minibwa on none of them:
  | set | minibwa median (CPU, RSS) | default median (CPU) | × | G1 median | kept default / G1 / G2 | % D0 / D20 default | same place default | not mb-proper |
  |---|---|---|---|---|---|---|---|---|
  | HiSeq 2x250 (D0 188,963, D20 185,217) | 25.31 s (105–115 s, 7.6 GB) | 13.87 s (51–54 s) | 1.82 | 15.93 s (1.59×) | 169,243 / 170,821 / 170,958 | 89.56 / 91.38 | 89.53 / 91.32 | 44 |
  | NovaSeq 2x151 cut (D0 187,008, D20 182,695) | 13.44 s (56–67 s, 7.3 GB) | 15.03 s (56–58 s) | 0.89 | 16.18 s (0.83×) | 165,140 / 165,946 / 166,141 | 88.31 / 90.39 | 88.30 / 90.37 | 2 |
  | mason 2x150 (D0 194,603, D20 193,068) | 14.41 s (54–60 s, 7.4 GB) | 18.21 s (67–71 s) | 0.79 | 20.35 s (0.71×) | 180,904 / 183,672 / 183,990 | 92.96 / 93.70 | 92.96 / 93.69 | 0 |
  Our RSS 5.5 GB everywhere. On 150 bp mates minibwa needs half its HiSeq CPU; ours does not drop (6 seeds, sbound(16) close to m − 1).
- **Pair-level anchor join — PROVED, not worth it** (`codecs/PairJoin.lean`: `noPairJ`, `noPairJ_ok`; reason `noPair`; `PassKer.noPair` pre-check; `kpKerB_ok`, `routeKPB_ok`; bench `WG_JOIN1` / `WG_JOIN2`). All anchors of all seeds of both mates, merge join of facing strands within `hi + n1 + n2 + 2·gapBound` per mate: no meeting anchors → no proper pair of hits → pair none. 20k: kept unchanged (exact), but it settles 137 of 1,973 pass-2 pairs (0.01 s of their pass-2 time), only 3 of 592 slow pairs; the join costs 7.4 s (full buckets of repeat seeds), pass 2 6.4 → 10.3 s; in pass 1 1.7 → 36.4 s. Repeat mates' anchors meet within the fragment window almost always. Off by default.
- **Pass-2 cost order** (`RouteCfg.swap2`, bench `WG_P2ORD=cost`, default): for noHit pairs, search the cheaper mate first (exact for either order): pass 2 on 20k 9.69 → 6.05 s (−38%). `RouteCfg.gate2` (bench `WG_P2BUDGET=N`): only pairs with estimated cost ≤ N go to pass 2; the rest keep their pass-1 settlement (exact for any gate, `routeG_ok`).
- **Plan for later (Rowan, not now): multi-pass router.** Several passes, each a kernel optimized for an error band (x ≤ pen ≤ y); each runs only on the previous pass's noHit residual, may pass information forward (e.g. the band already ruled out), and a final mop-up pass ends the chain. The router proof composes them (`routeG_ok` generalizes to a list of `KerOk` kernels). Watch each pass's startup cost against how fast the pool shrinks.
- Note: a few whole runs spent ~80 s of wall outside the timed phases (box load / exit); the 20k measurement avoids the 150 s guard.

### Pair-level uniqueness: modes U, H, HN (branch `speed/tiers`, 2026-10-05)
- **Mode U — PROVED** (`pairUKPF_mz_eq`, `pairUKPRF_tie`, codecs/PairLadder.lean, PairLadderF.lean): `pairSpecUT` (best proper pair over all hits, sl = 0, dcost0) by a cap ladder; `ladderUF` builds the proper pairs once per rung, grouped by (chromosome, strand) (`properPairsF_eq`), and replaces the quadratic `bestPairD` with `bestOfPairs` (`bestOfPairs_pp`). On NovaSeq 2k this cut pairing from 27.4 s to 0.39 s. The Lean ladder now takes 0.42–0.65× the C model's time on both-repeat pairs.
- **Mode H — PROVED** (`pairUKH_mz_eq`, `pairUKH_tie`, codecs/PairHybrid.lean): mode PR first. PR's pair is kept when it is proper under `properPairU` and its distance cost is 0 (`fastU_ok`); otherwise the pair goes to the ladder. H = U, also checked on all 57,538 20k pairs.
- **Mode HN — PROVED** (`pairUKHN_eq` = mode H, `pairUKHN_mz_eq`, `pairUKHN_tie`, codecs/PairNear.lean). At each rung the ladder searches the second mate only on diagonals near the first mate's hits (`keepN`, `hitsAtKPN`: hitsC with a diagonal predicate). The generic lemma is `ladderUB_eq`: B's list may be any sublist of its hits that holds every hit with a proper partner in A's list (`NearOk`, `hitsKPFN_near`). B's seed lookups are still genome-wide; only kfiltV and the kernels are restricted.
- 20k pairs, 4 tasks, one run per set (noisy box). HN = H on every pair.
  | set | PR wall / CPU | H wall / CPU | HN wall / CPU | kept PR / H | H pairTie |
  |---|---|---|---|---|---|
  | NovaSeq | 2.07 / 3.4 s | 9.22 / 24.2 s | 7.97 / 20.0 s | 16,451 / 16,958 | 634 |
  | mason | 2.50 / 5.0 s | 7.67 / 19.9 s | 5.72 / 16.9 s | 17,413 / 17,859 | 495 |
  | HiSeq | 1.33 / 3.8 s | 5.32 / 15.6 s | 4.68 / 13.6 s | 16,814 / 17,120 | 567 |
- NovaSeq, 1 thread, time by class:

  | class | H | HN |
  |---|---|---|
  | 0 (no repeat mate) | 1.0 s | 1.0 s |
  | 1 (one repeat mate) | 6.4 s | 3.2 s |
  | 2 (both repeat) | 16.1 s | 14.4 s |

  Both-repeat pairs are now 77% of the time; next: shared lookups across rungs.

### Budget experiment: give up on expensive pairs (bench only, unproved, not the default; 2026-10-05)
- Input for Rowan's spec rewrite.
  - Bench mode `RTB<N>` = the default router (RT) behind a gate. The pair is reported unmapped (reason gaveUp) when either mate's lookup work after the rarest-seed choice, `costP` at the pass-1 cap (anchors), exceeds N.
  - Every reported pair is still RT's answer (`pairSpecT`): every dump is a subset of N = ∞'s, and mason has 0 wrong placements at every N. Only recall drops.
  - `WG_BUDT=N,…` tallies, per N, the pairs given up by what RT gave them. `PRB<N>` / `HB<N>`: the same gate in front of modes PR / H.
  - The gate preps each mate a second time; this overhead is within noise.
- 20k pairs per set, 4 tasks, one run each. Kept lost against N = ∞ (as % of ∞'s kept):

  | N | mason | NovaSeq | HiSeq |
  |---|---|---|---|
  | 5k | 1,309 (7.25%) | 1,282 (7.76%) | 503 (2.97%) |
  | 20k | 429 (2.38%) | 491 (2.97%) | 142 (0.84%) |
  | 30k | 247 (1.37%) | 298 (1.80%) | 112 (0.66%) |
  | 40k | 142 (0.79%) | 178 (1.08%) | 81 (0.48%) |
  | 50k | 84 (0.47%) | 101 (0.61%) | 54 (0.32%) |
  | 60k | 48 (0.27%) | 61 (0.37%) | 37 (0.22%) |
  | 70k | 29 (0.16%) | 42 (0.25%) | 29 (0.17%) |
  | 100k | 21 (0.12%) | 29 (0.18%) | 23 (0.14%) |
  | 200k | 13 (0.07%) | 28 (0.17%) | 19 (0.11%) |

- Smallest budget per recall limit on every set: 1% → **50k**; 0.5% → **60k**; 0.25% → **70k**.
- At N = 60k:
  - Pairs given up: mason 58 (0.29% of all pairs), NovaSeq 170 (0.85%), HiSeq 109 (0.55%).
  - What RT gave the lost pairs (mapped / tie / other): mason 48 / 7 / 3, NovaSeq 61 / 9 / 100, HiSeq 37 / 5 / 67.
  - Same place, as % of minibwa D0 / D20 (first 20k pairs), ∞ → 60k: mason 92.65 / 93.41 → 92.40 / 93.17; NovaSeq 88.16 / 90.34 → 87.83 / 90.00; HiSeq 89.64 / 91.49 → 89.45 / 91.29.
  - mason: all 48 lost pairs were correct placements; 0 wrong at any N.
- CPU, ∞ → N (noisy, 4 tasks):

  | set | ∞ | 60k | 20k | 5k |
  |---|---|---|---|---|
  | mason | 5.2–5.3 s | 4.9 s | 3.5 s | 2.1 s |
  | NovaSeq | 3.1–3.8 s | 3.1 s | 2.3 s | 1.5 s |
  | HiSeq | 3.8–4.1 s | 3.0 s | 2.9 s | 2.1 s |

  Within ≤ 0.5% recall the budget buys little. The big savings need N ≤ 20k, which loses 1–3% (7–8% at 5k).
- **200k vs minibwa at N = 60k** (session 5: one BIG.lock hold, 3 interleaved rounds of minibwa / default RT (N = ∞) / RTB60000, 4 tasks; mapping = real − index load).
  - D_hi round 1 hit the 130 s guard while loading the genome, so HiSeq D is the median of 2. Its dump is session 4's (same kept count, 169,243).

  | set | minibwa (median of 3) | RT, N = ∞ | ×mb | RTB60000 | ×mb | CPU ∞ → 60k |
  |---|---|---|---|---|---|---|
  | HiSeq | 34.36 / 22.32 / 23.77 → **23.77 s** | 9.89 / 10.48 → **10.18 s** | 2.33 | 8.48 / 8.47 / 8.50 → **8.48 s** | **2.80** | 39–41 → 33 s |
  | NovaSeq | 12.36 / 11.78 / 11.90 → **11.90 s** | 11.32 / 10.56 / 11.33 → **11.32 s** | 1.05 | 8.34 / 8.54 / 8.50 → **8.50 s** | **1.40** | 41–44 → 33 s |
  | mason | 11.23 / 11.32 / 11.32 → **11.32 s** | 13.78 / 13.62 / 13.92 → **13.78 s** | 0.82 | 13.05 / 13.62 / 13.15 → **13.15 s** | **0.86** | 53–54 → 51–53 s |

  minibwa CPU 94–102 s (HiSeq), 52–54 s (NovaSeq and mason); RSS 7.3–7.6 GB vs ours 5.5 GB.
- Recall at 200k, ∞ → 60k:

  | set | kept | lost (% of ∞'s kept) | same place % D0 / D20 |
  |---|---|---|---|
  | HiSeq | 169,243 → 168,831 | 412 (0.24%) | 89.53 / 91.32 → 89.31 / 91.10 |
  | NovaSeq | 165,140 → 164,427 | 713 (0.43%) | 88.30 / 90.37 → 87.92 / 89.98 |
  | mason | 180,904 → 180,369 | 535 (0.30%) | 92.96 / 93.69 → 92.69 / 93.41 |

  Every budget dump is a subset of ∞'s. mason: 0 wrong placements, and all 535 lost pairs were correct placements.
- Reading: the budget takes HiSeq from 2.3× to 2.8× and NovaSeq from 1.05× to 1.4×, but barely moves mason (0.82× → 0.86×). mason's time is not in the repeat mates; it is spread over ordinary pairs (150 bp at cap 16, sbound close to m − 1). A budget alone does not reach 2× on 150 bp mates.
- **Where mason's time goes** (bench `WG_MPROF=N`, profile only).
  - Setup: 20k mason pairs, RT, 1 thread. RT total 4.44 s = 222 µs per pair.
  - Buckets use the larger of the two mates' penalties in our answer; mason has 0 wrong placements, so this is the true penalty.
  - Parts come from a re-run of each step. Lookups are timed alone; phase 1 is shown without them. Stage B never runs at caps ≤ 16. "other" = RT total − sum of parts (router, decoding, a second search after a failed hint).
  - Trimming is outside the timed path: the inputs are pre-trimmed.

  | bucket | pairs | time | RT µs/pair | prep | order | lookups | phase 1 | stage K | region | other | seeds/pair |
  |---|---|---|---|---|---|---|---|---|---|---|---|
  | 0 | 1,303 | 0.06 s | 43 | 5.1 | 2.5 | 4.6 | 5.1 | 7.6 | 5.4 | 13 | 4.0 |
  | 1–4 | 5,661 | 0.40 s | 71 | 5.1 | 2.6 | 9.9 | 9.8 | 10.9 | 6.2 | 26 | 6.8 |
  | 5–8 | 6,304 | 0.89 s | 141 | 5.3 | 2.6 | 25.6 | 20.2 | 40.1 | 8.3 | 39 | 9.6 |
  | 9–12 | 3,607 | 1.29 s | 358 | 5.5 | 2.7 | 71.5 | 50.6 | 144.0 | 11.6 | 72 | 12.2 |
  | 13–16 | 1,180 | 0.75 s | 639 | 5.5 | 2.9 | 126.2 | 114.6 | 272.1 | 18.6 | 100 | 14.4 |
  | unmapped | 1,817 | 1.14 s | 628 | 5.5 | 2.9 | 84.2 | 95.0 | 350.0 | 4.7 | 85 | 6.7 |

  - The 0–4 buckets are 35% of pairs and 10% of the time, at 43–71 µs per pair. minibwa's average is about 225 µs CPU per pair, so these pairs are already 3–5× cheaper than minibwa's average.
  - 70% of the time goes to pairs at penalty ≥ 9 or unmapped (33% of pairs), mostly stage K and lookups. mason is not a low-error set: 66% of pairs are at penalty ≥ 5.
  - A near-exact pair pays a fixed 43 µs:
    - prep 5 µs, order 2.5 µs, lookups 4.6 µs, phase 1 5 µs, stage K 7.6 µs, region 5.4 µs, other 13 µs.
    - A "found an exact/1-mismatch hit, prove uniqueness cheaply" path could at most skip order, region and part of stage K / phase 1: about 15–20 µs per pair.
    - The cap-16 uniqueness proof still needs its seeds.
    - On mason that is ≤ 0.1 s of 4.4 s (1 thread); the near-exact path is not where the gap is.
- Mode H with the same gate (mason 20k): HB1000 kept 15,428, HB2000 15,793, vs PRB1000 15,224 and PRB2000 15,572; PR 17,413 and H 17,859 at ∞. Mode H places 8 of its 17,859 mason pairs wrongly; PR and RT place 0 wrongly.

### Tiered certificate check (mode RTX; bench only, no new proofs; branch `speed/tiers`, 2026-10-06)
Every pair gets a tier with what was proved about it (`bench/WholeGenome.lean`, `WG_MODES=RTX`; dump `WG_TIEROUT=1`, profile `WG_XPROF=N`).
- Tiers:
  - T1: RT mapped (unique proper pair, proved).
  - T1g: pair-level guarantee found the unique proper pair with combined penalty ≤ G.
  - T1gm: a second qualifying pair within G was found (a proved multimapping tie; skipped, not reported).
  - T1t / T1d: tie / discordant (ladder only).
  - T2: over the cap, with an upper bound p from a re-scored CIGAR (`checkRuns`).
  - T3: given up. Suffix x = the pigeonhole does not apply (a mate under 25 bp, tooShort).
- Gate: RTB (`gaveUpR` N on `costP(cap1F)`) skips RT for expensive pairs; those go straight to the guarantee.
- **Pair-level guarantee G ∈ {0, 4}** (`pairGX`; proper pairs as in pairSpecUT, dcost 0):
  - Total ≤ 4 means one mate is perfect, and a gap costs ≥ 8, so all hits are gapless.
  - Candidates by pigeonhole on the 25-letter seeds:
    - 0 mismatches: intersection of the 2 rarest buckets;
    - 1 mismatch: union of the pairwise intersections of the 3 rarest.
  - Buckets are read with `rawLook` (no genome reads; a sound superset), then each candidate is verified on the genome.
  - The mate with fewer candidates (summed sizes of its smallest buckets, free) is enumerated. The partner is checked by a letter scan of its `regionB` window (≤ 1 kb) with the remaining mismatches.
  - Stops at the second qualifying pair. There is no limit L.
- **Grid4** (20k pairs per set, 4 tasks, wall / CPU in s; cap 16, the expensive T2 DP / region search off). "lean" = guarantee only (`WG_XPERF=0 WG_XFREE=0`). Others add mate-level perfect hits and free bounds.

  | config | mason | NovaSeq | HG002 |
  |---|---|---|---|
  | RT | 1.367 / 5.19 | 0.881 / 3.45 | 1.059 / 4.12 |
  | RTB60000 | 1.244 / 4.83 | 0.786 / 3.11 | 0.858 / 3.35 |
  | G0, N 5k | 0.886 / 3.47 | 1.148 / 4.33 | 1.226 / 4.76 |
  | G0, N 20k | 1.271 / 4.97 | 1.351 / 5.16 | 1.412 / 5.48 |
  | G4, N 5k | 0.973 / 3.80 | 1.367 / 5.21 | 1.366 / 5.23 |
  | G4, N 20k | 1.273 / 5.00 | 1.488 / 5.75 | 1.516 / 5.89 |
  | **G4, N 5k lean** | **0.744 / 2.89** | **0.620 / 2.38** | **0.722 / 2.81** |
  | G4, N 20k lean | 1.244 / 4.83 | 0.887 / 3.43 | 0.909 / 3.55 |
  | G0, N 20k lean | 1.021 / 3.98 | 0.702 / 2.69 | 0.853 / 3.30 |
  | G4, N 20k + ladder | 1.78 | 2.25 | 2.15 |
  | minibwa (mapping only) | ~1.18 | ~1.24 | ~2.32 |

- **Speed target (wall within 5% of RT on every set).**
  - Met by the lean configs, which are faster than RT on all three sets.
  - Missed by the full configs on NovaSeq and HG002.
  - Where the time goes (NovaSeq G4 N 5k, 1 thread): gate + RT 1.17 s, guarantee 0.86 s, mate-level perfect hits 1.60 s, free bounds 0.83 s. The guarantee itself is not the problem.
- **Guarantee cost** (1 thread):
  - CPU: G0 mason 0.08–0.10 s, NovaSeq 0.27–0.33, HG002 0.16–0.18; G4 0.53–0.59 / 0.79–0.89 / 0.52–0.61.
  - Candidates checked per pair: p50 0–1; p99 9–176 (G0), ~770–1056 (G4); max 775–62,975 (G0), 4198–10,094 (G4).
  - Worst pair, G4 NovaSeq: 63–79 ms, mates 150 / 93 bp, 3790 candidates checked, none ≤ G.
  - Worst pair, G0 NovaSeq: 19–22 ms, mates 49 / 54 bp (two seeds each, large buckets), 62,963 candidates.
  - Blow-ups, G4 NovaSeq: 26–30 pairs over 5 ms take 0.36–0.43 s, about 45% of the guarantee time.
- **Checks**:
  - Lost-at-≤G against the RT dump: **0 lost in every config**. RT pairs with total ≤ G: G0 mason 1303, NovaSeq 10,683, HG002 9132; G4 4717 / 13,981 / 12,756.
  - Every such pair is T1 / T1g at RT's placement, or T1gm.
  - mason wrong placements: **T1 0 in every config**; T1g 2 at G4, 0 at G0. T1gm (skipped) pairs that are off the truth: 18 at G0, 95 at G4.
  - Pairs where the guarantee does not apply (x; short mates): G0 NovaSeq 135, HG002 201, mason 0; G4 328 / 354 / 0.
- **Tier %**:

  | config | set | T1 | T1g | T1gm | T1t | T1d | T2 | T3 |
  |---|---|---|---|---|---|---|---|---|
  | G4 N 5k lean | mason | 83.73 | 2.94 | 0.76 | – | – | – | 12.58 |
  | G4 N 5k lean | NovaSeq | 76.20 | 6.48 | 2.52 | – | – | – | 14.80 |
  | G4 N 5k lean | HG002 | 82.22 | 2.61 | 1.82 | – | – | – | 13.35 |
  | G4 N 20k + ladder | mason | 89.64 | 1.68 | 0.76 | 3.57 | 0.07 | 4.12 | 0.18 |
  | G4 N 20k + ladder | NovaSeq | 80.71 | 3.26 | 2.52 | 2.40 | 0.70 | 6.99 | 3.43 |
  | G4 N 20k + ladder | HG002 | 84.56 | 1.42 | 1.82 | 2.52 | 0.28 | 6.90 | 2.51 |

  - Lean T3 mates carry only the pair-level bound (> G). There are 4264 mason, 4242 NovaSeq and 3778 HG002 such mates at N 5k.
  - Mates under 25 bp after trimming are tooShort with no bound possible: NovaSeq 137, HG002 204.
- **minibwa** (first 20k pairs, both mates aligned):

  | set | MAPQ ≥ 20 | MAPQ ≥ 1 | all |
  |---|---|---|---|
  | mason | 96.64% (wrong 1) | 97.44% (wrong 19) | 100% (wrong 369) |
  | NovaSeq | 91.78% | 94.77% | 98.95% |
  | HG002 | 92.84% | 95.72% | 99.50% |

- **Earlier designs, dropped for speed**:
  - Per-mate cap ladder (0, 4, 8, 12, 16 under a `costP` budget) plus T2 DP / region DP: 1.5–7× RT. Over the cap grid {8, 12, 16} × N {20k, 60k, ∞} it was 1.5–6.7× RT; cap 8 was slower on mason (15 s CPU against 5.4).
  - The guaranteed cap-0 rung read the genome for each bucket slot (`okAt`, ~200 ns per slot): 158 ms on satellite reads. This led to `rawLook` and the pair-level design.
- **Free upper bounds** (BK 500, top 16 diagonals):
  - hamW (gapless) = p for ~76% of over mates.
  - 4·(n − U) and the chain bound (4·uncovered + Σ(6 + 2|Δ|)) are loose: median excess ~330.
  - 0 re-score failures.
  - Cost: 2.1% of RT on mason, ~15% on NovaSeq (over the 3% target).

### Roadmap: fast deep caps (T = −17 … −39), intermediate exact stages before the banded step
Event-based pigeonhole proves the fast path exact to 15/23/39 (100/150/250 bp), but above 16 reads fall through to stage B (banded DP): chr21 2×250 1% error, T=−24 1.24k pairs/s, T=−39 48 (vs 28.6k at −16). Candidate exact speed-ups, each to be proved equal to the spec:
- Hamming tier: word XOR + popcount over the packed genome at every seed-hit diagonal gives an upper bound U for the read; DP only for candidates whose lower bound ≤ U.
- Lower bounds from seeds: a candidate window with k spoiled seeds costs ≥ 4k (same event argument); skip windows whose bound > T or > current best (unique mode: > second best).
- Word kernels past 16: extend ker16 / stage K (one gap, shared mismatch profiles) to gap length ≤ (T−6)/2 (16 shifts at −39), then two-gap kernels; only reads that fail these reach the banded step.
- Bit-parallel banded DP (Myers / Hyyrö-style bit vectors, affine variant): band ≤ 64 fits one word per column.
- WFA (gap-affine wavefront, Rowan 2026-10-05): cost O(n·s), bounded by the score; with cap ≤ 39 only a few narrow wavefronts per survivor, match runs extended by packed XOR + ctz. Good for survivors with a few indels off the main diagonal. Proof: cap-bounded WFA minimum = banded DP minimum within min(P, best).
- Iterative deepening per read: −16, then −24, then −39, only on reads not settled; ambiguity early exit (two hits ≤ T tie → unmapped in default unique mode).
- Batch the slow reads (stragglers) so their genome windows are fetched together.
- 125–149 bp mates at T=−16 instead of −12: Rowan approved (2026-10-05) if still fast; A/B in progress on speed/wg-speed.

### TODO (Rowan, 2026-10-05)
- Repeat-masked genome as a separate comparison: hg38 here is unmasked (all uppercase). Map HG002 against a repeat-masked hg38 (RepeatMasker/soft-mask → hard-mask) and compare kept %, speed and MAPQ-0 ties against the unmasked run. Check whether genotyping pipelines normally use masked references (GATK-style WGS uses the unmasked analysis set, with masking/filters applied downstream; verify).
- Deeper errors: 7.5% of HG002 pairs exceed the new proved caps. Options: (a) run proved caps up to the pigeonhole limit (cost measured by the cap sweep); (b) a second tier (deepening) only for unmapped pairs; (c) past the pigeonhole limit, a new filter proof (shorter seeds / q-gram counting lemma); (d) 47% of these pairs (6,989 of 14,981) have a soft-clipped mate in minibwa: a spec with end clipping (local or clip penalty) would keep them without deeper caps; this is a spec change for Rowan.
- Bigger/denser index: up to 7.6 GB RSS allowed; measure what it saves on lookups (~32% of time).
- Benchmarks (Rowan): every speed change must be ≥ 2× minibwa mapping time (index load excluded; it amortizes) on all three, same session: real HG002 HiSeq 2×250 200k (cut); real HG002 NovaSeq 2×151 PCR-free 200k (/home/user/data/novaseq, pairs 1,000,001–1,200,000 of gs://brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002…, the minibwa paper's data); mason 2.0.9 GRCh38 2×150 200k with the paper's flags (--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5; /home/user/data/mason/bin, bioconda build). Cross-checks: mason-like and low-variant sim sets (/home/user/data/sim).
- **Spec decision (Rowan, 2026-10-05):** proper-pair mode = pair-level uniqueness (`pairSpecU`, `bestPair` over both mates' hits, per-mate caps; B searched only near A's hits); it becomes the default once proved and fast (tiers agent). Per-mate uniqueness (`pairSpecT`) is kept for an "all mappings" mode (each mate mapped on its own, not only proper pairs).
- **Pair distance (Rowan, 2026-10-05):** the fragment cap is a mode parameter: 1 kb in short-read mode for now (2 kb measured as an option, 5 kb later) and 1 Mb in general. Long reads are single-end, so it does not apply to them. `bestPair` ranks by pen1 + pen2 only: by default closest is not best. **Distance cost (off, kept as an option):** `pairSpecUT` takes a `dcost` parameter (monotone, ≥ 0, added to the pair sum), with default `fun _ => 0`. The variant we tried was 0 up to 1 kb, then +1 per extra kb. At hi 2000 it changed nothing. At hi 5000 it gave 13 wrong mason placements vs 7 without it, per 20k. To restore it, pass that function as `dcost`. The branch-and-bound pruning still holds because dcost ≥ 0. Rowan may add it back as an option later. Per-mate caps apply to the mate penalties only. No dovetail: f.start ≤ r.start + s and f.end ≤ r.end + s, with slack s = 0 by default. s = 5, to allow for trimming, is measured as an option. The current `properPair` checks only f.start ≤ r.end and lo ≤ frag (lo = 100).
- **Spec rewrite pending (Rowan, 2026-10-05):** Rowan will reorganize the spec and acceptance criteria, and may restart from scratch if we are still far off. Options under consideration: port minibwa's algorithm to Lean, prove properties around it, then speed it up; relax the spec to "one of the best" placements together with the MAPQ spec. Until then the default stays PR (pairSpecT), with the goal of near-minibwa speed on low-error pairs on all three benchmarks. pairSpecU modes U/H/HN are proved but 4–8× PR's CPU (repeat pairs). Budget experiment (sound-only give-up) is running, as input to the rewrite.
- Later roadmap: simulated long reads (ONT) and HiFi (paper: Badread), with new long-read kernels and possibly a new spec.
- Long-term roadmap (with long reads): a full-recall mode that maps (almost) every pair minibwa maps, at about minibwa's speed (need not be faster). Needs MAPQ (own spec), tie/non-proper handling, end clipping or deeper caps.
- Per-mate margin (paused, needs its own spec): define the second best over placements at a non-overlapping locus; under "any different placement" the margin is always ≤ 8, because extending the window by one letter costs at most one 1-letter gap. Bench prototype `WG_MARGIN=k` in bench/WholeGenome.lean writes `<mode>_<set>.margin_k<k>.tsv`. It is unproved and untested, and exact only while stage B does not run (P ≤ 16).

Stage-B seed filter — PROVED (`chromKBS`, `chromKBF`, `chromKBFG`; `chromKBS_cover` extended):
- Each stage-B diagonal goes through `kfilt` at `lim = P` (25-letter seeds looked up and unseen, plus 8-letter pieces, at most `sbound (min P best)` missed), re-evaluated at the best of the moment (`stageKS`). Proof: `hfilt` generalized to any `lim ≥ x` (`hfiltG`), stage B via `stageKS_inv`.
- chr21 2×250 1% sim, 20k pairs, 1 task, GP_K=1, pairs/s before → after (dumps identical): T=−20 4.95k → 5.33k, T=−24 3.22k → 3.78k, T=−32 1.04k → 1.91k.
- Real HG002 2×250 (first 20k ACGT-only pairs of D1_S1_L001_R{1,2}_004, not trimmed) vs chr21 (mostly off-target): T=−16 52.2k → 57.2k, T=−20 9.18k → 31.0k, T=−24 3.66k → 17.4k, T=−32 367 → 3.70k (dumps identical).

### Denser-index / seed-scheme prototype for 135–175 bp mates (bench-only, 2026-10-05)
- Tool: scratch C (`seeds.c`), exact L-mer occurrences over all of hg38 (one stream, 444 s, 1.8 GB), 2,500 pairs each of NovaSeq and mason (q25-trimmed), both strands. Candidate = diagonal whose ±band (band = (4e−6)/2) holds ≥ thr distinct seeds; thr from pigeonhole. Slow mate = > 1000 current anchors (NovaSeq 789/5000, mason 741/5000).
- Means per slow mate at e = 4 (P = 16; NovaSeq / mason): anchors, candidate diagonals, loci (clusters).
  - L25 disjoint ×6, thr 2 (current): 33.6k / 29.5k anchors; 9.9k / 5.1k cand; 5.95k / 4.46k loci.
  - L22 disjoint ×6, thr 2: 63k / 54k; 12.5k / 4.6k; 4.9k / 3.5k.
  - L20 disjoint ×7, thr 3: 109k / 89k; 15.4k / 3.9k; 4.4k / 2.7k.
  - L25 step 13 ×10, thr 10−2e (works on the current index): 56k / 47k; 12.3k / 6.6k; 6.8k / 5.9k.
  - L22 step 11 ×12, thr 12−2e: 124k / 100k; 12.5k / 3.3k; 3.95k / 2.7k.
  - L20 step 10 ×14 / step 7 ×19: 205k–284k anchors; 17.9k–23.7k / 4.1k–5.2k cand.
  - Adjacent L20 pair (strobe-like), ≥1 pair: 2.6k / 2.2k cand, but only sound for e ≤ ⌊m/2⌋−1 = 2 (killing every other seed breaks all adjacent pairs).
- At e = 3 the current scheme is best on candidates (NovaSeq 3.4k, mason 1.05k); at e = 6 everything except the pair key degrades to thr 1 (all anchors are candidates).
- Verdict: shorter or denser seeds cut slow-mate loci by ≤ 34% but multiply anchors 2–8×; at 0.05 µs/anchor + 0.37 µs/candidate every scheme is slower than the current one (L25 5.3k / 3.4k µs vs ≥ 7.4k / 4.4k µs). Slow-mate candidates are genuine near-copies (repeats); no seed filter removes them. Index for any L ∈ {20, 22} at the same density (k = L−3, w = 4) ≈ 4.2–4.5 GB, the same as now; current + new ≈ 8.5 GB RAM, does not fit 3.6 GB free disk.
- A sound strobe-like key at e = 4 needs m ≥ 10 disjoint seeds (2×15-mer keys, 30 letters per key) — not measured; the per-candidate cost (speed/wg-speed) is the lever.

Stage-B pruning blocks of 8 letters (was 25) — PROVED (same lemmas, `block_step` holds for any block length ≥ 2):
- Each spoiled 8-letter read block (no exact copy in the band) adds 4 to the death threshold; 31 blocks per 250 bp read instead of 10, so dead passes stop earlier.
- HG002 20k pairs vs chr21, 1 task, GP_K=1, pairs/s (two interleaved runs, dumps identical): T=−24 18.1–18.4k → 20.6–20.7k; T=−32 3.42–3.43k → 4.08–4.34k. Lengths 5/6/10 tried: 8 best or tied.
- Tried and dropped: band loop restricted to non-saturated cells (identical output, 10–20% slower: live cells fill the band).

### Cap ceiling vs minibwa unique proper pairs (bench/cap_table.py, Q25, HG002 200k cut, 2026-10-05)
minibwa alignments re-scored with the spec after Q25 trimming; share of minibwa proper pairs (both MAPQ > 0: 188,963 / both MAPQ ≥ 20: 185,217) whose both mates are within the cap. Upper bound for our mapper (ignores our ties).
| cap | MAPQ>0, ≥50 bp, within proved | MAPQ>0, ≥50 bp, cap only | MAPQ≥20, ≥50 bp, within proved | MAPQ≥20, ≥50 bp, cap only |
|---|---|---|---|---|
| 16 | 92.3% | 92.7% | 93.3% | 93.7% |
| 20 | 93.4% | 94.1% | 94.4% | 95.0% |
| 24 | 94.0% | 94.9% | 94.9% | 95.7% |
| 30 | 94.5% | 95.6% | 95.3% | 96.3% |
| 39 | 94.7% | 96.2% | 95.5% | 96.8% |
| 80 | 94.7% | 97.3% | 95.5% | 97.7% |
| ∞ | 94.7% | 98.5% | 95.5% | 98.5% |
1.5% of pairs have a mate < 50 bp after Q25 trimming. Proved caps (4·(n/25)−1) top out at 94.7% / 95.5%; the rest needs a longer-reach filter proof or end clipping in the spec.

### Accuracy and speed vs minibwa on simulated + real pairs (branch `speed/simeval`, 2026-10-05)
Scripts: `bench/sim_pairs.py` (own simulator: mason-like / HG002-like variants / high divergence), `bench/sim_eval.py` (correct = same chromosome and |Gs∩Ga|/|Gs∪Ga| ≥ 10%, Fig 2a rule; minibwa swept by MAPQ, ours one point per config; our wrong mates re-scored at the truth), `bench/sim_plot.py`, `bench/speed_bars.py` (Fig 3 style Gbp/hr + RSS), `bench/real_plot.py` (same place % via mb_overlap.py), `bench/sim_common.py`. Plots: `sim_roc_reads.png`, `sim_roc_pairs.png`, `sim_time.png`, `speed_bars.png`, `real_time.png`. Data: /home/user/data/sim/mason/ (real mason 2.0.9, paper flags, seed 7, truth tsv), /home/user/data/sim/mason_like_*, /home/user/data/novaseq/hg002_nova_200k_cut_{1,2}.fq (cutadapt, same adapters as HiSeq). Whole genome, 4 threads, Q25 trim, one run each, BIG.lock per run; box shared (±20%). Configs: A = WG_CAP1 150:16,100:12,75:11; B = WG_SHORT=1; P20/P23 = B + pass 2 (150:20 / 150:23,125:19,100:15); C12/C20/C23 = pass-1 caps (≤ proved cap per length; 150 bp mates cannot go past 23, so 24/28 are not possible).
- mason 2.0.9 GRCh38 2×150 200k, % reads aligned / error: minibwa MAPQ≥60 91.65% / 0, ≥40 95.79% / 0, ≥20 96.59% / 2.3e-5, ≥1 97.30% / 7.8e-4, all 100% / 2.0e-2 (paper Fig 2a ≈ 91.5% @1e-7 … 97% @1e-3). Ours, 0 wrong in every config: A 90.45%, B 91.06%, P20 92.70%, P23 93.59%, C12 84.70%, C20 = C23 92.97%. A's 19,096 unmapped pairs: true locus beyond cap 7,447, within cap (tie / not proper) 10,243, mate trimmed / < 75 bp 1,406 (mason puts N in reads). Reasons (50k, A): tie 2,488, noHit 1,230, noPartner 737, short 330, notProper 24.
- Own sims (cross-checks): mason-like A 87.47% / 0 wrong, P23 92.85% / 0; HG002-like variants A 94.63%, 1 wrong pair (spec optimum ≠ truth: truth worse), minibwa ≥60 92.34% (1 wrong read); high divergence (~2.5%) A 60.0%, 2 wrong pairs (truth worse) vs minibwa ≥60 91.9%; pass 2 there exceeds 150 s.
- Mapping time (load excluded) ours A vs minibwa: mason 19.2 vs 11.6 s (0.60×), NovaSeq 2×151 19.0 vs 17.4 s (0.91×), HiSeq 2×250 16.7 vs 25.0 s (1.50×); C12 12.4 / 16.0 / 10.4 s. Pass 2 / caps ≥ 20: 3–7× slower than A. Peak RSS ours 5.6–5.8 GB vs minibwa 7.3–7.6 GB. minibwa 3.1–4.7 Gbp/hr/thread vs paper 4.24.
- Profile (A, mason-like, 20k mates, 1 thread): prep 6 µs, lookups + phase 1 88 µs, stage K 136 µs per mate; 2.2% of mates (repeats, ~3,800 anchors) take 84% of the time. On-target 150 bp reads are where we lose to minibwa.
- Real data, same place % of minibwa unique proper pairs (MAPQ>0 / ≥20): NovaSeq A 88.30 / 90.37, P20 89.16 / 91.25, C23 89.70 / 91.80; HiSeq A 89.53 / 91.32, B 90.07 / 91.87, P23 91.35 / 93.17.
- Caveats: own simulator is an approximation (variants hashed per position, no SVs/CNVs, iid errors); mason's own reads carry N (trimmed by us). No MAPQ for ours yet (Rowan: one point per config until a MAPQ spec). WG_MARGIN not merged anywhere; skipped.

Cap-16 two-gap fallback on word scans — PROVED (`twoGap16K_eq`; WgPacked `twoGap16KG`, `twoGap16KG_same`):
- Profile, repeat-heavy chr21 2×150 at T=−16 (mate 1 at an Alu-like site): phase 1 89% of the search, `ker16K` 73% inclusive, of which the two-gap fallback ~38% (byte first/last-mismatch scans 26%, computed twice when the necessary test passes).
- Now first/last mismatch once per call by `fwdL`/`bwdL` (word scans, `fwdL_eq`/`bwdL_eq`), passed to the necessary test and `twoGapBP`.
- Packed path (`whole_genome pmap`, mode PK, chr21 index, 20k pairs, 1 task, CPU s, 3 alternating runs, dumps identical): repeat-heavy 3.57–3.62 → 3.16–3.48; random 2×150 2.46–2.69 → 2.46–3.08 (noise; the fallback is rare there).
- WFA band pass prototype (gap-affine wavefronts, byte extension): identical dumps, parity speed; core loop 52M Ir vs bandLoopB 108M, but allocation overhead ate the gain. Parked (scratch copy only).

`ker16KW` / `ker16KWG` — PROVED (`ker16KW_eq`; `ker16KWG_same`, `kerHKG_bytes` still rfl):
- Same-length flagged windows at cap 16: `hamA`, then first / last mismatch straight from `fwdA` / `bwdA` (no byte pre-scans, no extra `winOk`), else `ker16K`.
- Packed path (whole_genome pmap PK, chr21 index, 2k repeat-heavy 2×150 pairs, callgrind): 309M → 285M Ir (−7.6%); byte fwdMis/bwdMis on the packed genome 47M → word fwdW/bwdW 27M. Wall/CPU time on 20k pairs within noise (2.37–2.64 → 2.39–2.49 CPU s). Dumps identical.
- Remaining there: hamW 51M, `hamming` of the two-gap middle check 33M, flagsOk 13M.

Flank table (C), measured, not built (held: ~20% exact gain vs a large proof build; spec may change):
- Setup: whole genome (GRCh38 primary chr1–22,X,Y from the 1000G S3 copy; own index, 1,580 s build, check3P true). 20k pairs per set: NovaSeq HG002 2×151 pairs 1,000,001–1,020,000; mason 2.0.9 GRCh38 2×150 (`--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5`); HG002 HiSeq 2×250 (`D1_S1_L001_*_004`). Adapters cut by a cutadapt-like Python cut (substitutions only, overlap ≥ 3, ≤ 10% mismatches; PyPI blocked here), then the mapper's Q trim. Bench only: `WG_FLANK`, `WG_PART` in bench/WholeGenome.lean (fa3fb57, b596d1c).
- Slow strands = read strands with > 1000 anchors of the `hitsSK` seeds (cheapest sbound(16)+1) at cap 16. Counts are whole-genome distinct diagonals per strand (A, fixed pieces) or occurrences (C; ~90% are distinct diagonals).
- (A) flanks into the neighbouring seeds (C = seed occurrence count, f letters each side), diagonals: NovaSeq (6,155 strands) now 63.4M → C 1000: f4 23.0M, f8 12.2M, f16 6.4M, f25 4.3M; C 10000 f16 27.6M; C 50000 f16 48.8M. HiSeq (3,101) 21.7M → C 1000 f16 3.5M; C 10000 f16 10.9M. mason (5,895) 52.0M → C 1000 f16 5.2M; C 10000 f16 24.4M. Most diagonals come from seeds with 1k–10k occurrences. Not covered by the pigeonhole (the flanks overlap looked-up seeds): an optimistic bound.
- Fixed disjoint pieces (sbound+1 pieces of n/(sbound+1) letters): NovaSeq 52.8M (prefix 25-mers alone 104.6M), HiSeq 15.1M, mason 41.8M — they lose the cheapest-seed choice.
- (C) best partition per read: sbound+1 = 5 disjoint segments (5-letter grid, each ≥ 25 letters), each by its cheapest grid 25-mer with the whole segment exact; ~1000 slow strands per set, occurrences: NovaSeq 11.95M → 4.17M (2.9×), HiSeq 9.17M → 3.31M (2.8×), mason 8.90M → 2.62M (3.4×). Oracle choice (true counts of 26 / 46 grid 25-mers + extensions per 150 / 250 bp strand); a table version would read counts as range sizes (binary search on (25-mer, right flank)) and extend segments rightwards only, so somewhat below this.
- Memory at count > 1k (bucket-size proxy): 51M entries ≈ 255 MB of positions (> 10k: 14M, 70 MB; > 50k: 2.6M, 13 MB); flanks compared against the packed genome during the search.
- Estimate (not measured): NovaSeq 20k, 7.4M slow-read diagonals × ~65% removed × ~500 ns ≈ 2.4 s of ~12 s (~20%); choosing ~26–46 binary searches per slow strand (~0.04 s per set).
- Lemma shape: for any list of disjoint read segments (each ≥ 2 letters, chosen by any rule), a window within penalty x leaves one of more than sbound(x) segments clean (`exists_clean_seed_amongE` / `coverLE` with segments for seeds); the segment lookup returns every exact match of the whole segment (replaces `hArr`'s "every exact match of the 25-mer" for the segments, via the table's sortedness + range bounds, or the anchor list filtered on the extension).
