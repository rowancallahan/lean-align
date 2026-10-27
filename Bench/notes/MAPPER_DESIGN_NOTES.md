# Design notes: a verified, fully sensitive short-read mapper

Written 2026-09-15 from a planning conversation. Placeholder prose; Rowan
rewrites anything public and writes the specification by hand. Nothing here is
implemented. Speed figures are estimates unless a source is given.

## 1. Goal and claim

A short-read mapper written in Lean. Its speed target is near the frontier,
possibly after a later Rust + Aeneas port.

Its guarantee is machine-checked from spec to executable code: every non-excluded read (or read pair) gets
- every location within k edits, and
- the exact best-scoring set among them.

Proposed claim wording (precise, to avoid counterexamples):

> The first read mapper with machine-checked proofs, from specification to
> executable code, that every non-excluded read gets every location within k
> edits, optimally scored.

Trust base, named explicitly:
- the Lean kernel and compiler;
- the I/O layer;
- the index checker.

The exclusion rules and parameters are part of the spec.

Also shipped as a testing artifact: a proved gold standard for scoring other
mappers (section 9).

## 2. Prior art (see ALIGNMENT_READING_LIST.md)

- **RazerS / RazerS 3** (SeqAn):
  - fully sensitive k-error mapping, with a paper proof (pigeonhole, q-gram lemma / SWIFT filter);
  - unverified C++;
  - indexes the reads and scans the reference;
  - checks candidates with banded Myers bit-vector alignment;
  - RazerS 3 paper: about 9 GB best-mode / 15 GB all-mode for 10M 100 bp reads on human.
- **Rabema** (2011): formal definition of read mapping as "every interval within distance k".
  - Categories: all / all-best / any-best.
  - Gold standard generated with RazerS.
  - Tested Bowtie, BWA (backtrack), SHRiMP2 and SOAP2 on fly and yeast.
  - Findings:
    - SHRiMP2 had the highest all-locations sensitivity above 3 errors;
    - BWA was best at finding one best location;
    - on simulated data BWA and SHRiMP2 found best locations for ≥ 90% of intervals;
    - parameters changed results by more than 20 points.
- **Isabelle building blocks (not a mapper):**
  - verified suffix array construction, including SA-IS (Cheung & Rizkallah, AFP 2024 / JAR 2025);
  - the Burrows–Wheeler transform and its inverse (AFP Jan 2025 / CPP 2025);
  - KMP and Aho–Corasick string search (AFP);
  - Monad_Memo_DP (edit distance, LCS).
- **Briefings in Bioinformatics 2025,** "Formal verification of bioinformatics software using model checking and theorem proving":
  - CBMC found generic C bugs in BWA and other libraries;
  - Rosette/Z3 was applied to two toy models;
  - no aligner verified.
- **Earlier search (2026-08-18):** no mechanized Smith–Waterman, Needleman–Wunsch with general scoring, or affine-gap alignment in any prover.
- **Searches on 2026-09-14/15:** no verified read mapper found in Isabelle, Coq, Lean, Dafny, Why3, F* or Verus.
- **Still to do before a public claim:** a manual pass over:
  - the full AFP index;
  - Rocq/Coq opam packages;
  - Dafny, Verus and F* example repositories;
  - arXiv and bioRxiv;
  - CPP, ITP and WABI proceedings.

## 3. Specification shape

### 3.1 Single read
- **Alignment mode:** semi-global, with the whole read aligned and reference-side end gaps free.
  - The existing repo spec is global (end gaps penalized; ALIGNMENT_THEOREMS_FOR_REVIEW.md item 4) and needs the ends-free variant.
  - Soft clipping (local with a clip penalty) can come later.
- **Error bound:** k edits, chosen moderate (about 4–6 for 150 bp).
  - Most human reads have 0–3 edits (about 0.1% SNP divergence plus about 0.1–1% sequencing error).
  - Reads beyond k are flagged "too divergent".
- **Best set:** the minimum edit count e* ≤ k, plus every location achieving it. Uniqueness is reported by checking whether any location has e*+1 edits.
- **Exclusion is an output, not a precondition.** Define a computable predicate `excluded(read, reference)` and prove:
  - not excluded ⇒ complete and optimal;
  - excluded ⇒ flag.

  This covers every input, and the exclusion rate is reported.
- **Repetitive:** defined on the read and reference, not on index internals.
  - Read split into k+1+s pieces.
  - A piece is over-cap if it has more than c exact occurrences.
  - Excluded only if more than s pieces are over-cap: k edits touch at most k pieces, so at least s+1 pieces are exact and up to s over-cap pieces can be skipped with completeness intact.
  - The piece layout, k, s and c are spec parameters.
- **Low scoring:** threshold T. Completeness is promised over locations scoring at least T; otherwise the read is flagged "no confident alignment".
- **Masking:** none. Nothing is removed from the reference. Masking was considered and rejected: it lets repeat-derived reads map confidently to similar unmasked copies.

### 3.2 Read pairs
- **Normalization:** read 1 as sequenced, plus the reverse complement of read 2.
- **Proper pair:** both normalized mates align to the same reference strand (+ or −) on the same contig, with read 1 first along that strand's direction.
  - This equals the standard FR orientation.
  - Other library types (e.g. RF mate-pair) change only the normalization step.
- **Template length:** from read 1's start to the end of reverse-complemented read 2, along the strand, in [I_min, I_max].
  - The insert size may be estimated from data beforehand, but is fixed as an input before the proved search runs.
- **Edit limits:** per-mate (each ≤ k) or combined (sum ≤ K). Decide which.
- **Best pair set:** minimum total edits; ties reported as a set.
- **Completeness:** every proper-pair placement within the limits is found.
- **Pair-level exclusion:** exclude only when neither mate can anchor the pair (both over the repeat cap), or when low scoring or too divergent.
  - A repetitive mate is placed by scanning the anchor mate's window completely.
- **Edge cases to state explicitly:** short fragments (mates overlap or read into adapter), dovetailed mates, contig ends, circular contigs (chrM).
- **Out-of-spec pairs** (orientation, insert size, different contigs) are flagged "not properly paired within spec", never dropped. They double as the discordant-pair signal.

### 3.3 Batches
The spec stays per read (per pair): the batch result is the per-read spec mapped over the input, in order. No batch-level spec is needed. See section 7 for the proof layers.

## 4. Index

### 4.1 Spec
`lookup ref pattern` = exactly the positions where `pattern` occurs in `ref`.
Every structure and layout below is an implementation of this.

### 4.2 Structure choice
Pigeonhole seeding needs exact matches of fixed-length pieces (about 25–40 bp), not maximal exact matches.

| Structure | Cache misses per lookup | Memory (human) | Notes |
|---|---|---|---|
| FM-index (BWA, Bowtie) | About 1 per base (≈30 for a 30 bp piece) | A few GB (minibwa BWT ≈ 3 GB) | Suits variable-length matches |
| Suffix array + prefix bucket table | 1 jump + short binary search | 32-bit positions (3.1 Gb < 2³²): ≈ 12.4 GB one strand | Any piece length; search reads' reverse complements instead of indexing both strands |
| Sorted k-mer array / hash (minimap2, strobealign style) | 1–2 | Depends on sampling | Fastest for one fixed length |

**Laptop target (6–12 GB).** The fast structures are larger than the budget. Options:
- a sampled suffix array;
- a sampled k-mer table, with sampling aligned to piece boundaries so completeness holds;
- partitioning into 4 pieces:
  - partitions overlap by at least read length + k;
  - every read is searched against all partitions, keeping best-so-far per read, spilled to disk in read order;
  - one extra covering lemma is needed;
- the RazerS-style design: index the read batch and scan the reference in chunks, so memory scales with batch size.

### 4.3 Layout tricks (all provable against the lookup spec)
- 2-bit packed reference; 32-bit positions.
- Prefix bucket table (first 12–14 bases).
- Cache-line-sized blocks (BWA-MEM2 / minibwa: 64-byte blocks holding counts plus 128 bp of 2-bit sequence).
- Batched, interleaved lookups; seeds sorted by index position.
- Huge pages (OS setting, outside the proof).
- A learned hint, as in BWA-MEME. Recommended form: gallop outward from any hint, then binary search.
  - The proof is one sorted-array lemma.
  - The model needs no proof and may use floating point.
  - The BWA-MEME-style stored error bound would need a build-time checker whose float evaluation matches runtime; avoid it.
  - Memory caveat: BWA-MEME's modes use much more memory than BWA-MEM2 (tens of GB, from memory, unchecked).

### 4.4 Construction outside the proof
- Build with any fast tool.
- Run a proved checker at build time:
  - suffix array: permutation, sorted, bucket table agrees;
  - k-mer table: one reference scan.
- Stamp the index with a hash; the mapper refuses a mismatched index.
- Runtime proof = lookup correctness + "index passed checker". SA-IS never needs proving.

## 5. Alignment kernel

- **Primary: the existing proved WFA (U3).** Reads are close to the reference, where WFA is cheapest, and it needs no SIMD.
- **Needed changes:**
  - **Semi-global ends-free variant** (spec + kernel proofs). Probably the largest change.
  - **Score cap:** `wfa_capped B` returns the optimum if it is ≤ B, otherwise "over bound". This enables branch and bound; a small proof extension.
  - **Short-call overhead:** existing benchmarks are 1 kb / 10 kb pairs. Mapping makes many 150 bp calls against short windows. Use per-worker buffers reused across calls, and time 150 bp calls directly.
- **Fast paths before the wavefront:**
  - ungapped check first (minibwa does this);
  - the existing `compactSmall` (exact 1–2 substitution) path.
- **Alternative for a pure edit-distance spec:** banded Myers bit-vector; band 2k+1 ≤ 64 fits one `UInt64`.
- **For comparison:** minibwa uses ungapped alignment, then SIMD DP (SSE4.1/NEON) with dual affine gaps, semi-global, citing Suzuki & Kasahara 2018 (likely ksw2-style); no WFA. SIMD DP suits tools that have SIMD; proved Lean does not, which favours WFA or bit-vector.

## 6. Provable speed tricks (output identical to spec)

★ = likely biggest wins (estimate).

**Candidate filtering**
- ★ **Piece–diagonal agreement:** keep only windows with at least s+1 piece hits within ±k of one diagonal. Pigeonhole plus position-shift bound.
- **q-gram count threshold** (q-gram lemma).
- **Base-composition lower bound** on edit distance.
- **Merge overlapping candidate windows** (coverage lemma).
- **Precomputed repeat bitmap** at index build (checked).
- **Paired geometry filter:** keep a mate location only if the other mate has hits consistent with strand, order and window.

**Candidate checking**
- ★ **Stratified early exit:** 0 edits, then 1, then 2…; stop at the first non-empty level (+1 for uniqueness).
- ★ **Branch and bound:** cap later candidates at the best e found (e+1 for uniqueness); check the most promising candidates first. Order-independence of min.
- ★ **Score first, traceback only for reported winners.**
- **Ungapped mismatch count** as an early upper bound.
- **Early DP stop** when every band cell exceeds the bound.
- **Word-level comparison:** 2-bit packed, 32 bases per `UInt64` (XOR + popcount / trailing zeros); induction on words.
- **Pair rescue:** complete scan of the anchor mate's window (≤ I_max, about 500–1,000 bp).

**Across reads**
- **Identical-read dedup** within a batch (map = map over distinct + lookup).
- **Read + reverse complement searched together** against a single-strand index.
- **Seeds sorted / interleaved lookups; memoized repeated k-mer lookups** (pure function).

## 7. Batching, chunking, multithreading: proof layers

1. **Batched kernel = map over the batch.** The interleaved step acts on each read's state independently; induction on steps. Proving 1- and 2-read cases first is a warm-up or test, not the route to n.
2. **Chunking = map:** split into n chunks of m, map, concatenate (list lemma).
3. **Parallel = sequential:** one task per chunk; `(Task.spawn f).get = f ()`.

**Engineering notes**
- Flat `ByteArray` read buffers with offset arrays; per-worker, uniquely owned, reused scratch buffers.
- The shared read-only index is accessed through borrowed parameters, so no atomic reference counts on the hot path.
- Pipeline: streaming reader → bounded chunk queue → workers → ordered writer. Memory = index + chunk × threads.
- Hardware threads: set task count = logical CPUs; measure with half. Seeding (cache-miss bound) likely gains more than extension.
- At 32–64 threads, expect memory bandwidth and I/O to bound throughput:
  - gzip decompression is single-stream unless BGZF;
  - FASTQ parsing and SAM/BAM writing also cost.

  Use byte-level parsing and parallel output; lean-zip is Lean-native deflate.

**Snakemake**
- one aligner at a time: `threads: workflow.cores`, or `resources: aligner=1` with `--resources aligner=1` (plus `mem_mb` on a laptop);
- or one job aligning all samples in one process, loading the index once;
- or a memory-mapped index shared through the page cache (needs a small trusted FFI layer).

## 8. Speed landscape and targets

**Mappers (short-read WGS)**
- **strobealign:** fastest; 4–6× BWA-MEM, ≈ 3.5× BWA-MEM2.
- **minibwa** (Heng Li & Nils Homer, arXiv 2606.15357, June 2026):
  - ≈ 4× BWA-MEM, > 2× BWA-MEM2, ≈ 10% slower than strobealign, with better variant calls in their tests;
  - BWA seeding with prefetch batching, minimap2 chaining, 50 best chains, repetitive short seeds skipped, 7-mer mate-rescue prefilter;
  - extension ≈ 35% of CPU time;
  - "<<20 GB" peak at 32 threads; BWT ≈ 3 GB;
  - benchmarked on 2× Xeon Gold 6130, 32 threads, output to /dev/null (I/O excluded), no thread-scaling experiment.
- **BWA-MEME / BWA-MEM3:** faster than BWA-MEM2 (BWA-MEME: identical output, up to 3.45× seeding).
- **BWA-MEM2:** ≈ 1.7× BWA-MEM, identical output. BWA-MEM remains the pipeline default; variant callers are tuned to its output.
- **Heuristics everywhere** (occurrence caps, reseeding, chain dropping, band / Z-drop, capped mate rescue). None is complete for k errors.

**Laptop estimate for 30M pairs (2×150)**
- Anchor: bwa-mem2 ≈ 31 s per million reads, from the bwa-mem4 README; setup unconfirmed, possibly M4 Max, 8 threads.
- Estimates:
  - minibwa ≈ 15 min on such a machine, 20–40 min on a typical 8-core x86 laptop;
  - BWA-MEM ≈ 1.5–3 h;
  - sorting and compression extra.
- Measure 1M pairs on the target machine.

**Targets (estimates)**
- **BWA-MEM throughput in optimized Lean:** plausible, not certain.
  - For: stratified exit on most reads, exclusion of repeats, multithreading.
  - Against: the Lean WFA is 1.6–4.7× behind BiWFA; no prefetch.
- **minibwa throughput:** needs Rust + Aeneas plus minibwa-level seeding engineering.
- **strobealign:** unlikely while fully sensitive.
- **Plan:** a chr20 prototype of stratified 0/1/2-edit semi-global search in Lean, measured in reads/s per core against bwa-mem2 on x86, before deeper investment.

## 9. Benchmark artifact (proved gold standard)

- **Input:** 1M reads (simulated first, chr20), then human / HG002.
- **Gold standard (proved):** for each non-excluded read or pair, the best set and the all-within-k set.
- **Categories for each tested mapper** (bwa-mem2, minimap2, strobealign, minibwa):
  - correct: in the best set (any tied location counts);
  - valid but suboptimal: within k, worse than best;
  - misplaced: not within k;
  - missed: unmapped although a location exists;
  - overconfident: high mapping quality despite tied best locations;
  - excluded reads reported separately.
- **Compare by reference interval,** with a stated rule for soft-clipped alignments (Rabema's interval approach).
- **Two views on simulated data:** agreement with the proved best set, and with the true simulated origin. Best-scoring ≠ true origin when:
  - the sample has sequence absent from the reference (e.g. a paralog);
  - a sequencing error tips a tie.

  The gap between the two views is itself a result.
- **Variant artifacts:** cluster each mapper's misplaced reads by locus; sites with consistent mismatches become "false variant candidates"; cross with that mapper's false-positive calls against GIAB HG002.
- **Trust:** generator proved; SAM parsing and interval comparison trusted unless also written in Lean.
- **Differences from Rabema:**
  - modern mappers;
  - human genome, 150 bp pairs;
  - proved (not RazerS-generated) gold standard;
  - variant-artifact analysis.

## 10. Speed path beyond Lean

- **Lean now:** tasks; `ByteArray` packing; clang flags (`moreLeancArgs = ["-O3", "-march=x86-64-v3"]`, not yet in the lakefile); hot code kept in one module. Already done in wfa_u32: `UInt32` arrays, `uget`/`uset`, `USize`, `@[inline]`, one-module hot loops, no runtime `Nat` literal parsing. No multithreading anywhere in the repo yet.
- **Not available to proved Lean code:**
  - SIMD intrinsics, prefetch, GPU (Parabricks), FPGA (DRAGEN);
  - memory mapping and fast gzip/BGZF only via a trusted FFI I/O layer.
- **Rust + Aeneas (chosen direction for speed):**
  - safe Rust extracted to Lean;
  - proved equal to the existing Lean model;
  - LLVM auto-vectorization gives AVX2 with nothing opaque;
  - explicit intrinsics are out (no opaque models wanted);
  - prefetch is the one harmless candidate (model = `()`);
  - `rustc`/LLVM trusted.
  - hax + F* (Cryspen's 565 tested intrinsic models) not chosen, since proofs stay in Lean.
  - Caution from ePrint 2026/192: a wrong AVX2 multiply axiom in libcrux's ML-DSA F* proofs made them unsound (the model, not the hardware).
- **Machine-code proofs (trimmer/asm, Sail RISC-V):** trust gain, not speed, at large cost. Not the route for the mapper.

## 11. First steps (smallest first)

1. Semi-global spec (Rowan).
2. Single-read stratified search with exclusion as output, proved against a small reference.
3. Pair spec and pair search with window rescue.
4. Batch / chunk / task layers with their equality proofs.
5. chr20 index: suffix array + bucket table, proved checker, lookup proof.
6. Benchmark artifact on 1M simulated chr20 reads.
7. Measure reads/s per core against bwa-mem2 on x86; decide on the Rust + Aeneas port.

## 12. Open decisions

- Pair edit limits: per-mate k or combined K.
- k, s, c, T, I_min / I_max defaults.
- Scoring for the spec: unit edit distance (Myers-friendly) or affine (WFA / variant-caller-friendly).
- Soft clipping: in the first spec or later.
- Index: sampled suffix array vs partitioned vs read-indexed scan, for the laptop target.

## Sources

- RazerS 3: https://academic.oup.com/bioinformatics/article/28/20/2592/206947
- RazerS: https://genome.cshlp.org/content/19/9/1646
- Rabema: https://pmc.ncbi.nlm.nih.gov/articles/PMC3128034
- minibwa: https://arxiv.org/html/2606.15357v1
- strobealign: https://genomebiology.biomedcentral.com/articles/10.1186/s13059-022-02831-7
- BWA-MEME: https://academic.oup.com/bioinformatics/article/38/9/2404/6543607
- bwa-mem2: https://github.com/bwa-mem2/bwa-mem2
- bwa-mem4 (throughput anchor): https://github.com/IPNP-BIPN/bwa-mem4
- Suffix array (AFP): https://www.isa-afp.org/entries/SuffixArray.html
- BWT (AFP): https://www.isa-afp.org/entries/BurrowsWheeler.html
- Bioinformatics formal verification review: https://academic.oup.com/bib/article/26/4/bbaf383/8221466
- Aeneas: https://github.com/AeneasVerif/aeneas
- Rust-to-Lean pipeline with AI provers: https://arxiv.org/html/2605.30106
- Cryspen SIMD models: https://cryspen.com/post/specify-rust-simd/
- False Assurance (ePrint 2026/192): https://eprint.iacr.org/2026/192.pdf
