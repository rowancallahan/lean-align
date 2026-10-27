import Lake

open Lake DSL

/-!
lean-align: proved pairwise alignment, compiled to one command-line tool.

  Main.lean            every file-system call the tool makes (trusted, short)
  LeanAlign/           pure code: command line (Cli) and bytes-in → bytes-out (Run)
  Spec/                THE specification: Alignment, Mapping, Aligner, Shim (frozen, Spec/FROZEN.sha256);
                       Sam, Fasta, Fastq are trusted plumbing for the shim (not guaranteed)
  old_spec/            the earlier frozen specs the current proofs are built on, and theorems about Cli and Run
  kernels/<group>/     alignment kernels, each proved against old_spec/AlignmentSpec.lean
  index/<group>/       index kernels (minimizer, packed genome, CSR, ...)
  mapper/              the main mapping code (tier router, pair search); mapper/lemmas/ supporting lemmas
  Proofs/              Spec/ with the proofs filled in (comparator solution)
  trimmer/             read-window trimmer (frozen contract + proved implementations)
  checks/, scripts/    executable cross-checks and the full re-check script

Module names are unchanged from the read_window_trimmer repository.
-/

package lean_align where
  version := v!"0.1.0"

-- ───────────────────────────── spec ─────────────────────────────

@[default_target]
lean_lib Spec where                  -- THE specification (statements only; buildIndex / alignPairs are holes)
  globs := #[.submodules `Spec]

@[default_target]
lean_lib Proofs where                -- the spec with proofs filled in (same names; checked against Spec/ by comparator)
  globs := #[.submodules `Proofs]

@[default_target]
lean_lib AlignmentSpecLib where       -- earlier specs, still what the codecs are proved against
  srcDir := "old_spec"
  roots := #[`AlignmentSpec, `AlignmentLexicographic, `MapSpec, `PairSpec, `PairSpecTier, `PairSpecU]

-- ──────────────────────────── alignment kernels ────────────────────────────

@[default_target]
lean_lib KernelsBand where   -- bandDoublingAlign (full equality with the spec)
  srcDir := "kernels/band"
  roots := #[`AlignmentWavefront]

@[default_target]
lean_lib KernelsGapless where   -- gapless and one-indel alignments
  srcDir := "kernels/gapless"
  roots := #[`MapperGapless, `MapperOneIndel]

@[default_target]
lean_lib KernelsGotoh where   -- gotohFusedAlign (full equality with the spec)
  srcDir := "kernels/gotoh"
  roots := #[`AlignmentAlgorithms]

@[default_target]
lean_lib KernelsK250 where   -- word kernels on candidate windows (MapperK250*, FastGenK250)
  srcDir := "kernels/k250"
  roots := #[`FastGenK250, `MapperK250, `MapperK250Bits, `MapperK250Chunk, `MapperK250Loops, `MapperK250Seed, `MapperK250Sel, `MapperK250Spec, `MapperK250Words]

@[default_target]
lean_lib KernelsMapperBand where   -- banded kernel for the mapper (MapperBand*, BandScore)
  srcDir := "kernels/mapper_band"
  roots := #[`BandScore, `MapperBandBytes, `MapperBandFast, `MapperBandKernel, `MapperBandProof, `MapperBandPrune, `MapperBandSpec]

@[default_target]
lean_lib KernelsWfa where   -- wfaAlign: the proven wavefront (score + sound + total)
  srcDir := "kernels/wfa"
  roots := #[`AlignmentExchange, `AlignmentWfa]

@[default_target]
lean_lib KernelsWfaFast where   -- wfaAlignI/F/L: executed paths proven = wfaAlign
  srcDir := "kernels/wfa_fast"
  roots := #[`AlignmentWfaFast, `AlignmentWfaFused, `AlignmentWfaLazy, `AlignmentWfaLazyLevel]

@[default_target]
lean_lib KernelsWfaOffsets where   -- wfaAlignC / wfaAlignCA: offsets-only fronts + certified traceback
  srcDir := "kernels/wfa_offsets"
  roots := #[`AlignmentWfaArray, `AlignmentWfaCertified, `AlignmentWfaDirect, `AlignmentWfaLcp, `AlignmentWfaOff, `AlignmentWfaOffLoop, `AlignmentWfaOffR, `AlignmentWfaPoint, `AlignmentWfaView]

@[default_target]
lean_lib KernelsWfaRuns where   -- wfaAlignK: direct run-length traceback with scalar checker
  srcDir := "kernels/wfa_runs"
  roots := #[`AlignmentCigarCheck, `AlignmentCigarCheckFast, `AlignmentTraceRuns, `AlignmentWfaRuns, `AlignmentWfaRunsFast, `AlignmentWfaRunsVsWfa]

@[default_target]
lean_lib KernelsWfaSmallErrors where   -- wfaAlignH / wfaAlignHC: exact ≤2-substitution shortcut + compact output
  srcDir := "kernels/wfa_small_errors"
  roots := #[`AlignmentCompact, `AlignmentSmallErrors]

@[default_target]
lean_lib KernelsWfaU32 where   -- proved UInt32 kernels U/U2/U3 (U3 is the one the tool runs)
  srcDir := "kernels/wfa_u32"
  roots := #[`AlignmentWfaU32, `AlignmentWfaU32Ext, `AlignmentWfaU32Fill, `AlignmentWfaU32Fill3, `AlignmentWfaU32FillS, `AlignmentWfaU32FillSSpec, `AlignmentWfaU32FillSpec, `AlignmentWfaU32FillSpec3, `AlignmentWfaU32Kernel2, `AlignmentWfaU32Kernel3, `AlignmentWfaU32Lattice, `AlignmentWfaU32Level, `AlignmentWfaU32Level2, `AlignmentWfaU32Level3, `AlignmentWfaU32LevelS, `AlignmentWfaU32Loop, `AlignmentWfaU32Loop3, `AlignmentWfaU32Run2, `AlignmentWfaU32Run3, `AlignmentWfaU32Single, `AlignmentWfaU32Step, `ProbeU32, `WfaU3]

-- ──────────────────────────── index kernels ────────────────────────────

@[default_target]
lean_lib IndexCsr where   -- CSR index
  srcDir := "index/csr"
  roots := #[`CsrIndex]

@[default_target]
lean_lib IndexKmer where   -- k-mer index
  srcDir := "index/kmer"
  roots := #[`MapperFastIndex]

@[default_target]
lean_lib IndexMinimizer where   -- minimizer index (MzIndex) and its checkers
  srcDir := "index/minimizer"
  roots := #[`MapperMzWords, `MzCheckFast, `MzCheckPar, `MzIndex, `MzView, `MzWord]

@[default_target]
lean_lib IndexPackedGenome where   -- 2-bit packed genome
  srcDir := "index/packed_genome"
  roots := #[`MapperPGen, `MapperPacked, `MzPacked, `WgPacked]

@[default_target]
lean_lib IndexRepeatMask where   -- repeat masking
  srcDir := "index/repeat_mask"
  roots := #[`RepeatMask]

@[default_target]
lean_lib IndexSketch where   -- seed sketches
  srcDir := "index/sketch"
  roots := #[`MapperSketch]

-- ──────────────────────────── mapper (main code) ────────────────────────────

@[default_target]
lean_lib Mapper where   -- tier router, pair search, batching: the code alignPairs runs
  srcDir := "mapper"
  roots := #[`EarlyStopMapper, `FastGen, `FastGenAlgo, `FastGenBatch, `FastGenBlock, `FastGenCover, `FastGenCoverE, `FastGenCoverL, `FastGenMz, `FastGenPair, `FastGenPairPacked, `FastGenProof, `FastGenShort, `FastGenSupp, `FastGenTier, `FastGenTierK, `FastGenTierPacked, `FastGenWordFilt, `FastMapper, `FastMapperMz, `FastMapperPar, `LowErrorMapper, `MateFloor, `PairBnB, `PairBox, `PairConcat, `PairConcatPacked, `PairDispatch, `PairExact, `PairGuarFast, `PairGuarQ, `PairGuarQB, `PairGuarQC, `PairGuarQD, `PairGuarQE, `PairGuarantee, `PairHits, `PairHitsKP, `PairHybrid, `PairInterleave, `PairJoin, `PairJoint, `PairLadder, `PairLadderF, `PairMapper, `PairNear, `PairPacked, `PairReason, `PairRegion, `PairRegionU, `PairRouter, `PairSched, `PairUnique, `ParGroup, `ParMap, `ParStream, `PreFilterMapper, `ReadTrim, `SeedMapper, `SeedMapper2, `SketchMapper, `TierOpt, `TierRouter]

@[default_target]
lean_lib MapperLemmas where   -- lemmas for the seed-and-index mapper
  srcDir := "mapper/lemmas"
  roots := #[`MapperBytes, `MapperDefs, `MapperEvents, `MapperFastAlgo, `MapperFastBest, `MapperFastBytes, `MapperFastKernel, `MapperFastLazy, `MapperFastLoop, `MapperFastMerge, `MapperFastScore, `MapperFastSupport, `MapperGRead, `MapperGen16, `MapperGenBest, `MapperGenLook, `MapperGenScore, `MapperGenSearch, `MapperGenShare, `MapperInterleave, `MapperLists, `MapperSeedsAmong, `MapperWalk, `MapperWalk2]

-- ──────────────────────────── trimmer ───────────────────────────

@[default_target]
lean_lib Trimmer where
  srcDir := "trimmer"
  roots := #[`ReadWindowTrimmer]

-- ───────────────────────────── tool ─────────────────────────────

@[default_target]
lean_lib LeanAlign where
  roots := #[`LeanAlign]

@[default_target]
lean_exe «lean-align» where
  root := `Main

-- ──────────────────────────── bench ─────────────────────────────

lean_exe map_bench where              -- benchmark only; prints to stdout
  srcDir := "bench"
  root := `MapBench

lean_exe proto where                  -- speed prototype only (unproved)
  srcDir := "bench"
  root := `Proto

lean_exe map_bench2 where             -- benchmark only: mapWithIndex vs mapWithIndex2 / 2V
  srcDir := "bench"
  root := `MapBench2

lean_exe band_bench where             -- banded kernel vs wfaAlignU3 (benchmark only)
  srcDir := "bench"
  root := `BandBench

lean_exe csr_bench where              -- CSR index build/save/load/check timing (unproved IO)
  srcDir := "bench"
  root := `CsrBench

lean_exe par_bench where              -- parMap threads / shared-memory check only
  srcDir := "bench"
  root := `ParBench

lean_exe stream_bench where           -- writer overlapped with mapping, benchmark only
  srcDir := "bench"
  root := `StreamBench

lean_exe lowerr_bench where           -- benchmark only: low-error fast path vs mapWith
  srcDir := "bench"
  root := `LowErrBench

lean_exe group_bench where            -- dedup / sort / binned pipelines vs plain streaming, benchmark only
  srcDir := "bench"
  root := `GroupBench

lean_exe gen_try where                 -- experiments on the general fast path (unproved IO)
  srcDir := "bench"
  root := `GenTry

lean_exe fast_bench where             -- proved fast mapper on a real genome (unproved IO)
  srcDir := "bench"
  root := `FastBench

lean_exe layout where                 -- index layout bench (unproved)
  srcDir := "bench"
  root := `Layout

lean_exe proto_sketch where           -- seed-scheme prototype (unproved): k-mer / minimizer / syncmer / mod-minimizer index
  srcDir := "bench"
  root := `ProtoSketch

lean_exe mz_test where                -- randomized test: proved MzIndex lookup vs naive scan
  srcDir := "bench"
  root := `MzTest

lean_exe proto2 where                 -- speed prototype 2: closed-form scoring (unproved)
  srcDir := "bench"
  root := `Proto2

lean_exe micro where                  -- micro-benchmarks of Lean code patterns
  srcDir := "bench"
  root := `Micro

lean_exe map_dump where               -- benchmark only; per-read results of the proved mapper
  srcDir := "bench"
  root := `MapDump

lean_exe proto0 where                 -- first speed prototype, kept for comparisons (unproved)
  srcDir := "bench"
  root := `Proto0

lean_exe k250_bench where             -- word kernels vs byte kernels on candidate windows (unproved IO)
  srcDir := "bench"
  root := `K250Bench

lean_exe gen_pair_bench where         -- proved general-path pair mapper (pairFastGB) over a concatenated index (unproved IO)
  srcDir := "bench"
  root := `GenPairBench

lean_exe pair_bench where             -- proved pair mapper (pairFast) on mate files (unproved IO)
  srcDir := "bench"
  root := `PairBench

lean_exe packed_bench where           -- 2-bit packed mismatch count vs byte loop (unproved IO)
  srcDir := "bench"
  root := `PackedBench

lean_exe trim_map where               -- trimmed FASTQ pairs → proved trimmer → proved pair mapper (unproved IO)
  srcDir := "bench"
  root := `TrimMap

lean_exe whole_genome where           -- whole genome held once: index over a view of the chromosomes (unproved IO)
  srcDir := "bench"
  root := `WholeGenome

lean_exe seed_lab where               -- seed lookup cost on the whole genome (benchmark only, unproved IO)
  srcDir := "bench"
  root := `SeedLab
