import Lake

open Lake DSL

/-!
lean-align: proved paired-end alignment, compiled to one command-line tool.

  Main.lean    every file-system call the tool makes (trusted, short)
  Spec/        THE specification (frozen, Spec/FROZEN.sha256)
  Proofs/      Spec/ with the proofs filled in; Proofs/core/ = the internal model the code is proved against
  Aligner/     the code that runs: kernels/, index/, mapper/, trimmer/, LeanAlign/ (CLI parsing, bytes in / bytes out)
  Testing/       benches/, scripts/ (CI_check.sh, check.sh), checks/, tests/, data/, notes/

Module names are unchanged from the read_window_trimmer repository; folders map to modules below.
-/

package lean_align where
  version := v!"0.1.0"

-- ───────────────────────────── spec ─────────────────────────────

@[default_target]
lean_lib Spec where                  -- THE specification (statements only; buildIndex / alignPairs are holes)
  globs := #[.submodules `Spec]

@[default_target]
lean_lib Proofs where                -- the spec with proofs filled in (same names; checked against Spec/ by comparator)
  roots := #[`Proofs.Alignment, `Proofs.Mapping, `Proofs.Answer, `Proofs.Hits, `Proofs.Tiers, `Proofs.Bridge, `Proofs.Whole, `Proofs.Report, `Proofs.LastResort, `Proofs.GaveUp, `Proofs.Heavy, `Proofs.HeavyBuild, `Proofs.Index, `Proofs.Pack, `Proofs.Floor, `Proofs.Aligner, `Proofs.SaveLoad, `Proofs.Shift, `Proofs.Build, `Proofs.IndexBuild, `Proofs.IndexFinal, `Proofs.Fasta, `Proofs.Fastq, `Proofs.Sam, `Proofs.TrimRecord]

@[default_target]
lean_lib Core where                  -- proof internals: what the kernels and router are proved against, translated to Spec/ in Proofs/Bridge.lean
  srcDir := "Proofs/core"
  roots := #[`AlignmentSpec, `AlignmentLexicographic, `MapSpec, `PairSpec, `PairSpecTier, `PairSpecU]

-- ──────────────────────────── alignment kernels ────────────────────────────

@[default_target]
lean_lib KernelsBand where   -- bandDoublingAlign (full equality with the spec)
  srcDir := "Aligner/kernels/band"
  roots := #[`AlignmentWavefront]

@[default_target]
lean_lib KernelsGapless where   -- gapless and one-indel alignments
  srcDir := "Aligner/kernels/gapless"
  roots := #[`MapperGapless, `MapperOneIndel]

@[default_target]
lean_lib KernelsGotoh where   -- gotohFusedAlign (full equality with the spec)
  srcDir := "Aligner/kernels/gotoh"
  roots := #[`AlignmentAlgorithms]

@[default_target]
lean_lib KernelsK250 where   -- word kernels on candidate windows (MapperK250*, FastGenK250)
  srcDir := "Aligner/kernels/k250"
  roots := #[`FastGenK250, `MapperK250, `MapperK250Bits, `MapperK250Chunk, `MapperK250Loops, `MapperK250Seed, `MapperK250Sel, `MapperK250Spec, `MapperK250Words]

@[default_target]
lean_lib KernelsMapperBand where   -- banded kernel for the mapper (MapperBand*, BandScore)
  srcDir := "Aligner/kernels/mapper_band"
  roots := #[`BandScore, `MapperBandBytes, `MapperBandFast, `MapperBandKernel, `MapperBandProof, `MapperBandPrune, `MapperBandSpec]

@[default_target]
lean_lib KernelsWfa where   -- wfaAlign: the proven wavefront (score + sound + total)
  srcDir := "Aligner/kernels/wfa"
  roots := #[`AlignmentExchange, `AlignmentWfa]

@[default_target]
lean_lib KernelsWfaFast where   -- wfaAlignI/F/L: executed paths proven = wfaAlign
  srcDir := "Aligner/kernels/wfa_fast"
  roots := #[`AlignmentWfaFast, `AlignmentWfaFused, `AlignmentWfaLazy, `AlignmentWfaLazyLevel]

@[default_target]
lean_lib KernelsWfaOffsets where   -- wfaAlignC / wfaAlignCA: offsets-only fronts + certified traceback
  srcDir := "Aligner/kernels/wfa_offsets"
  roots := #[`AlignmentWfaArray, `AlignmentWfaCertified, `AlignmentWfaDirect, `AlignmentWfaLcp, `AlignmentWfaOff, `AlignmentWfaOffLoop, `AlignmentWfaOffR, `AlignmentWfaPoint, `AlignmentWfaView]

@[default_target]
lean_lib KernelsWfaRuns where   -- wfaAlignK: direct run-length traceback with scalar checker
  srcDir := "Aligner/kernels/wfa_runs"
  roots := #[`AlignmentCigarCheck, `AlignmentCigarCheckFast, `AlignmentTraceRuns, `AlignmentWfaRuns, `AlignmentWfaRunsFast, `AlignmentWfaRunsVsWfa]

@[default_target]
lean_lib KernelsWfaSmallErrors where   -- wfaAlignH / wfaAlignHC: exact ≤2-substitution shortcut + compact output
  srcDir := "Aligner/kernels/wfa_small_errors"
  roots := #[`AlignmentCompact, `AlignmentSmallErrors]

@[default_target]
lean_lib KernelsWfaU32 where   -- proved UInt32 kernels U/U2/U3 (U3 is the one the tool runs)
  srcDir := "Aligner/kernels/wfa_u32"
  roots := #[`AlignmentWfaU32, `AlignmentWfaU32Ext, `AlignmentWfaU32Fill, `AlignmentWfaU32Fill3, `AlignmentWfaU32FillS, `AlignmentWfaU32FillSSpec, `AlignmentWfaU32FillSpec, `AlignmentWfaU32FillSpec3, `AlignmentWfaU32Kernel2, `AlignmentWfaU32Kernel3, `AlignmentWfaU32Lattice, `AlignmentWfaU32Level, `AlignmentWfaU32Level2, `AlignmentWfaU32Level3, `AlignmentWfaU32LevelS, `AlignmentWfaU32Loop, `AlignmentWfaU32Loop3, `AlignmentWfaU32Run2, `AlignmentWfaU32Run3, `AlignmentWfaU32Single, `AlignmentWfaU32Step, `ProbeU32, `WfaU3]

-- ──────────────────────────── index kernels ────────────────────────────

@[default_target]
lean_lib IndexCsr where   -- CSR index
  srcDir := "Aligner/index/csr"
  roots := #[`CsrIndex]

@[default_target]
lean_lib IndexKmer where   -- k-mer index
  srcDir := "Aligner/index/kmer"
  roots := #[`MapperFastIndex]

@[default_target]
lean_lib IndexMinimizer where   -- minimizer index (MzIndex) and its checkers
  srcDir := "Aligner/index/minimizer"
  roots := #[`MapperMzWords, `MzBuildOk, `MzCheckFast, `MzCheckPar, `MzIndex, `MzView, `MzWord]

@[default_target]
lean_lib IndexPackedGenome where   -- 2-bit packed genome
  srcDir := "Aligner/index/packed_genome"
  roots := #[`MapperPGen, `MapperPacked, `MzBuildP, `MzPacked, `WgPacked]

-- ──────────────────────────── mapper (main code) ────────────────────────────

@[default_target]
lean_lib Mapper where   -- tier router, pair search, batching: the code alignPairs runs
  srcDir := "Aligner/mapper"
  roots := #[`EarlyStopMapper, `FastGen, `FastGenAlgo, `FastGenCover, `FastGenCoverE, `FastGenCoverL, `FastGenMz, `FastGenPair, `FastGenPairPacked, `FastGenProof, `FastGenSupp, `FastGenWordFilt, `FastMapper, `FastMapperMz, `LowErrorMapper, `MateFloor, `PairBnB, `PairBox, `PairConcat, `PairConcatPacked, `PairDispatch, `PairExact, `PairGuarFast, `PairGuarQ, `PairGuarQB, `PairGuarQC, `PairGuarQD, `PairGuarQE, `PairGuarantee, `PairHits, `PairHitsKP, `PairHybrid, `PairInterleave, `PairJoin, `PairJoint, `PairLadder, `PairLadderF, `PairMapper, `PairNear, `PairPacked, `PairReason, `PairRegion, `PairRouter, `PairUnique, `ParMap, `ParStream, `ReadTrim, `SeedMapper, `SeedMapper2, `TieCut, `TierHeur, `TierOpt, `TierRouter, `BandCellsJProof]

@[default_target]
lean_lib MapperLemmas where   -- lemmas for the seed-and-index mapper
  srcDir := "Aligner/mapper/lemmas"
  roots := #[`MapperBytes, `MapperDefs, `MapperEvents, `MapperFastAlgo, `MapperFastBest, `MapperFastBytes, `MapperFastKernel, `MapperFastLazy, `MapperFastLoop, `MapperFastMerge, `MapperFastScore, `MapperFastSupport, `MapperGRead, `MapperGen16, `MapperGenBest, `MapperGenLook, `MapperGenScore, `MapperGenSearch, `MapperGenShare, `MapperInterleave, `MapperLists, `MapperSeedsAmong, `MapperWalk, `MapperWalk2]

-- ──────────────────────────── trimmer ───────────────────────────

@[default_target]
lean_lib Trimmer where
  srcDir := "Aligner/trimmer"
  roots := #[`ReadWindowTrimmer, `AdapterTrim]

-- ───────────────────────────── tool ─────────────────────────────

@[default_target]
lean_lib LeanAlign where
  srcDir := "Aligner"
  roots := #[`LeanAlign.Cli, `LeanAlign.Run]

@[default_target]
lean_exe «lean-align» where              -- the shim (Main.lean): build INDEX / map pairs to SAM, calling the proved alignPairs
  root := `Main


@[default_target]
lean_lib UniqueGenome where           -- unique-genome proofs: k-mers once ⇒ 150-windows far apart; proved k-mer checker
  srcDir := "Testing/unique"
  roots := #[`UniqueGenome]

lean_exe kmer_check where             -- runs the proved checker UniqueGenome.checkUnique on a FASTA (the IO is unproved)
  srcDir := "Testing/unique"
  root := `KmerCheck
