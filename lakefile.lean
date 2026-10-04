import Lake

open Lake DSL

/-!
lean-align: proved pairwise alignment, compiled to one command-line tool.

  Main.lean            every file-system call the tool makes (trusted, short)
  LeanAlign/           pure code: command line (Cli) and bytes-in → bytes-out (Run)
  spec/                frozen alignment specification, and theorems about Cli and Run
  codecs/<kernel>/    alignment codecs, each proved against spec/AlignmentSpec.lean
  trimmer/             read-window trimmer (frozen contract + proved implementations)
  checks/, scripts/    executable cross-checks and the full re-check script

Module names are unchanged from the read_window_trimmer repository.
-/

package lean_align where
  version := v!"0.1.0"

-- ───────────────────────────── spec ─────────────────────────────

@[default_target]
lean_lib AlignmentSpecLib where
  srcDir := "spec"
  roots := #[`AlignmentSpec, `AlignmentLexicographic, `MapSpec, `PairSpec]

-- ──────────────────────────── codecs ────────────────────────────

@[default_target]
lean_lib PoolGotoh where            -- gotohFusedAlign (full equality with the spec)
  srcDir := "pool/gotoh"
  roots := #[`AlignmentAlgorithms]

@[default_target]
lean_lib PoolBand where             -- bandDoublingAlign (full equality with the spec)
  srcDir := "pool/band"
  roots := #[`AlignmentWavefront]

@[default_target]
lean_lib PoolWfa where              -- wfaAlign: the proven wavefront (score + sound + total)
  srcDir := "pool/wfa"
  roots := #[`AlignmentExchange, `AlignmentWfa]

@[default_target]
lean_lib PoolWfaFast where          -- wfaAlignI/F/L: executed paths proven = wfaAlign
  srcDir := "pool/wfa_fast"
  roots := #[`AlignmentWfaFused, `AlignmentWfaLazy, `AlignmentWfaLazyLevel, `AlignmentWfaFast]

@[default_target]
lean_lib PoolWfaOffsets where       -- wfaAlignC / wfaAlignCA: offsets-only fronts + certified traceback
  srcDir := "pool/wfa_offsets"
  roots := #[`AlignmentWfaOff, `AlignmentWfaOffLoop, `AlignmentWfaOffR, `AlignmentWfaView,
             `AlignmentWfaPoint, `AlignmentWfaDirect, `AlignmentWfaLcp, `AlignmentWfaCertified,
             `AlignmentWfaArray]

@[default_target]
lean_lib PoolWfaSmallErrors where   -- wfaAlignH / wfaAlignHC: exact ≤2-substitution shortcut + compact output
  srcDir := "pool/wfa_small_errors"
  roots := #[`AlignmentSmallErrors, `AlignmentCompact]

@[default_target]
lean_lib PoolWfaRuns where          -- wfaAlignK: direct run-length traceback with scalar checker
  srcDir := "pool/wfa_runs"
  roots := #[`AlignmentCigarCheck, `AlignmentCigarCheckFast, `AlignmentTraceRuns, `AlignmentWfaRuns, `AlignmentWfaRunsFast, `AlignmentWfaRunsVsWfa]

@[default_target]
lean_lib PoolWfaU32 where           -- proved UInt32 kernels U/U2/U3 (U3 is the one the tool runs)
  srcDir := "pool/wfa_u32"
  roots := #[`ProbeU32, `AlignmentWfaU32Level, `AlignmentWfaU32Step, `AlignmentWfaU32Loop, `AlignmentWfaU32, `AlignmentWfaU32Fill, `AlignmentWfaU32Run2, `AlignmentWfaU32Ext, `AlignmentWfaU32FillSpec, `AlignmentWfaU32Single, `AlignmentWfaU32Level2, `AlignmentWfaU32Lattice, `AlignmentWfaU32Kernel2, `AlignmentWfaU32FillS, `AlignmentWfaU32FillSSpec, `AlignmentWfaU32LevelS, `AlignmentWfaU32Fill3, `AlignmentWfaU32Run3, `AlignmentWfaU32FillSpec3, `AlignmentWfaU32Loop3, `AlignmentWfaU32Level3, `AlignmentWfaU32Kernel3]

@[default_target]
lean_lib PoolMapper where             -- lemmas for the seed-and-index mapper
  srcDir := "pool/mapper"
  roots := #[`MapperDefs, `MapperWalk, `MapperLists, `MapperWalk2, `MapperBandSpec, `MapperBandKernel, `MapperBandProof, `MapperBandFast, `MapperBytes, `MapperGapless, `MapperOneIndel, `MapperSeedsAmong, `MapperFastAlgo, `MapperFastScore, `MapperFastBytes, `MapperFastKernel, `MapperFastIndex, `MapperFastMerge, `MapperFastBest, `MapperFastSupport, `MapperFastLoop, `MapperFastLazy, `MapperGenBest, `MapperGenScore, `MapperMzWords, `MapperSketch, `MapperPacked, `MapperGenLook, `MapperInterleave, `MapperGenSearch, `MapperGen16, `MapperPGen]

@[default_target]
lean_lib Codecs where                 -- one file per codec: algorithm + theorem against the spec
  srcDir := "codecs"
  roots := #[`WfaU3, `SeedMapper, `SeedMapper2, `BandScore, `CsrIndex, `ParMap, `ParStream, `LowErrorMapper, `EarlyStopMapper, `PreFilterMapper, `RepeatMask, `ParGroup, `PairMapper, `PairJoint, `FastMapper, `FastMapperPar, `FastMapperMz, `FastGenCover, `MzCheckFast, `MzIndex, `SketchMapper, `FastGenAlgo, `FastGenProof, `FastGen, `PairInterleave, `MzCheckPar, `FastGenMz, `PairConcat, `FastGenPair, `MzPacked, `PairPacked, `PairConcatPacked]

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

lean_exe gen_pair_bench where         -- proved general-path pair mapper (pairFastGB) over a concatenated index (unproved IO)
  srcDir := "bench"
  root := `GenPairBench

lean_exe pair_bench where             -- proved pair mapper (pairFast) on mate files (unproved IO)
  srcDir := "bench"
  root := `PairBench

lean_exe packed_bench where           -- 2-bit packed mismatch count vs byte loop (unproved IO)
  srcDir := "bench"
  root := `PackedBench
