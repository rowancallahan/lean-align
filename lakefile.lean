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
  roots := #[`AlignmentSpec, `AlignmentLexicographic]

-- ──────────────────────────── codecs ────────────────────────────

@[default_target]
lean_lib CodecGotoh where            -- gotohFusedAlign (full equality with the spec)
  srcDir := "codecs/gotoh"
  roots := #[`AlignmentAlgorithms]

@[default_target]
lean_lib CodecBand where             -- bandDoublingAlign (full equality with the spec)
  srcDir := "codecs/band"
  roots := #[`AlignmentWavefront]

@[default_target]
lean_lib CodecWfa where              -- wfaAlign: the proven wavefront (score + sound + total)
  srcDir := "codecs/wfa"
  roots := #[`AlignmentExchange, `AlignmentWfa]

@[default_target]
lean_lib CodecWfaFast where          -- wfaAlignI/F/L: executed paths proven = wfaAlign
  srcDir := "codecs/wfa_fast"
  roots := #[`AlignmentWfaFused, `AlignmentWfaLazy, `AlignmentWfaLazyLevel, `AlignmentWfaFast]

@[default_target]
lean_lib CodecWfaOffsets where       -- wfaAlignC / wfaAlignCA: offsets-only fronts + certified traceback
  srcDir := "codecs/wfa_offsets"
  roots := #[`AlignmentWfaOff, `AlignmentWfaOffLoop, `AlignmentWfaOffR, `AlignmentWfaView,
             `AlignmentWfaPoint, `AlignmentWfaDirect, `AlignmentWfaLcp, `AlignmentWfaCertified,
             `AlignmentWfaArray]

@[default_target]
lean_lib CodecWfaSmallErrors where   -- wfaAlignH / wfaAlignHC: exact ≤2-substitution shortcut + compact output
  srcDir := "codecs/wfa_small_errors"
  roots := #[`AlignmentSmallErrors, `AlignmentCompact]

@[default_target]
lean_lib CodecWfaRuns where          -- wfaAlignK: direct run-length traceback with scalar checker
  srcDir := "codecs/wfa_runs"
  roots := #[`AlignmentCigarCheck, `AlignmentCigarCheckFast, `AlignmentTraceRuns, `AlignmentWfaRuns, `AlignmentWfaRunsFast, `AlignmentWfaRunsVsWfa]

@[default_target]
lean_lib CodecWfaU32 where           -- proved UInt32 kernels U/U2/U3 (U3 is the one the tool runs)
  srcDir := "codecs/wfa_u32"
  roots := #[`ProbeU32, `AlignmentWfaU32Level, `AlignmentWfaU32Step, `AlignmentWfaU32Loop, `AlignmentWfaU32, `AlignmentWfaU32Fill, `AlignmentWfaU32Run2, `AlignmentWfaU32Ext, `AlignmentWfaU32FillSpec, `AlignmentWfaU32Single, `AlignmentWfaU32Level2, `AlignmentWfaU32Lattice, `AlignmentWfaU32Kernel2, `AlignmentWfaU32FillS, `AlignmentWfaU32FillSSpec, `AlignmentWfaU32LevelS, `AlignmentWfaU32Fill3, `AlignmentWfaU32Run3, `AlignmentWfaU32FillSpec3, `AlignmentWfaU32Loop3, `AlignmentWfaU32Level3, `AlignmentWfaU32Kernel3]

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
