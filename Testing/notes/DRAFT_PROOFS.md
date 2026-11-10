# Proofs for the locked drafts (Spec/Draft/Trim.lean, Spec/Draft/Sam.lean)

Branch trim/spec-proofs (off festive e4b8a72). Standard axioms only; no Spec text changed. CI: mirror checks
(`draft_mirror.py` for Trim, `cmp` after renaming imports for Sam), `Proofs/Draft/*.lean` in the forbidden-token check,
the theorems below in the headline list.

## Trimming
- `Proofs/Draft/TrimCore.lean`: `winTrim minLen letters qual` = `ReadTrim.trimRead` (fast `@[csimp]` loops) then
  `dropShort`. `winTrim_contract`: for ≤ 10 000 letters it is `keepB` of the frozen `get_best_window`
  (no A/C/G/T: the contract's best window is one base, by `get_best_window_returns_a_maximum_score`).
- `Proofs/Draft/Trim.lean` (mirror): `trim` = `winTrim minLength` on the read's bytes (reads > 10 000 letters: the
  contract directly; never reached from valid FASTQ, ≤ 1000). `trim_correct` proved: `window_score` of the contract's
  scores is the spec's `windowScore` (`window_score_eq`, needs equal lengths), so the contract's window is a best one.
- `Proofs/Draft/TrimFast.lean`: `cut_eq` (`Spec.Trim.cut` = `AdapterTrim.cutTruSeq`: the spec's `adapterAt` is
  `matchesAt truSeq 6 1` at every position, and `find?` over the positions is `cutPos`), `@[csimp] cut_eq_cutF`,
  `trim_cut_eq` (`trim (cut r) = Spec.trimRead r`, ≤ 10 000 letters), `trimReadB_cut_trim`
  (`(trimReadB rb).toRead = trim (cut rb.toRead)`): the shim keeps running `trimReadB` / `trimChunk` on `ReadB`.

## SAM
- `Proofs/Draft/Sam.lean`: `Spec/Draft/Sam.lean` with the imports renamed to the Proofs copies.
- `Proofs/Draft/SamFast.lean`: `samLinesS` / `samChunkS` / `samHeaderB` = the shim's byte writer (`Spec.samLines`,
  `samChunk`, the header lines) with two changes: no XT tier tag (the spec has none), and TLEN as the spec computes it
  (`max stop − min start` as a `Nat`; `Spec.mappedLine` uses `Int` subtraction for the leftmost mate, the same whenever
  `max stop ≥ min start`, which real placements satisfy but `Placement` does not require).
  Proved: `samHeaderB_eq` (header bytes = `SamSpec.header`), `samChunkS_eq` (chunk bytes = `SamSpec.body` of its pairs,
  `ReadB.toRead`), `samFileS_eq` (header then the chunks in order = `SamSpec.samFile`, one result per pair per chunk).
  Per line: `bl_samLine` (fields joined by tabs), `bl_unmappedLine`, `bl_mappedLine`, `bl_samLines`; numbers via
  `pushNat_eq` / `pushInt_eq` (from research/io2), QNAME via `qnameB_eq` + `qnameOf_eq`, SEQ/QUAL via `bl_reverseMap`.
- Using it in the shim drops the XT tier tag from the output (so the SAM changes by that tag); not done here.
