# Paired / unpaired input, and trimming: what the code does today

Read from the code at 5c309c3 (`Spec/Shim.lean`, `Spec/Aligner.lean`, `Spec/Sam.lean`, `Proofs/Aligner.lean`,
`Aligner/mapper/ReadTrim.lean`, `Testing/benches/WholeGenome.lean`). Nothing here was run; no file in `Spec/` is
changed. Sections 3-5 are proposals for Rowan to accept or reject.

## 1. Current behaviour

**Input is two FASTQ files, always.** `map INDEX R1.fq R2.fq OUT.sam MIN MAX` opens both; `Spec.readChunk` reads
one record from each in step and stops at the first file that runs out (the longer file is silently truncated;
names are never compared, so mate order is trusted). There is no single-end mode, no interleaved mode, no gzip,
no orphan file.

**`alignPairs` already has a "mate missing" slot.** It takes `Option ByteArray × Option ByteArray`; `none` means
the mate was trimmed away. `alignOne` returns `.trimmedAway .one` if mate 1 is `none` (also when both are), else
`.trimmedAway .two` if mate 2 is `none`. The surviving mate is never aligned on its own.
`PairResult.Correct` says only `trimmed1 = none` (resp. `trimmed2 = none`).
`samLines` prints both records unmapped (flags 77 / 141) with the tag `XT:Z:trimmedAway1` or `…2` (the same tag
name that carries the tier for aligned pairs).

**The shim trims nothing.** `Spec.chunkPairs` wraps every mate in `some` ("Stand-ins: no trimming"), so
`.trimmedAway` is never produced by `lean-align map`. SEQ/QUAL in the SAM are the original record's.

**A proved trimmer exists but is only wired into the bench.** `ReadTrim.trimReadQ Q seq qual : Option (Nat × Nat)`
keeps the best-scoring window: per base `qual − 33 − Q` for A/C/G/T, −1 000 000 for anything else, `Q ≤ 93`
(`defQ` is the default; the bench overrides it with `WG_TRIMQ`). It returns `none` for a read with no A/C/G/T or
longer than 10 000 letters. Proved: `trimRead_eq_contract` (equals the frozen window contract) and `trimRead_acgt`
(kept window is A/C/G/T only). The bench (`WholeGenome.lean`, the FASTQ branch of the mate loader) trims both
mates; a pair with a `none` mate is dropped before routing (reason `trimmedAway`). The trimmer is not part of
any theorem: `alignPairs_correct` is stated about *already-trimmed* mates (`PAIRED_MAPPING_CORRECTNESS_GOAL.md`).

Consequences:

- With trimming on in the shim, `samLines` would print the **original** SEQ/QUAL while placement and CIGAR describe
  the **trimmed** window, so CIGAR length ≠ SEQ length. Either print the trimmed bytes or add `S` operations for
  `[0,s)` and `[e,n)`.
- The router has its own length thresholds (`cap1` at 150 / 100 / 75). The spec has no notion of "too short": such
  a pair comes back `.aligned` with `found := none`.

## 2. What trimmers usually do (for contrast)

| Situation | Typical output |
|---|---|
| Both mates survive | `R1.fq`, `R2.fq`, kept in step |
| One mate dropped (too short, low quality) | Trimmomatic: paired `1P/2P` plus unpaired `1U/2U`; fastp: `--unpaired1/2`; cutadapt: `--pair-filter=any/both` decides whether the pair is dropped; trim_galore: `--retain_unpaired` |
| Single-end data | a separate mode with no mate 2 |
| Pre-trimmed reads | a "no trimming" flag, or the aligner runs on the trimmer's output files |

The aligner then maps an orphan as a single-end read (flag 0/16, or 4 if unmapped, no 0x1 bit). lean-align today
discards the pair instead.

## 3. Proposal: single-end and orphan output

In `Spec/` terms:

1. **Result type.** Add `| orphan (mate : Mate) (answer : MateAnswer)` to `PairResult`, with
   `MateAnswer = {found : Option MateReport, bestPossibleScore : Int, uniqueness : Uniqueness, tier : Tier}`.
   Its `Correct` is the single-read analogue of `PairAnswer.Correct`: a reported placement is a real
   `GenomicAlignment` printed exactly; the bound holds for every placement; `unique` means every other placement
   scores strictly lower. `trimmedAway` stays for "both gone" (and the case where orphans are not wanted).
2. **Single-end entry point.** `alignReads (reads : List (Option ByteArray)) : List ReadResult`, same
   one-result-per-input statement. `InsertSettings` does not apply.
3. **Shim.** `map INDEX --single READS.fq OUT.sam` next to the paired form. For a pair with one dropped mate: the
   aligned orphan gets flag 0/16 (or 73/89-style paired flags with 0x8 set if the pair stays a pair in the SAM; pick
   one convention), the dropped mate gets either no record or an unmapped record tagged `XT:Z:trimmedAway`
   (today both mates of the pair get a record).
4. **Router.** The `eachMateUnique` tier already searches a single mate, so a per-mate answer is a smaller version
   of existing work; no proper-pair logic is needed.

## 4. Proposal: trimming on/off

Trimming must be skippable (pre-trimmed reads, speed) and stay outside the proved call:

- **Switch in the shim only.** `map … [--trim Q | --no-trim]`, default `--no-trim` (today's behaviour).
  `chunkPairs (trim : Option Nat) chunk` maps each record through `ReadTrim.trimReadQ Q letters quality` to
  `some (letters.extract s e)` or `none`. With `--no-trim` the quality bytes are not read in this step and there
  is no per-read cost.
- **Output.** `samChunk` must receive `(s, e)` per mate to print the trimmed SEQ/QUAL or soft clips (§1). That is a
  `Sam.lean` change (trusted code), not a change to `Spec/Aligner.lean`.
- **Proof coverage.** To extend the theorem to "raw FASTQ in → SAM out" add a separate theorem
  (`trim_then_align_correct`) with `trimmedPairs = rawPairs.map trimPair`, where `trimPair` follows
  `ReadWindowTrimmer/Contract.lean`; `trimRead_eq_contract` is the existing bridge. The two frozen theorems stay.
- **Pre-trimmed input.** `--no-trim` is already covered: `alignPairs_correct` quantifies over the mates as given.
  The end-to-end theorem needs A/C/G/T/N only (`MatesAreDNA`), so other letters should fail loudly at read time
  (assert) instead of being passed through.
- **Adapters.** `ReadTrim` is quality/N window trimming only. Adapter removal is a different function
  (SESSION_SUMMARY treats cutadapt as a separate pre-step).

## 5. What the FASTQ and BAM specs need

**FASTQ** (replaces the unproved `Spec/Fastq.lean`):
- Record = `@name`, sequence, `+` line (optionally repeating the name), quality; sequence and quality lengths
  equal. Today `readFastqRecord` ignores the `+` line and does not compare lengths.
- Alphabet: sequence over `A C G T N`; quality bytes 33…126 (Phred+33).
- Pairing: the two files have the same number of records and names agree after dropping `/1`, `/2` (as `samName`
  does). Today a mismatch is truncated or mispaired silently.
- Single-end and interleaved as separate formats; compressed input only after decompression is specified.
- Line endings `\n` and `\r\n`; a missing final newline accepted.
- Statements: `parse (print records) = records`, and `parse` succeeds only on well-formed input.

**BAM writer** (SAM text today is `Spec/Sam.lean`, also unproved):
- `encodeBam : SamRecord → ByteArray` with the binary layout: `block_size`, refID, pos (0-based), `l_read_name`, mapq,
  bin (UCSC binning of `[pos,end)`), `n_cigar_op`, flag, `l_seq`, next refID/pos, tlen, NUL-terminated name, CIGAR
  as `len<<4|op` (`M I D S` = 0 1 2 4), 4-bit sequence (`=ACMGRSVTWYHKDBN`), raw Phred qualities (no +33), typed tags.
- Header: magic `BAM\1`, header text (can reuse `samHeader`), `n_ref` with names and lengths.
- BGZF (deflate blocks ≤ 64 KiB plus the EOF block) is a separate layer; `LEANZIP_SPEC_MAP.md` is the existing note
  on proved compression.
- Statements: `decodeBam (encodeBam records) = records`, and the SAM and BAM of one run agree field by field.
- Tags: `AS:i`, `XB:i`, `XU:Z`, `XT:Z` need explicit BAM types (smallest fitting integer type for `i`, NUL-terminated
  `Z`). The shim emits `SO:unsorted`; a sorted BAM needs a sort-order statement and a `.bai` spec.
- MAPQ is a stand-in today (60 if `unique`, else 0); finalise its definition before specifying it in BAM.
