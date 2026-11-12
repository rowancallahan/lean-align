# spec/fastq-bytes: Rowan's FASTQ spec, the proved byte parser, the byte pipeline

Base: festive dd2f3cb. Rowan approved changing Spec/Fastq, Spec/Sam, Spec/Shim, Main and their proofs/mirrors.

## What changed

| file | now |
|---|---|
| `Spec/Fastq.lean` | exactly `Testing/notes/byte_specs/FastqSpec.lean`, with only the namespace changed (`FQ` → `Spec.FQ`). It has `Record`, `Read`, `Record.valid`, `toBytes`, `toRead`, `parse := sorry`, and `parse_correct` (proof `sorry`). Nothing else: no reader, no trimming, no pairing. |
| `Proofs/Fastq.lean` | The Spec text, then the holes filled. Details below the table. |
| `Aligner/io/FastqIO.lean` (new lib `FastqIO`) | The shim's FASTQ bytes. Details below the table. |
| `Spec/Sam.lean` (= `Proofs/Sam.lean`) | Everything between reads and SAM bytes. Details below the table. |
| `Proofs/TrimRecord.lean` | Trimming theorems restated where the type changed, plus the QNAME rule on bytes. Details below the table. |
| `Spec/Shim.lean` (= `Main.lean`) | The byte pipeline. Details below the table. |
| `Spec/Fasta.lean`, `Proofs/Fasta.lean` | Only the import changes: `FastqReader` moved from Spec/Fastq to FastqIO. |
| CI | Mirror rule, forbidden-token list and headline list updated. Details below the table. |
| `Testing/scripts/fuzz_reads.py` | The long-read case is capped at 1000 bases (the spec's limit; before, a 1000-base read could grow past it from an insertion). |

**`Proofs/Fastq.lean`: the holes filled.**
- `parse` is a readable state machine:
  - `Field` and `Field.next`;
  - `Parse {field, current, done}`;
  - `step`, a single `match b == newline, p.field`;
  - `emptyParse`.
  - `parse` is the fold over the bytes, then a check that the input ends between records, then a check that every record is valid.
- `parse_correct` is proved, along with:
  - `parse_of_records`: any valid decomposition is the one `parse` finds;
  - `toBytes_unique`;
  - `parse_cons`.
- `parseFastqB_eq`: the shim's byte parser is `parse`. It fails exactly when `parse` does, and otherwise returns the same reads.
- `@[csimp] parse_eq`: `parse` runs as the byte parser.

**`Aligner/io/FastqIO.lean`: the shim's FASTQ bytes.**
- `FastqReader`, for the FASTA reader.
- `findNewline` and `allBytes`: structural loops, each with a `uget` version under `@[csimp]`.
- `ReadB {name, seq, qual : ByteArray}`.
- `recordError`: `Record.valid` on the four lines, with a reason string.
- `parseFrom` / `parseFastqB`: well-founded recursion, no `while`.

**`Spec/Sam.lean`: everything between reads and SAM bytes.**
- `ReadB.toRead`.
- The QNAME rule: `qnameOf` on `List UInt8` (up to the first space, then drop a trailing /1 or /2) and `qnameOk` (1..254 bytes, in `!`..`?` or `A`..`~`), with byte versions `qnameB` and `qnameOkB`.
- Trimming over reads: `trimBytes` (moved from Proofs/TrimRecord), `trimRead : FQ.Read → FQ.Read`, `trimReadB`, `trimChunk`, `chunkPairs`.
- The SAM writer as bytes over `ReadB`: `samSequence`, `samLine`, `mappedLine`, `unmappedLine`, `samLines`, `samChunk`. Each appends to a `ByteArray`, with `pushNat`/`pushInt` for numbers. This is the `samChunkB` of research/io2.
- `reverseMapBytes` with a `uget` version (`@[csimp]`).

**`Proofs/TrimRecord.lean`.**
- Kept unchanged: `trimBytes_window`, `trimBytes_acgt`, `trimBytes_size`, `cutAt_spec`.
- Restated on `FQ.Read`: `trimRead_correct` (was `trimRecord_correct`), `trimRead_quality_bytes` (was `trimRecord_quality_bytes`), and `parse_trim_quality` (was `parseRecord_trim_quality`).
  - `parse_trim_quality` now reads: every trimmed quality byte of a read that `FQ.parse` returned is in '!'..'~'. Its UTF-8 content is gone, because quality is bytes now.
- New: `trimReadB_toRead`, and `trimChunk_eq` (now over `ReadB`).
- The QNAME rule on bytes: `qnameB_eq`, `qnameOkB_eq`, `qnameB_toRead`.

**`Spec/Shim.lean` (= `Main.lean`): the byte pipeline.**
- Two readers cut slices at every 4·16000th newline.
- A dispatcher builds the jobs.
- 4 workers each run `parseFastqB` on both slices, then `pairUp` (same count, same `qnameB`, `qnameOkB`), `trimChunk`, `alignPairs` and `samChunk`.
- An ordered writer writes the jobs in order.
- Errors are deterministic: the writer reports the first failed job in order, after writing every job before it.

**CI.**
- Fastq mirror rule "up to the holes" (`Testing/scripts/fastq_mirror.py`): Proofs/Fastq.lean must be its imports, then the Spec lines before `def parse` unchanged, then `def parse` with the same signature, then `parse_correct` stated word for word.
- `Spec/Fastq.lean` leaves the no-sorry shim list, since it has holes now; `Aligner/io/FastqIO.lean` joins it.
- Headline list: `trimRead_*`, `parse_trim_quality`, `trimReadB_toRead`, `FQ.parse_correct`, `FQ.parseFastqB_eq`, `qnameB_eq`, `qnameOkB_eq`.

## Checks

- `lake build`: OK (all Proofs; standard axioms only).
- `FUZZ=1 Testing/scripts/CI_check.sh`: everything passes except `Spec/FROZEN.sha256` for `Spec/Shim.lean`, which must be regenerated now that the shim has changed. My attempt to regenerate it was denied, so Rowan has to do it. Output fuzz: 2917 pairs, VIOLATIONS: none.
- SAM byte-identical to festive (dd2f3cb code = e7ecb81):
  - novaseq_200k: 669b42f69137 (identical, `cmp`).
  - hg002_200k: 17656d95172c (identical, `cmp`).
  - CI fuzz inputs (2917 pairs): ca67078a1113 (identical).
  - 5M FIFO (zcat), whole-run wall time including index load:

    | set | festive | this branch | md5 (both) |
    |---|---|---|---|
    | nova5M | 179.6 s | 131.2 s | 025f8576cd71 |
    | hg002_5M | 198.7 s | 137.1 s | 606e5fea16a6 |
- Wall time at 200k (4 cores, warm cache): hg002 7.5 s against festive's 8.5 s; nova 6.7 s (festive's run was cold, 189 s).

## Behaviour that differs from festive (all follow from Rowan's `Record.valid` / `toBytes`)

Edge-case differential, 61 cases (local, not committed):
- **Rejected now, accepted by festive:**
  - CRLF files ('\r' is not allowed in a name, sequence or quality);
  - no final newline;
  - reads with more than 1000 bases (10001 and 12000 tested);
  - names shorter than 10 bytes including '@' (e.g. "@rd9/1");
  - a '+' line naming a different read.
- **Accepted now, rejected by festive:** header bytes that are ASCII but not printable, in the comment after the first space. A tab inside the QNAME is still rejected, as "not a SAM QNAME".
- **Same exit code, different message:** truncated record, empty lines, missing '+', no '@', lowercase, IUPAC, length mismatch, quality outside '!'..'~', mates out of step, one file longer. Messages now carry the record's byte offset in its slice.
- **Partial SAM before a late error:** the SAM written before the error is cut at job size (16000 pairs) rather than festive's chunk size (20000). Example: a bad record r20000 of 32000 writes 32000 SAM lines instead of 40000. The error reported is now deterministic: the first in file order.

## Not done

- **Variant B (per-worker prepared index):** not included. The shim can only call Spec functions, and Spec has no `alignPairsP (chunkSetup index) = alignPairs index` interface yet; in the earlier patch it was a Main-only exception to the mirror rule.
- **`Testing/benches/*`:** these still use the old `FastqRecord` and are not built by default. They need updating, or removal, before they are next built.
- **Slicing (trusted, stated in Shim):** the claim that cutting at every 4k-th newline and parsing the slices equals `parse` on the whole file is not proved. `parse_cons` / `toBytes_unique` are the lemmas for it.

## Trimming: best window and validity on `FQ.Read` (S-H)

New in `Proofs/TrimRecord.lean` (standard axioms; in the CI headline list):
- `trimRead_best`: for a read of at most 10 000 letters whose part before the TruSeq cut (`preCut`) has an A/C/G/T
  letter, `trimRead r = keepWindow r (get_best_window [] (scoresOf (preCut r)) (map (perBase defQ)))`: the kept window
  is exactly the frozen contract's best window of the cut read (from `ReadTrim.trimRead_def_eq_contract`), or nothing
  when there is none or it is shorter than `minLength`. When Rowan's TruSeq cut spec lands, `preCut` is the place to
  state it.
- `trimRead_best_none`: when nothing before the cut is A/C/G/T (all N, or the cut leaves nothing), `trimRead` keeps
  nothing and so does the contract: every base scores −1 000 000, so by `get_best_window_returns_a_maximum_score` its best
  window is one base, shorter than `minLength`. `trimRead_contract` joins the two: `trimRead r = keepWindow r (contract)`
  for every read of at most 10 000 letters (the spec's reads have at most 1000).
- `trimRead_valid`: `r.valid → ∃ r', r'.valid ∧ toRead r' = trimRead (toRead r)` (same name and `+` line; letters
  A C G T N, ≤ 1000; quality bytes; equal lengths). `parse_trim_valid`: the same for every read `FQ.parse` returns.
  `parse_trim_quality` (qualities only) is the quality part of it.
- Compared with what was already here: `trimRead_correct` (window, cut bound, ACGT, empty or ≥ `minLength`) and
  `trimChunk_eq` (on `ReadB`, with `trimReadB_toRead`) already cover the window/chunk statements of the earlier
  `TrimBytes` draft (branch spec/fastq-bytes-trim), so that module is not needed.

Cost of List ↔ ByteArray (callgrind, 2k pairs): the shim never converts (`parseFastqB` → `ReadB` → `trimReadB` on
`ByteArray`s; `toRead` is only in proofs). A variant that trims through `FQ.Read` (`ReadB → toRead → trimRead → back`)
gives identical SAM but costs NovaSeq 935.5M → 1,315.2M Ir (+41%) and HiSeq 1,099.1M → 1,672.6M Ir (+52%):
~95k-145k Ir per mate, mostly `List.toArrayAux`, `Array.toList`, allocation and freeing of one cons cell per byte.
So `List UInt8` stays in the statements and the executed code stays on `ByteArray`, as it is.
