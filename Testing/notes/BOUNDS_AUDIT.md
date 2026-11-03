# Bounds-check audit: per-byte loops in FASTQ parsing, trimming, SAM writing

Base: festive e7ecb81 (`claude/festive-fermi-mf9mo6`). Branch `exp/bounds`.

How the numbers were measured:
- **Ir:** callgrind, 4000 pairs, `heavy.idx`. hg002 has 250 bp reads (festive total 2583M Ir); NovaSeq 200k has 151 bp reads (2261M). "Self" means the function's own instructions; "incl" includes everything it calls.
- **Wall:** 1M-pair plain files, 5 interleaved reps, medians. Map wall and user+sys exclude index load (`timed_load.py`).
- **SAM:** md5 identical to festive in every run (30 wall runs, 8 callgrind runs).

## 1. Loop list (festive)

Access kinds:
- **checked:** `a[i]!`, a Nat index, plus an `outOfBounds` branch on every read.
- **rtGet:** one machine-word compare plus `uget`, with a dead Nat fallback.
- **uget:** proof-carrying, no test.
- **String:** UTF-8 String operations.

| loop | file | access | hg002 self Ir | nova self Ir |
|---|---|---|---|---|
| `reverseMapBytes` (Range forIn, push) | Spec/Sam | checked | 104.1M (4.0%); incl 216M (8.4%) | 66.0M (2.9%) |
| `allBytesGo` ×3 in `parseRecord` (header, letters, quality) | Spec/Fastq | checked | 106.0M (4.1%) | 70.0M (3.1%) |
| `findNewline` (`while`, opaque `Loop`) | Spec/Fastq | checked | 67.0M (2.6%) | 44.5M (2.0%) |
| `FastqReader.line` CR test `buffer[newline-1]!` | Spec/Fastq | checked, once per line | ~0 | ~0 |
| `parseRecord` `header[0]!`, `plus[0]!` | Spec/Fastq | checked, once per record | ~0 | ~0 |
| `String.fromUTF8!` (name, quality) in `parseRecord`; letters/qualities in `samSequence`; qualities in `trimRecord` | Spec/Fastq, Spec/Sam | String (validation) | validate_utf8 127M (4.9%), utf8_strlen 66M (2.6%) | 84M, 49M |
| `mateName` / `samName` (`splitOn " "`) | Spec/Fastq, Spec/Sam | String | incl 98M + 49M (5.7%) | incl 117M + 58M (7.7%) |
| `readChunk` QNAME test `name.all` | Spec/Fastq | String | 24.2M (0.9%) | 24.1M (1.1%) |
| `ReadTrim.wlR` (quality window) | Aligner/mapper/ReadTrim | rtGet, 2 arrays | 72.0M (2.8%) | 43.7M (1.9%) |
| `AdapterTrim.saLoopTS` (TruSeq bit-parallel) | Aligner/trimmer/AdapterTrim | rtGet | 64.0M (2.5%) | 38.9M (1.7%) |
| `AdapterTrim.scanTS` (tail) | AdapterTrim | no array read | 4.2M | 4.3M |
| `trimReadQ` `seq[s]!`; first `rtGet` of `wlF` | ReadTrim | checked / rtGet, once per read | ~0 | ~0 |
| `cutPosW` / `wlU2` / `wlI` fallbacks | trimmers | rtGet / checked | 0 (only taken for reads ≥ 2^30 or past 10000 bp) | 0 |

Byte-pipeline code (`Testing/notes/byte_pipeline.patch`, la_bp4, a4d9f6f base, hg002 4000 pairs, total 2194M Ir):

| loop | access | self Ir |
|---|---|---|
| `spaceAt` (QNAME end), structural | checked `h[i]!` | below 0.1% (not in profile top) |
| `qnameOk` (`q.data.all`) | Array.all: USize loop, uget | below 0.1% |
| `lineAt` / `findNewlineU` (shim_speed) | uget; `findNewline` wrapper 46.0M (2.1%) | |
| `parseFrom` (structural, 4 lines per record) | calls `parseRecord` | `allBytesGo` 96.3M (4.4%) |
| `samChunkB` / `samSequenceB` | `reverseMapBytes`, checked | 91.7M (4.2%), plus push 33.7M |
| `pushNat` / `pushInt` | no array read | small |
| `mateName` (skipWhile) | String | 23.3M (1.1%) |

## 2. Outside Spec: committed on this branch

Both functions now take the bound as an erased proof argument and read by `uget`, with no compare in the loop. The generated C has 0 `outOfBounds`, `fget` or `sarray_size` calls.

- **`ReadTrim.wlRc`.** Same as `wlR`, with `hb : i ≤ seq.size ∧ i ≤ qual.size` as an extra argument.
  - `wlRc_eq` proves `wlRc … hb = wlR …` for all arguments.
  - `wlF` calls `wlRc` when `hb` holds; otherwise it calls `wlR` as before.
  - `wl_eq_wlF` (`@[csimp]`, unchanged statement) is re-proved.
- **`AdapterTrim.saLoopTSc`.** Same as `saLoopTS`, with `hn : nU.toNat ≤ read.size` as an extra argument.
  - `saLoopTSc_eq` proves `saLoopTSc … hn = saLoopTS …`.
  - `cutPosTS` calls it, and `cutPosTS_eq` is re-proved.
  - `cutTruSeq_eqF` (`@[csimp]`) is unchanged.
- **New lemma `ReadTrim.rtGet_of`:** `rtGet B p = B.uget p h` when `p < B.size`.
- **No theorem statement changed.** `FROZEN_CONTRACT.sha256` (`ReadWindowTrimmer/Contract.lean`) is untouched.

Gain, hg002 Ir: `wlR` 72.0M → 54.2M (−25%), `saLoopTS` 64.0M → 53.9M (−16%). Total −26.2M (−1.0%); nova −15.6M (−0.7%).
Native time is within noise; see §4.

## 3. Spec: `Testing/notes/bounds_spec.patch` (for Rowan, NOT applied)

The patch touches Spec/Fastq.lean and Spec/Sam.lean, plus the Proofs/ mirrors (kept byte-identical; CI checks this).

1. **`findNewline`.** The definition changes, because the `while` form is an opaque `Loop` and nothing can be proved about it.
   - New definition: `findNewline bytes i := findNewlineGo bytes (bytes.size - i) i`, where `findNewlineGo` is structural on fuel.
   - Fast version `findNewlineU`: uget, with `hs : size < 2^32` and `hj : j ≤ size`.
   - `findNewlineU_eq`, and `@[csimp] findNewline_eq : findNewline = findNewlineF`.
   - No theorem used the old `findNewline`.
   - Same results: the old loop stops at the first 10 byte or at `size`, and so does `findNewlineGo` with fuel `size - i`.
2. **`allBytes`.** `allBytesF` now calls `allBytesU` (uget, `@[specialize]`); `allBytesGo` remains the fallback for size ≥ 2^32.
   - `allBytesU_eq : allBytesU p b i h = allBytesGo p b i.toNat`.
   - The statement of `@[csimp] allBytes_eq : allBytes = allBytesF` is unchanged and is re-proved.
   - `allBytesGo` and `allBytesGo_eq` are kept.
3. **`reverseMapBytes`.** New `revMapU` (uget, last byte first).
   - `revMapU_eq` is equality with the `List.range'` fold that `simp` makes of the `for` loop.
   - `@[csimp] reverseMapBytes_eq : reverseMapBytes = reverseMapBytesF`.
4. **`parseRecord`.** It no longer re-validates the quality as UTF-8, because `allBytes (33..126) quality` was just checked.
   - New `parseRecordF`: `String.fromUTF8 quality (validUTF8_of_allBytes …)` in place of `fromUTF8!`.
   - New lemmas: `validUTF8_of_allBytes` (all bytes < 128 implies `IsValidUTF8`) and `utf8Encode_ascii`, the latter taken from research/io2 SamBytes.
   - `@[csimp] parseRecord_eq`.
   - The name keeps `fromUTF8!`. It is short, and its proof needs an `extract` lemma.

Gain (4000 pairs, Ir; hg002, then nova):

| step | hg002 total Ir | nova total Ir |
|---|---|---|
| festive | 2583.1M | 2261.2M |
| + trimmers (§2) | 2556.9M (−1.0%) | 2245.6M (−0.7%) |
| + `findNewline`, `allBytes`, `reverseMapBytes` | 2391.3M (−7.4%) | 2153.7M (−4.8%) |
| + `parseRecord` quality without validation | 2355.5M (−8.8%) | 2130.4M (−5.8%) |

Inclusive Ir, hg002, festive → all changes:
- `readChunk`: 394.0M → 273.4M.
- `samLines`: 400.6M → 320.7M.
- `trimRecord`: 209.5M → 181.7M.

## 4. Wall and CPU (1M plain files, 4 cores, 5 reps, medians; map wall s / user+sys s)

| set | festive (bd0) | + trimmers (bd1) | + Spec patch (bd3) |
|---|---|---|---|
| nova1M | 29.4 / 104.2 | 30.0 / 105.8 | 28.9 / 102.2 (−1.7% / −1.9%) |
| hg002_1M | 32.7 / 115.3 | 33.9 / 119.2 | 31.2 / 109.7 (−4.6% / −4.9%) |

- **Run-to-run spread is ±3–5%.** So the trimmer change alone (≈1% Ir) is not visible natively. The first rep of bd0 on each set was slow (cold page cache), but the median is unaffected.
- **Native gain is about half the Ir gain.** The removed instructions are cheap, well-predicted compares; the remaining time is memory and allocation.

## 5. Left for later (not bounds checks; String work)

- **`mateName` / `samName` `splitOn`:** about 5.7% of Ir on hg002, 7.7% on nova. The byte pipeline's `qnameOf` removes it.
  - A `@[csimp]` from `splitOn " " |>.headD` to a byte scan would need `String.splitOn` lemmas that do not exist in 4.35.
- **`fromUTF8!` in `samSequence` and `trimRecord`:** about 3%. It cannot be dropped while quality is a String: a trimmed slice of a String's bytes need not be valid UTF-8, and nothing in the types says ASCII. Quality as bytes (shim_speed / byte pipeline) removes it.
- **`lean_byte_array_push` in `revMapU`:** 29M. It could write into a copy with `uset` instead, but the proof is harder.

## 6. Combining with byte_pipeline.patch

- **`allBytes` and `reverseMapBytes`:** these hunks are independent of the byte pipeline. In la_bp4 the same loops are 4.4% + 4.2% of Ir.
- **`findNewline`:** this conflicts with shim_speed's `findNewlineU`. Take this patch's structural version, which has no `while` and is fully proved.
- **`parseRecordF`:** with quality as a ByteArray (shim_speed), the UTF-8 step disappears and `parseRecordF` is not needed.

## 7. CI

- **Branch state** (trimmer changes and notes; Spec untouched): `FUZZ=1 Testing/scripts/CI_check.sh` → ALL CHECKS PASSED. That covers standard axioms only, no forbidden tokens, the mirrors, and the output fuzz (2917 pairs, no violations).
- **Spec patch applied locally:** a full `lake build` (434 jobs, all Proofs including TrimRecord) succeeds, and the Proofs/ mirrors are byte-identical to Spec.
  - `Spec/FROZEN.sha256` must be regenerated when the patch is applied; that is not done here.
