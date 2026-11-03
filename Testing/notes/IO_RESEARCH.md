# Where the FASTQ read and SAM write cost is, and a pure-Lean prototype that removes most of it

Base: festive 6ef8212. Box: 4 vCPU, `taskset -c 0-3`, real NovaSeq 2x151 (first 2 000 pairs for callgrind, all 200 000 for timing), hg38 release index.
"+patch" = `Testing/notes/shim_speed.patch` applied locally. "proto" = the unproved prototype of this note (`Testing/benches/IoFast.lean`, built on top of the patch).
Nothing in `Spec/`, `Proofs/`, `Main.lean` was changed on this branch. Files: `Testing/benches/IoFast.lean` (prototype), `Testing/benches/IoBench.lean` (bench), `Testing/notes/io_lakefile.patch` (adds the `IoFast` lib and `io_bench` exe to the lakefile; apply with `git apply`).

## 1. Breakdown (callgrind, instructions, first 2 000 NovaSeq pairs, one chunk)

| | total Ir | `readChunk` (parse + trim) | `alignPairs` | `samChunk` | SAM bytes |
|---|---|---|---|---|---|
| base | 526.4 M | 265.8 M (50 %) | 164.7 M | 67.1 M | |
| +patch | 449.9 M (-14.5 %) | 188.3 M (42 %) | 164.7 M | 70.4 M | identical to base |
| +patch, bench harness (old path) | 447.3 M | 187.5 M | 164.7 M | 70.4 M | |
| +patch + proto (bench harness) | **334.2 M (-25 %)** | **126.0 M** | 164.7 M | **~30 M** (by subtraction) | **identical** (NovaSeq and HiSeq 200k) |

(Index load and start-up are 13.8 M of every total.) At this size reading is the largest single piece, bigger than alignment.

Where `readChunk` goes in base (self cost, 2 000 pairs): `lean_dec_ref_cold` + `mi_free` + `lean_alloc_small_object_core` 113 M (22 % of the whole run; one boxed object per line, `String`, `List`, `Array` cell), UTF-8 handling (`lean_string_utf8_get`, `utf8_strlen`, `validate_utf8`, `String.splitOn`, `skipWhile` over the name for `mateName`) about 126 M, `findNewline` loop 22 M, the four `allBytes` validation passes 35 M, and only then the useful work: `ReadTrim.wlU` 34 M and `AdapterTrim.saLoopU` 27 M. The patch removes the `splitOn` and the per-byte `findNewline` cost but still pays `mateName` (35 M, `takeWhile` is a per-character loop) and the allocation cost per line.
`samChunk` (67-70 M): `samLines` builds `String`s per field (`toString`, `intercalate`, `++`), `String.fromUTF8!` validates SEQ/QUAL (reversed through `List`), then `.toUTF8` copies the text again.

## 2. Is reading the bottleneck? Yes, already at 4 threads (NovaSeq 200k, 20 000-pair chunks, measured one phase after the other, `io_bench`)

| phase per 20k chunk | base | +patch | +patch + proto |
|---|---|---|---|
| serial `readChunk` | ~310 ms (10 chunks: 3 088 ms) | ~230 ms (2 084-2 703 ms over 5 runs) | ~125 ms (813-1 706 ms over 5 runs; 16 parse tasks on 4 cores) |
| `alignPairs`, 4 threads | ~70 ms (699 ms) | ~68 ms (601-808 ms) | ~68 ms |
| `samChunk`, 16 tasks | ~83 ms (826 ms) | ~75 ms (601-906 ms) | ~50 ms (333-618 ms) |

Reading one 20k chunk takes 3.5-4.5 times as long as aligning it on 4 cores. The shim overlaps reading chunk n+1 with aligning chunk n, so wall time is about max(read, align + sam) per chunk = read: that is why 4 to 16 threads will not help until reading is fixed (at 16 threads align would be ~17 ms per chunk against 230 ms to read: the run is 100 % bounded by the serial reader, about 87 000 pairs/s). The timings are noisy (the box shows the usual 20-30 % spread); the order is not.
**Disk is not the cost.** `strace -f -T`: the 31 FASTQ block reads (4 MB each, from the page cache) take 0.14 s for the whole 200k run (max 47 ms), the 8 large SAM writes 0.26 s (125 MB); the index read is 18.7 s of blocked time under strace (5.3 GB) and is a separate issue. `strace -c`: futex waits dominate (task pool), 1 627 calls.

## 3. What minibwa does (source c07de5c: `kseq.h`, `bseq.c`, `format.c`, `map-main.c`)

- Input: `gzread` into a 16 KB buffer; `ks_getuntil2` finds the end of a line with `memchr` (SIMD in glibc), then `memcpy`s the bytes into a `kstring_t` that is reused for every record (`seq`, `qual`, `name`, `comment` are grown once and kept). No per-record allocation on the parse side, no validation (no alphabet, quality range or UTF-8 checks), `\r` dropped, `U` to `T` and `kstrdup` of name/seq/qual into the batch record (one malloc per field).
- Batches: whole batches of reads (by total bases, default 10 M), parsed by one thread in a pipeline stage, mapped by the thread pool, then formatted and written by a third stage.
- Output: `mb_fmt_sam` appends to one `kstring_t` per batch with `kputs/kputc/kputw`-style appends (digits written in place); SEQ and QUAL are `memcpy`d, or a per-byte table lookup loop for the reverse strand (`sam_write_sq`); one `fwrite` per batch. No intermediate strings.
Which of these a pure Lean `ByteArray`/`USize` loop can match: block reads (already done), the reused buffer (Lean has no in-place append into a reused array unless the array is uniquely referenced; we can keep one `ByteArray` per task and `push`, which is what the prototype does), table-free byte loops (yes), digit-by-digit number writing (yes), one allocation per field (yes, `extract`). What Lean cannot match without FFI: `memchr`/AVX2 scanning (a `USize` byte loop costs about 3 Ir per byte; memchr about 0.1).

## 4. The prototype (UNPROVED; `IoFast.lean`; byte-identical output)

- **Reading** (`readChunkFast`): a serial scan counts newlines to find where each of 16 equal groups of records starts (4 lines per record), reading 16 MB blocks; the 16 groups are then parsed, validated (same checks as `parseRecord` and `readChunk`: header `@` + printable, `+` line, letters `ACGTN`, quality `!`..`~`, equal lengths, QNAME 1-254 characters of the SAM alphabet, mate names equal) and trimmed (`cutTruSeq`, `trimRead`, `dropShort`, unchanged) in `Task.spawn` tasks straight from the block, with `@[specialize]` byte loops. Records carry the QNAME, letters and quality as `ByteArray` (no `String`).
- **Writing** (`samChunkFast`): every line appended to one `ByteArray` per part (numbers digit by digit, SEQ/QUAL appended or reverse-complemented byte by byte), parts joined in order.
- **Result.** Instruction count for 2 000 pairs: `readChunk` 187.5 M to 126.0 M, of which 79 M is the unchanged trimming, so the parsing/validation/allocation overhead falls from ~108 M to ~47 M (2.3x); SAM formatting 70 M to ~30 M (2.3x); whole process 447 M to 334 M (-25 %). Wall (4 cores, idle): read 230 ms to 125 ms per chunk (up to 3x better in the best runs), SAM 75 to 50 ms. **SAM and trimmed letters identical** to the current code on all 200 000 NovaSeq pairs (156.7 MB) and all 200 000 HiSeq pairs (222.4 MB) (`io_bench compare`).
- A first version of the prototype used a generic `allIn (p : UInt8 → Bool)` loop and was **slower** than the current code (238 M Ir): the closure call per byte cost 140 M. The `@[specialize]` tail-recursive loop (the same shape as the existing `allBytesGo`) fixed it. Any pure-Lean byte loop in this code needs that.
- What is left in the read path: trimming (79 M of the 126 M: `AdapterTrim.saLoopU` 27 M, `ReadTrim.wlU` 34 M, allocation of the extracted slices), the serial boundary scan (`findNewlineU` 14.9 M per 2 000 pairs, about 25 ms per 20k chunk) and `lean_dec_ref_cold` (freeing the per-record arrays).
- **Does it scale to 16-32 threads?** The parse/trim/format parts run in tasks and scale with the thread count; the serial scan does not. At 25 ms per 20k chunk it limits the reader to ~800 000 pairs/s, below where 32 threads would align (about 8 ms per 20k chunk at the 4-thread rate scaled), so beyond ~12-16 threads the scan becomes the next cap. Options without FFI: scan the 16 byte ranges in parallel and resynchronize at each range start by looking for `\n@` followed two lines later by `\n+` (standard FASTQ resync, an unproved heuristic that can be wrong only if qualities mimic that pattern; check it against the serial scan); larger chunks; two readers (R1 and R2 are scanned independently, so two tasks already halve it).

## 5. FFI? A SIMD `memchr`

Not worth it yet. The scan is 25 ms per 20k chunk, 10 % of the current serial read time and ~2 % of the prototype's; the large costs were allocation and per-byte closures, both fixable in Lean. If the scan becomes the cap at 32 threads, a one-function C shim (`lean_find_newline(b, i)` calling `memchr`) would cut it ~10x, but it adds C to the trusted base and the build; try the parallel resync first. A zero-copy `mmap` of the FASTQ would remove the 4 MB block copies (small: 30 ms per run now) but Lean has no `mmap` without FFI.

## 6. What the FASTQ and SAM specs would need to say for a proved fused version

- FASTQ: records as byte ranges, not Strings: `FastqRecord := {name letters quality : ByteArray}` (or ranges in a block), with `Valid` stating the same constraints as now over bytes; the QNAME rule (up to first space, drop `/1`,`/2`, 1-254 characters of `!`..`?` or `A`..`~`) stated on bytes; block boundaries: a parse of a file is the concatenation of per-record parses, so a parallel parse is correct when each group starts at a record boundary (the lemma that makes the resync proof possible).
- Trimming already works on `ByteArray` (`cutTruSeq`, `trimRead`, `dropShort`); `FastqRecord.quality` as `ByteArray` (what the patch does) is the first step.
- SAM: the spec of a line as a function into `ByteArray` (numbers by `Nat.repr` bytes, SEQ/QUAL as the reverse complement of bytes, tags), with the theorem `samLinesB = (samLines ..).toUTF8` per pair; the digit writer's correctness (`pushNat b n = b ++ (toString n).toUTF8`) is the main small lemma; the text of one chunk is the concatenation of the parts.
- Fusion: if the SAM writer takes the already-trimmed records, nothing needs `String` at all, which also removes `String.fromUTF8!` validation from the trusted/unproved shim.

## 7. Reproduce

```
git apply Testing/notes/shim_speed.patch Testing/notes/io_lakefile.patch      # local only
lake build io_bench
taskset -c 0-3 .lake/build/bin/io_bench old|fast|compare INDEX R1.fq R2.fq 20000
valgrind --tool=callgrind ... io_bench old|fast INDEX 2k_R1.fq 2k_R2.fq 2000      # first 2000 pairs: head -n 8000
```
Notes: `alignPairs` starts its tasks and returns; the bench forces every result before it stops the align timer (otherwise the align work lands in the next read and format timings).
