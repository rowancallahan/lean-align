# Lemmas for the parallel byte reader and the byte SAM writer

Both draft files now type-check with `lake env lean Testing/notes/byte_specs/FastqBytes.lean` (and `SamBytes.lean`) with **no `sorry`**; every theorem below depends on
`[propext, Classical.choice, Quot.sound]` only (`#print axioms` at the end of each file). Nothing in Spec/, Shim or Main was changed; the files are not built by lake.

## Verdict on the two drafts' sorry lemmas
Both statements were **true as written**; no change needed. Two points that cost effort and that Rowan may want to change in the spec text:
- `lines` goes through `ByteArray.toList`, which core defines by an index loop with no lemma. I proved `toList_eq : bs.toList = bs.data.toList` (and the loop invariant `toList_loop`); defining `lines` with `bytes.data.toList` would make this unnecessary.
- `samChunk_eq` (the chunk the shim writes = `linesBytes` of its pairs' lines) needs `0 < parts` (`parts = 0` gives an empty chunk); the shim passes 16.

## The lemmas

| lemma (file) | statement | unlocks | proof status | effort / notes |
|---|---|---|---|---|
| `lines_append_of_end` (Fastq) | if `a` ends with `\n`, `lines (a ++ b) = lines a ++ lines b` | cutting a FASTQ at line ends | proved | ~40 lines; core `List.splitOn_append_cons_self`, a `getLast`/`dropLast` case split |
| `parseLines_append` (Fastq) | `parseLines (L1 ++ L2) = (parseLines L1).bind (.. (parseLines L2).map (ra ++ ·))` when `L1.length = 4 n` | per-record composition, including which error wins | proved | first error in slice order |
| **`parseFastq_append`** (Fastq) | the draft lemma: cut after a record (ends with `\n`, `(lines a).length % 4 = 0`), parse parts = parse whole | splitting one chunk's bytes over tasks | **proved** | the empty-slice case included |
| **`parseSlices_eq`** (Fastq) | `parseSlices slices = parseFastq (concatBytes slices)` when all slices but the last are `Boundary` (ends with `\n`, whole records) | the parallel parser: parse each slice on a task, join in slice order, first error in order | **proved** | induction on the slice list using `parseFastq_append` |
| **`cutLinesL_spec`**, `cutLinesL_boundary` (Fastq) | the finder `cutLinesL (4 n) l = some (pre, post)` gives `l = pre ++ post`, `pre` holds exactly `4 n` lines, ends with `\n`, and `Boundary pre` | the serial record-boundary scan really cuts at record boundaries | **proved** at list level | the shim's scan is a byte-index loop (`findNewline` / `scanLines`); that it equals `cutLinesL` on the byte array is the missing bridge (below) |
| `linesBytes_append`, **`samFile_chunks`** (Sam) | `samFile` of the concatenation of chunks = header ++ the chunks' bytes in order | writing chunk after chunk (chained writer, any chunking) | **proved** | |
| **`samChunk_eq`** (Sam) | `samChunk chromosomes chunk results parts = linesBytes (all lines of the chunk's pairs)` for `0 < parts` | the per-chunk term of `samFile_chunks`; with `samChunkB_eq` (research/io2) it connects the byte writer to `samFile` | **proved** | slicing lemma `range_slices`; task join lemma `foldl_tasks` |

Composition for the byte writer, no new work: for chunks whose letters and qualities are ASCII, `samChunkB = samChunk` (**`samChunkB_eq`**, research/io2 `Proofs/SamBytes.lean`, `Testing/notes/sam_bytes.patch`, standard axioms, full `CI_check.sh` passes)
and `samChunk = linesBytes (...)` (`samChunk_eq`, this file), so `samChunkB chunk results 16 = linesBytes (lines of the chunk)`, which is the term inside `samFile_chunks`. To state it as one theorem the two files must be in one build (the patch applied).

## Not yet proved (what the shim code still needs), with effort
1. **Byte scan refines the list spec.** The shim's scan (`findNewline` loop on the `ByteArray`, or `scanLines` in the prototype) returns the index `p` after the `4 n`-th newline; prove `(b.extract i p).toList` is `cutLinesL`'s `pre` (induction on the number of lines, `ByteArray.extract` lemmas, `findNewlineU` spec). ~half a day, no new ideas. Unlocks: the serial part of the reader is proved to cut at record boundaries.
2. **One slice parsed straight from the buffer = `parseFastq` of that slice.** The prototype `parseOne`/`parsePart` (research/io `IoFast.lean`) reads four lines from offsets in the shared block and validates them; show it equals `parseFastq (b.extract s e)` (compose with `parseRecord`; the QNAME extraction must equal `mateName`). 1-2 days; the only part with real content is the name rule (`takeWhile`, `/1`,`/2`) on bytes.
3. **`pairsOfFiles` = what `readChunk` + `trimChunk` return.** `pairUp` on the joined slice lists vs the chunk loop with the mate-name check; bookkeeping, ~1 day.
4. **ASCII of parsed records.** `samChunkB_eq` needs `RecordAscii` (letters and qualities below 128); `parseRecord` checks `isDnaByte` and `'!'..'~'`, trimming only shortens: a short lemma (hours) that discharges the hypothesis for every record `parseFastq` returns.
5. **`samName` as bytes.** After the byte writer, `samName record.name` (`String.splitOn`/`takeWhile`) is the largest cost left in the format step (about 29 M of 127 M Ir per 2 000 pairs); carrying the QNAME as bytes in `FastqRecord` (spec change) makes it free and makes the byte writer fully String-free.

## What they enable (measured, NovaSeq, 2 000 pairs unless said; instruction counts are exact, times are noisy)
- Reader as the critical path (S-G): about 27 us/pair serial parse. The unproved prototype (research/io `IoFast.lean`) moves parse, validate and trim to 16 tasks and leaves a serial scan of about 1.3 us/pair (25 ms per 20k chunk, 4 cores); parse overhead 108 M to 47 M Ir (2.3x), `readChunk` 187.5 M to 126.0 M Ir, byte-identical SAM. Lemmas 1-3 above are what turns that prototype into a proved reader; `parseSlices_eq` and `cutLinesL_boundary` are the two inequalities-free pieces that already exist.
- Byte SAM writer (proved): format step 157.9 M to 126.6 M Ir (-20 %), whole process 1 226 M to 1 196 M Ir (-2.4 %); with the QNAME as bytes (item 5) about 30 M more per 2 000 pairs; wall: SAM format 126 ms per 20k chunk now (4 cores), it is not on the critical path at 4 threads, matters when alignment scales to 8-10+ threads.
- Per-chunk times at 4 cores (corrected, d0d2a79): read 265 ms, trim 77, align 676, sam 126 (NovaSeq); the serial reader becomes the cap above about 10 threads; with the parallel parser the serial remainder is the 25 ms scan, so the reader stops being the cap until about 100 threads.
