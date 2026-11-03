# Finishing checklist (Rowan) — before the blog

Order matters: make it right, check it, then understand it.

## 1. Spec changes: bytes in, bytes out (yours)
- Start from `Testing/notes/byte_specs/ProvisionalSpec.lean` (every change vs today's Spec is marked `-- CHANGED`):
  `FastqRecord {qname, letters, quality : ByteArray}`, one `qnameOf` (replaces mateName + samName),
  `parseRecord` with readChunk's checks, `lines` with '\n' at EOF, `pairUp`, byte `trimRecord`, `samFile` as bytes.
- Proofs already done for you (no sorry): `parseFastq_append`, `parseSlices_eq`, `cutLinesL_boundary`, `scanK_boundary`,
  `findNewlineU_eq`, ASCII lemmas, `samFile_chunks`, `samChunk_eq`, `samChunkB_eq` (research/io2). Open items: `LEMMAS.md`.
- Add `alignPairsP` + theorem `alignPairsP (chunkSetup index) = alignPairs index` (unlocks variant B, ~10% faster).
- Update the two proof files that break when quality becomes bytes: `Proofs/SamBytes.lean`, `Proofs/TrimRecord.lean`.
- Regenerate `Spec/FROZEN.sha256`.

## 2. Apply the shim
- `Testing/notes/byte_pipeline.patch` (S-G; against festive a4d9f6f; includes the pipeline, byte parsing, byte names,
  byte SAM, variant B). It assumes the shim_speed changes (quality as ByteArray, findNewlineU) — see UTILIZATION.md §7.
  Supersedes: `pipeline_proto.patch`, `reader_readahead.patch`, `shim_overlap.patch` (no gain; do not apply).
- Read first: `SHIM_EXPLAINED.md`, `UTILIZATION.md` §5 + §7 (every unproved assumption of the pipeline).

## 3. End-to-end theorem (yours)
- Three stops: bytes in (`pairsOfFiles`, trimming proved) -> mapping (`alignPairs_correct`) -> bytes out (`samFile`).
- Statement shape: output bytes = `samFile chromosomes (pairsOfFiles f1 f2 zipped with alignPairs results)`, every result
  satisfies `alignPairs_correct`. Remaining trusted: raw read/write of bytes, the index file (`hIndex`), task order.

## 4. Rebuild the index
- `lean-align build genome.fa shim.idx` (~30 min, ~14 GB RAM): the index format changed (heavy table).

## 5. Check (everything must pass)
- `FUZZ=1 sh Testing/scripts/CI_check.sh` -> `ALL CHECKS PASSED`.
- `MINIBWA=... SAMTOOLS=... bash Testing/verify.sh OUT` -> steps 1-5 (step 4 needs samtools).
- SAM md5 identical to plain festive on the 5M NovaSeq and HiSeq sets.
- Speed headline: ours vs minibwa on the same box, plain files, index load separate, median of 3.

## 6. Bigger machine (16 / 32 cores)
- Utilization and map wall at 4 / 8 / 16 / 32 threads, ours vs minibwa; Gbp/hr and Gbp per core-hour.
- Watch: memory per worker (variant B setup per worker; the 5.3 GB index is shared), job size, the two readers,
  zcat (use plain files or parallel decompression), serial writer.

## 7. Understand it (in your own words)
- `SHIM_EXPLAINED.md`, `UTILIZATION.md`, `byte_specs/LEMMAS.md`, `Testing/fuzz/ROWAN_CHECKLIST.md`, `SESSION_SUMMARY.md`.

## Later (not before the blog)
- Quality-aware soft clipping (the ~3.8% proper-pair gap to minibwa is clipping).
- Proved inflate for .fastq.gz (kim-em/lean-zip; check multi-member gzip, speed).
- Faster trimmer (S-H in progress, exact csimp, theorems unchanged); parseRecord byte checks as a USize loop.
- Index header (code hash + genome hash), quick-check / verify commands.
