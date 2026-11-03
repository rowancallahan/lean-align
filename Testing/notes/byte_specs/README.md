# Byte specs: DRAFT for Rowan (bytes in, bytes out)

**Start with `ProvisionalSpec.lean`**: one file showing how `Spec/Fastq.lean` and `Spec/Sam.lean` would change (byte `FastqRecord`, whole-file `parseFastq`, `pairUp`, `samFile`), checked against the current Proofs. The other two files hold the lemmas; `LEMMAS.md` is the status.

Not built by lake, not in Spec/. Each file type-checks on its own with `lake env lean <file>`; no `sorry` anywhere.

- `FastqBytes.lean`: `lines`, `parseLines`, `parseFastq bytes` (the records of a FASTQ file, reusing `parseRecord`),
  `pairUp` / `pairsOfFiles` (pairing + mate-name check). Key lemma `parseFastq_append`: parsing a file cut after a
  whole record = joining the parses (what a parallel parser needs). Later: `readChunk` returns the next records of
  `pairsOfFiles`.
- `SamBytes.lean`: `samFile` (header + every pair's `samLines`, in order, as bytes), `samFile_chunks` (writing chunk
  by chunk = writing all at once), `pushNat` (digit-writer spec). S4's `samChunkB_eq` (research/io2,
  Testing/notes/sam_bytes.patch) is the byte writer proved equal per chunk.

With these, the trusted part of the shim shrinks to: read the file's bytes, write bytes, tasks keep chunk order.
