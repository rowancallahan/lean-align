# lean-zip: what a human must read, and what the machine checks

Map for Rowan, 2026-08-21, from a full-history clone of kim-em/lean-zip
(1,677 commits, first commit 2026-02-17). Purpose: separate the AUDIT SURFACE
(read-and-trust) from the machine-checked mass, since the repo interleaves
them and authorship metadata is useless for this (every commit — code, specs,
proofs — is authored "Kim Morrison"; the agents committed under her name).

## The punchline

There is no "human-written part" to find. Specs, implementation, and proofs
were all agent-written. The meaningful split is not WHO WROTE IT but WHAT
MUST BE READ versus WHAT THE KERNEL CHECKS. Your instinct was right: the
roundtrip statement is the heart of the read-and-trust layer.

## Layer A — read and trust (the audit surface; small)

1. **Capstone theorem statements** (a few lines each; read these first):
   - `inflate_deflateRaw` in `Zip/Spec/DeflateRoundtripProduction.lean` —
     "inflating what we deflate, with the decoder we ship, returns the input
     exactly", ∀ input, ∀ level.
   - the zlib/gzip wrappers (`Zip/Spec/ZlibCorrect.lean`, `GzipCorrect.lean`)
     e.g. `zlib_decompressSingle_compress`.
   - `inflate_correct` in `Zip/Spec/InflateCorrect.lean` — shipped decoder
     agrees with the RFC-1951 bitstream spec `Deflate.Spec.decode`.
2. **The spec DEFINITIONS** — the `def`s, not the theorems around them.
   They are concentrated in five root files but interleaved with proofs
   (hence the "not organized to understand" feeling — extraction command
   below):
   - `Zip/Spec/Deflate.lean` — 24 defs: the RFC 1951 bitstream spec
     (bits-from-bytes LSB-first, block structure, stream decode),
     explicitly implementation-independent.
   - `Zip/Spec/LZ77.lean` — 5 defs. `Zip/Spec/Huffman.lean` — 9 defs
     (canonical codes; Kraft/prefix-freeness live in HuffmanKraft).
   - `Zip/Spec/Crc32.lean` — 7 defs (bit-level polynomial spec).
     `Zip/Spec/Adler32.lean` — 8 defs.
   - Total definitional surface: ~50–60 defs, on the order of a thousand
     lines. This is the "does the Lean match the RFC prose" eyeball layer.
3. **The C stopgaps**: `c/` = 4 files, 496 lines total —
   `bytearray_wide_ffi.c`, `copy_within_ffi.c`, `extend_within_ffi.c`, and
   notably **`inflate_fast_ffi.c`** — plus their pure-Lean reference twins.
   Proofs are about the twins; the C is trusted (runtime cross-checked).
   ⚠ For OUR golf-arena runtime gate: call the PURE-LEAN verified decoder
   path, not any C-accelerated path, so the gate carries the proof.
4. **The empirical anchor's design**: `conformance/` — both-direction interop
   vs system zlib + deterministic fuzzing. Read what it tests, not its code.

## Layer B — machine-checked; never read (the mass)

Everything else in `Zip/Spec/` — 68 files, ~51,700 lines, of which ~63 files
are named `*Correct`, `*Complete`, `*Roundtrip`, `*Props`: proof
infrastructure connecting `Zip/Native/*` to the Layer-A definitions. The
kernel re-checks all of it on every build. Reading it adds nothing to trust.

## Layer C — the supervision record (pre-split tag; the workflow answer)

The `pre-split` tag preserves how it was actually made:
- `plans/` — per-track plans, including **`track-e-trusted-boundary.md`**:
  their own living trusted-base discipline (boundary inventory, per-entry-
  point contract ledger for attacker-controlled input, hardening queue,
  `SECURITY_INVENTORY.md`). They treat the TCB as a maintained artifact —
  same philosophy as our BRIEF/house rules.
- `progress/` — timestamped per-session agent logs from 2026-02-19 onward,
  each recording accomplishments, decisions, and a **sorry count**. Log
  000001 (day one of the verified codec): Adler-32 and CRC-32 spec + native
  + equivalence proofs, in one session.
- `.claude/commands/` — the agent loop itself: plan / feature / review /
  repair / replan / reflect / summarize.

Timeline: 2026-02-17 repo starts as UNVERIFIED zlib FFI bindings; verified
pure codec begins 2026-02-19 with checksums; the whole verified tower is
~6 months of gated agent fleet.

## How this maps to our Track A plan

- The equivalence target `Zip.Native.deflateRaw` and its roundtrip tower are
  Layer B for us too — we compose with them, never re-read them.
- What Rowan personally audits before the fleet runs: Layer A above (once),
  plus our Track A statement (asm register model = `deflateRaw` under
  memory-layout assumptions) — the same basic-terms process as the trimmer.
- Their `progress/` + sorry-count + plans structure is worth copying
  verbatim for our fleet.

## Audit commands (run these yourself)

Extract just the spec definitions from the five root files:
```
cd <lean-zip> && grep -n -A3 "^def \|^noncomputable def " \
  Zip/Spec/Deflate.lean Zip/Spec/LZ77.lean Zip/Spec/Huffman.lean \
  Zip/Spec/Crc32.lean Zip/Spec/Adler32.lean | less
```
The capstone statements:
```
sed -n '1,40p' Zip/Spec/DeflateRoundtripProduction.lean
```
The C trusted base:
```
wc -l c/*.c && cat c/copy_within_ffi.c
```
The supervision record:
```
git show pre-split:plans/track-e-trusted-boundary.md | less
git show pre-split:progress/2026-02-19T12-34-46Z_000001.md
```
Local full-history clone used for this map:
`/private/tmp/claude-501/-Users-rowancallahan-read-window-trimmer/2f88839d-1b2e-4722-8b02-dbb1c564bdd0/scratchpad/lean-zip`
(scratchpad — re-clone to keep it past this session).
