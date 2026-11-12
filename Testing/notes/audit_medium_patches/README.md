# Patches for the frozen / Rowan-owned shim files (not applied)

Base for both: festive-fermi `5845b97`. Apply from the repo root; **either order works** (`git apply --check` passes both ways; the patches touch disjoint files).

| patch | touches | what |
|---|---|---|
| `Testing/notes/audit_medium_patches/shim_fasta_failfast.patch` | `Spec/Fasta.lean`, `Spec/Shim.lean`, mirrors `Proofs/Fasta.lean`, `Main.lean`, and `Spec/FROZEN.sha256` (new Shim checksum) | FASTA name up to the first space/tab; throw on non-ACGTN genome letters, empty name, sequence before the first `>`; sidecar header `#index size FNV-1a64` checked against the index, malformed sidecar lines throw; numeric args via `toNat?`; SAM written to `OUT.part` then renamed |
| `Testing/notes/shim_speed.patch` | `Spec/Fastq.lean`, `Spec/Sam.lean`, mirrors, `Proofs/TrimRecord.lean`, `Testing/scripts/CI_check.sh` | speed items 1-4 (about -10 % Ir), rebased over `parseRecord`; `FastqRecord.quality` becomes bytes |

Verified with each patch alone and with both applied (`lake build`, `FUZZ=1 sh Testing/scripts/CI_check.sh` = ALL CHECKS PASSED, no fuzz violations):
SAM byte-identical to the unpatched binary on the fuzz set (600 records) and on the first 20k pairs of `novaseq_200k` (40000 records, release `bench-release`, index `shim.idx`;
with the fasta patch the sidecar was regenerated in the new format). Only the Shim checksum line of `Spec/FROZEN.sha256` changes (in the fasta patch).

Notes: old `.chromosomes` sidecars are rejected after the fasta patch (re-run `build`). The speed patch's `findNewlineU` is still not proved equal to the while loop.
Details of each fail-fast item: `Testing/notes/AUDIT_MEDIUM_FIXES.md` (on `audit/medium-fixes`).
