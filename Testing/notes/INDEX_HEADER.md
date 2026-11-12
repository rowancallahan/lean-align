# Index header (patch for Rowan: `Testing/notes/index_header.patch`, NOT applied)

**Problem.** If you run a new binary on an old `shim.idx` (one built before the heavy 25-mer table), `loadIndex` returns `none`. Every pair then comes out unmapped and the run still exits 0.

**Fix.** The patch adds a sidecar file next to `INDEX.chromosomes`. The index bytes, `buildIndex` and every proof stay the same.

- `build` deletes any old `INDEX.header` first. After the index and `.chromosomes` have been written, it writes one line:
  `lean-align-index<TAB>code <indexCodeHash><TAB>genome <FNV-1a 64 of the FASTA file bytes>`.
  The genome hash is FNV-1a 64 over the raw FASTA, read in 1 MiB pieces. It is the same hash function `shim_fasta_failfast.patch` uses for the index checksum.
- `map` stops with `throw` (exit 1, no SAM written) before it reads the index if `INDEX.header` is missing, malformed, or holds a code hash other than the one compiled in. There is no recovery path. The genome hash is only recorded. `map` does not have the FASTA, so checking the genome hash belongs to a later `quick check` / `verify` command.
- The code lives in the new file `Spec/IndexHeader.lean`. It imports only Init and is not in FROZEN. In `Spec/Shim.lean` and `Main.lean`, the old `main` is renamed `run`. A new `main` at the end of the file checks the header and calls `run`, and also writes the header after `build`. Both files also gain `import Spec.IndexHeader`, so the CI mirror check still passes. `Spec/FROZEN.sha256` gets the new Shim checksum.

**Code hash: what it covers and how to regenerate it.** `indexCodeHash` is computed by `sh Testing/scripts/index_code_hash.sh` (new file): the sha256 of the `shasum -a 256` lines, in `LC_ALL=C` order, of these files:
`Proofs/{Aligner,Index,Heavy,HeavyBuild,LastResort}.lean`, `Aligner/index/minimizer/*.lean`, `Aligner/index/packed_genome/*.lean`.
These are `buildIndex`, `saveIndex`, `buildLoaded`, the heavy table, the minimizer builder and the packer. The repo had no FROZEN hashes for this code, so the patch adds this list.

`CI_check.sh` now runs `index_code_hash.sh --check`. It fails if any of these files changed and the constant was not updated. To update it:
1. Run the script.
2. Paste the hash it prints into `Spec/IndexHeader.lean`.
3. Rebuild, then re-run `build` on every index.

One cost: `Proofs/Aligner.lean` also holds `alignPairs`, so a mapper-only edit to that file also requires a new hash and an index rebuild. This errs on the safe side.

**Applying.** On 050ef82: `git apply Testing/notes/index_header.patch` (80 insertions, 4 deletions over 6 files; the patch file is 172 lines).
With `audit_medium_patches/shim_fasta_failfast.patch`, in either order, every hunk applies except `Spec/FROZEN.sha256`, because both patches change the Shim line there. Do this instead:
`git apply --exclude=Spec/FROZEN.sha256 <the second patch>`, then
`sed -i "s/^[0-9a-f]*  Spec\/Shim.lean$/$(shasum -a 256 Spec/Shim.lean | cut -c1-64)  Spec\/Shim.lean/" Spec/FROZEN.sha256`.

**Verified** (scratch application, since reverted):
- Patch alone: `FUZZ=1 sh Testing/scripts/CI_check.sh` passes (2917 fuzz pairs).
- Patch plus failfast, with the FROZEN line regenerated: the same full CI passes.
- Both orders of `git apply` were checked, as described above.
- Fuzz genome (`sim_genome_dup.py g 2 2 7`, 200 mason pairs):
  - correct header: `map` exits 0 with 400 records
  - code hash changed by one letter: exit 1, no SAM
  - `garbage` header: exit 1
  - missing header: exit 1
  - restored header: exit 0
- The genome field matches a Python FNV-1a 64 of the FASTA.
- Changing an index file without updating the constant makes `index_code_hash.sh --check` exit 1.
