# Audit findings 5, 6, 10, 11, 14: repro, impact, proposed fix (2026-11-02)

Proposal for Rowan. **Nothing in Spec/, Proofs/ or Main.lean is changed on this branch.** Every fix below lives in Spec/Fasta.lean, Spec/Fastq.lean,
Spec/Shim.lean (+ the mirrors Proofs/Fasta, Proofs/Fastq, Main.lean), so it is your call. They are bundled as one tested patch:
`Testing/notes/audit_medium_patches/shim_failfast.patch` (`git apply` it from the repo root).
Tested on a scratch copy of this base (e384063): `lake build` ok; `CI_check.sh` passes every step **except** the frozen checksum of `Spec/Shim.lean`
(the patch edits it, so `Spec/FROZEN.sha256` needs your re-freeze if you take it). Mirrors (`Proofs/*`, `Main.lean`) are regenerated and the mirror checks pass.
No sorry / native_decide / extern / unsafe / implemented_by / partial added.

Branch adds only: this note, the patch file, `Testing/scripts/input_audit.py` (prints the real-data facts asked for below; run it on your data).

Repros ran with the base binary (`lake build`, `.lake/build/bin/lean-align`), tiny hand-made genomes (1.5-3 kb), reads 100-150 bp, `MIN=100 MAX=600`.

## What I could NOT measure (read this first)

The session's network policy denies UCSC, the iGenomes S3 mirror, GIAB and Google Storage (`403 CONNECT`, per `__agentproxy/status`), so
**hg38, the HiSeq set and the NovaSeq set are not on this box**. Every "real data" statement below is therefore either (a) a fact from
this repo's own notes, with the source named, or (b) proved/observed on the tiny inputs, or (c) a command for you to run (`input_audit.py`).
I did not guess numbers. Items needing your run are marked **[RUN]**.

## 5. N matches N

**Repro (spec level).** `scoreWalk` gives `matchScore` when `q = r`, so N vs N = 0 (evidence file already has the `#eval`). Through the shim I could not
reproduce an N-read aligning into an N run, because the trimmer removes every N:

| input | result |
|---|---|
| 100 x N pair, qualities `I`, `#` or `5`, genome with an 800-N run | `trimmedAway1`, flags 77/141, unmapped |
| 150 bp read with one N at offset 2, 10, 25, 40, 75, 110, 125, 140, 147 (genome has N there too) | N never in the mapped read: CIGAR is the part on one side of the N (`147M`, `139M`, ..., `75M`, `110M`), `AS:i:0` |
| 100 bp mate spanning a genome 10-N gap | mate trimmed to the 50 bases after the gap (`50M`) |

**Why.** `Aligner/mapper/ReadTrim.lean` scores any non-ACGT letter -1e6 (`perBase`) and proves `trimRead_acgt` (every kept letter is A/C/G/T). So a read
that reaches `alignPairs` through the shim contains no N, and "N read vs N genome" cannot happen; read-ACGT vs genome-N is the normal mismatch (-4).

**Impact on real data.** Through the shim: none, by proof (not by sampling). So the HiSeq/NovaSeq sets cannot align into N runs; what reads with N
cost is trimming, not mis-placement. Repo notes: 0.1 % of the first 1M HiSeq reads contain N (SESSION_SUMMARY.md, "Real data" line). **[RUN]** counts for
both sets and the hg38 N runs: `python3 Testing/scripts/input_audit.py hg38.upper.fa HiSeq_R1.fq NovaSeq_R1.fq`. The audit's "about 150 Mb of N" is not
verified here.

**Residual risk.** The theorem `alignPairs_correct` itself still allows N=N for any other caller, and the trimmer is outside the spec files.

**Proposal (smallest).** No code change; one sentence in the Spec header: "N = N scores as a match; reads reach `alignPairs` only after `trimRead`, which keeps only A/C/G/T
(`trimRead_acgt`)". The real spec fix, `if q = r ∧ q ≠ 'N'` in `scoreWalk` (Spec/Alignment.lean, frozen), changes the objective every kernel and certificate
(`AlignmentSpec`, wfa*, band, gotoh) is proved against, so I did **not** try it; it is a large re-proof for a case the shim cannot reach.
The fail-fast part that I do propose is in 6 below (reads must be ACGTN before trimming; the trimmer then guarantees ACGT).

## 6. Lowercase / non-ACGTN letters

**Repro.** Genome 1500 random ACGT; read pair from position 500 (100 bp, fragment 300).

| genome | reads | base binary |
|---|---|---|
| uppercase | uppercase | `99/147 pos 501 100M AS:0 unique` (control) |
| bases 400-1100 lowercase (soft-masked) | same reads | **both mates unmapped**, flags 77/141, `XB:i:-32 XU:unknown`; exit 0, no warning |
| 14 `R` (IUPAC) inside the read region | same reads | same: both unmapped, exit 0 |
| uppercase | reads in lowercase | **both mates `trimmedAway1`**, `SEQ *`, exit 0 (lowercase is "not ACGT" for the trimmer) |

**Impact on real data.** From the repo notes, not re-measured: iGenomes hg38 is soft-masked, "about half" lowercase (SESSION_SUMMARY.md, 2026-10-27 evening);
the packer stores each non-ACGT letter as a boxed exception, so the whole-genome build on the raw file ran out of memory; `Testing/data/fetch.sh` therefore builds
`hg38.upper.fa` with `awk toupper`, and every benchmark uses it (OUTPUT_VS_MINIBWA: "the release holds only hg38.upper.fa"). So the benchmark data is not
affected, but the tool accepts the raw file at small scale and silently maps nothing over masked regions. Whether `hg38.upper.fa` contains IUPAC codes other than N: **[RUN]**
`input_audit.py` ("not ACGTN"). If it does, the strict check below will make the build fail on it, loudly; then decide between rejecting and an explicit map-to-N step.

**Proposal.** Fail fast, no silent folding. `readFasta` (Spec/Fasta.lean) and `readFastqRecord` (Spec/Fastq.lean) throw on any sequence byte outside A C G T N
(exactly the spec's `GenomeIsDNA` alphabet), and on sequence lines before the first `>`. After the patch: soft-masked and IUPAC genomes stop the `build` with
`FASTA lc: letters other than A C G T N (lowercase, IUPAC)` (exit 1); lowercase reads stop the `map` with `FASTQ: letters other than A C G T N` (exit 1).
Alternative if you prefer folding: `.toUpper` on the line in `readFasta` (one line), but it hides the input difference and still leaves IUPAC; I do not recommend it.
Cost: one extra byte loop per FASTA/FASTQ line (not measured on hg38; I expect it is small next to the index build, which took 6.7 s for a 3 kb genome because of a fixed 268 MB table).

## 10. FASTA name is the whole header line

**Repro.** `>1 dna:chromosome chromosome:GRCh38:1:1:1500:1 REF` and `>2<TAB>desc`:

```
@SQ  SN:1 dna:chromosome chromosome:GRCh38:1:1:1500:1 REF  LN:1500
@SQ  SN:2<TAB>desc<TAB>1500  LN:0     <- extra tabs: the sidecar line has 3 fields, so readChromosomeList falls back to (whole line, 0)
t  99  2<TAB>desc<TAB>1500  501 ...    <- RNAME carries the tabs: every record has 2 extra columns
```
(the `.chromosomes` file was `1 dna:...REF<TAB>1500` / `2<TAB>desc<TAB>1500`).
A space-only header gives a valid-looking but non-standard `SN` that does not match `samtools faidx` / GATK dictionaries; a tab header gives an **invalid SAM**.

**Impact on real data.** UCSC / iGenomes hg38 headers are `>chr1` ... `>chrUn_...` (no spaces) by my knowledge of that file, **not verified here**; **[RUN]**
`input_audit.py` prints "headers with space/tab". Ensembl/NCBI FASTA headers do have spaces, so the first user with a different hg38 build hits it.

**Proposal.** `readFasta`: name = header up to the first space or tab; throw on an empty name. After the patch the same input gives `SN:1`, `SN:2`, RNAME `2`, exit 0.
Touches Spec/Fasta.lean (+ Proofs mirror), 3 lines.

## 11. `.chromosomes` sidecar not tied to the index

**Repro.** Index built from `two.fa` (chromosomes `1`, `2`), sidecar copied from a different genome with the chromosomes swapped and renamed `X`, `Y`:
read pair from the second chromosome of `two.fa` -> `@SQ SN:X`, `SN:Y`, record **RNAME `Y`**, flags 99/147, MAPQ 60, exit 0. The placement is chromosome index 1 of the index; the sidecar says index 1 is `Y`, from another genome. No error.
Other sidecar faults on the base binary: file missing -> uncaught `no such file`, exit 1 (fine); sidecar with only one line for two
chromosomes -> reads on chromosome 2 get RNAME `*` with flag 99 (proper pair) and POS 501; length `abc` -> `PANIC at String.Slice.toNat!` and the run **continues**
(Lean panics print and go on; exit 0).

**Impact on real data.** Needs a stale or hand-edited sidecar, e.g. re-running `build` into the same index path for another genome partway, or copying an `.idx` without its
sidecar. Not triggered by anything in the repo's own scripts. It cannot be measured on the data; the failure is silent (correct placement, wrong name).

**Proposal (outside the proved index).** `build` writes, as line 1 of the sidecar, `#index<TAB>size<TAB>fnv1a64(index bytes)`; `map` recomputes both from the index file it
loaded and throws on a mismatch. Also: every other line must be exactly `name<TAB>number`, else throw (`toNat?`, no `toNat!`). Patch: `Spec/Fasta.lean`
(`fnv1a`, `chromosomeListText index`, `readChromosomeList path index`) and `Spec/Shim.lean`/`Main.lean` (pass `index` to both calls). After the patch:
swapped sidecar -> `w.idx.chromosomes: was not saved with this index (size or checksum differ)`, exit 1, no SAM; malformed length -> `length 'abc' is not a number`, exit 1.
Cost: a 268 MB index (the 3 kb test genome's) maps in 0.48 s total including the hash; so about 1 s per GB. **[RUN]** on the hg38 index for the real number.
**Limit:** a sidecar whose header line is right but whose names were edited by hand is not detected (that needs the names inside the index, which is the proved-format change in the audit's
original fix; not done). Old sidecars (no `#index` line) are rejected, `build` must be re-run.

## 14. Shim robustness

All repros on the base binary, `two.fa` index. Exit status is the shell's, not `head`'s.

| case | base binary | after patch |
|---|---|---|
| mate names differ at pair 20001 (past the first 20000-pair chunk) | exit 1, **but `big.sam` has the header + 40000 SAM lines**, looks complete | exit 1, only `big.sam.part` exists; `big.sam` absent |
| non-numeric `MIN_FRAGMENT` | `PANIC at String.Slice.toNat!`, run continues | `MIN_FRAGMENT is not a number`, exit 1 |
| non-UTF-8 quality byte (0xFF) | `PANIC at String.fromUTF8!`, continues | `FASTQ: quality outside '!'..'~'`, exit 1 |
| QNAME empty (`@/1`, or bare `@`) | SAM line with empty field 1 | `read name '/1' is not a SAM QNAME`, exit 1 |
| QNAME with a tab (`@a<TAB>b/1`) | SAM line with an extra column | exit 1 (`header line is not '@' + printable ASCII`) |
| header without `@` (`Xread/1`) | first letter silently dropped, read named `read` | exit 1 |
| third line not starting `+` | accepted | exit 1 |
| file ends in the middle of a record (both files) | treated as end of file, rest silently ignored (code read: `readFastqRecord` returned `none` on a missing line) | exit 1 `file ends inside a record` |
| QNAME > 254 chars | accepted (code read, not run) | exit 1 |

**Impact on real data.** None visible in the repo's data (these are error-path behaviours); the truncated SAM is the dangerous one for pipelines that ignore exit status.
Remaining panics: none found in the shim paths I ran; library `panic` in `Aligner/` not audited.

**Proposal.** Patch hunks: `Spec/Fastq.lean` (`allBytes`, `isDnaByte`, checks in `readFastqRecord`, QNAME check in `readChunk`), `Spec/Shim.lean`/`Main.lean`
(`toNat?` + throw, write `OUT.part`, `flush`, `rename` at the end). Why `throw` and not `assert!`: in compiled Lean `assert!` / `toNat!` panic **prints and continues** (seen above, exit 0),
so asserts would not fail fast in the binary.
Not covered (stays as audit finding 14 listed): wrapped multi-line FASTQ is rejected only when lengths differ; `mapq`/`XT` semantics; `samChunk` zip.

## Applying / re-freezing

```
git apply Testing/notes/audit_medium_patches/shim_failfast.patch
PATH=$HOME/.elan/bin:$PATH lake build
sha256sum Spec/Shim.lean   # update the Spec/Shim.lean line of Spec/FROZEN.sha256 if you accept it
sh Testing/scripts/CI_check.sh
```
