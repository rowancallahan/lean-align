# Recreating the numbers of `Testing/notes/RESULTS_2026-11-02.md`

Index of recipes (R-ids are used in the results page). Each script prints the number it is about; "measured here" is the wall time of the author's run
(4 vCPU, 15 GB, current head `ab3aacd` + notes) and is stated only where it was actually timed.

| id | what | command (from the repo root, after the setup below) | measured here |
|---|---|---|---|
| R1 | speed vs minibwa (CPU, wall, end-to-end) | `bash Testing/repro/speed.sh SET [REPS=6] [THREADS=4]` | NovaSeq 200k, 3 reps: 3 min 59 s |
| R2 | instruction counts (callgrind) | `bash Testing/repro/ir.sh BINARY SET [PAIRS=2000]` | not timed (200 pairs ran to completion) |
| R3 | mapped / unique / agreement with minibwa | `bash Testing/repro/mapping.sh OUT hg38_mason hg38_low hg002_200k novaseq_200k` | `hg38_low`: 1 min 45 s |
| R4 | unique-genome exact match | `bash Testing/unique/run.sh OUT` | 5 min 9 s |
| R5 | hg38 fuzz audits (rules A-E), 3 seeds x 3 modes | `bash Testing/repro/fuzz_audit.sh OUT` | 4 min 25 s (+ about 50 s once for the one-line genome) |
| R6 | real-data comparison and rescoring | `bash Testing/repro/real_rescore.sh OUT` | not timed (several minutes) |
| R7 | SAM/BAM output checks | `sh Testing/scripts/fuzz_ci.sh` (tiny genome) and `bash Testing/scripts/output_fuzz.sh OUT SET...` (hg38) | `fuzz_ci.sh`: 10-16 s |
| R8 | proofs: CI line, axioms, audit | `bash Testing/repro/proofs.sh` | 1 min 39 s (cached build) |
| R9 | theorem statements at two commits | `bash Testing/repro/statements.sh REV_A REV_B` | seconds |

## Setup from a fresh checkout (once)

```
git clone https://github.com/rowancallahan/lean-align && cd lean-align && git checkout docs/results   # or the commit named by the claim
# Lean 4.35.0 (lean-toolchain). Where release.lean-lang.org is blocked, use the GitHub release zip:
curl -L -o elan.tgz https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz && tar xzf elan.tgz && ./elan-init -y --default-toolchain none
curl -L -O https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.zip && unzip -q lean-4.35.0-linux.zip
export PATH=$HOME/.elan/bin:$PATH; elan toolchain link lean435 ./lean-4.35.0-linux; elan override set lean435
# data: the benchmark release (about 17 GB: hg38 genome, shim.idx, minibwa index mb.*, the read sets); needs gh (REST, no GraphQL)
sh Testing/data/fetch_release.sh bench-release                 # checks SHA-256, joins the parts, links reads + genome into Testing/data/downloads/
lake build lean-align bam_write kmer_check                      # (whole_genome only for the bench-based notes)
# minibwa, the version of every comparison
git clone https://github.com/lh3/minibwa && (cd minibwa && git checkout c07de5c && make); export MINIBWA=$PWD/minibwa/minibwa
# samtools 1.24 (R4, R7 only): tags 1.24 of github.com/samtools/htslib and samtools
(cd htslib && autoreconf -i && ./configure --disable-libcurl --disable-gcs --disable-s3 --disable-plugins && make -j4)
(cd samtools && autoreconf -i && ./configure --with-htslib=../htslib --without-curses && make -j4); export SAMTOOLS=$PWD/samtools/samtools
```
Not timed separately: the release download and a clean `lake build` (the first build on the author's box finished within about 45 minutes, in parallel with the download).
Release assets (names): `genome.fa.partaa/ab`, `shim.idx.partaa/ab/ac`, `shim.idx.chromosomes`, `mb.l2b`, `mb.mbw.partaa..ad`, `hg002_200k_R{1,2}.fq`, `hg002_1M_R{1,2}.fq`,
`novaseq_200k_R{1,2}.fq`, `hg38_mason_R{1,2}.fq`, `hg38_low_R{1,2}.fq`, `MANIFEST`, `SHA256`. The release's `shim.idx` was built at `f7ab094`; every later head loads it (REAL_VS_MINIBWA §5).

## Box-specific caveats (they decide how far a re-run can differ)
- **Index load is the noise.** The shim reads a 5.3 GB index into memory (`readBinFile`), minibwa's index is 7 GB, the box has 15 GB: the page cache is reclaimed and the shim's load of an
  empty FASTQ varied 1.6-44 s between runs on the author's box (THREADS_2026-11-02.md "Final proven head"; N32_KERNELS §4; my own runs 5-44 s). Timings therefore subtract an empty-FASTQ run made right before
  each full run. Wall differences under about 10 s are noise; **user+sys CPU is the steadier column** (run-to-run spread about +-10-20%, N32_KERNELS §4-5).
- **One tool at a time, nothing else running, `taskset -c 0-3`.** Interleaving the tools made it worse (N32 §4: "empty runs up to 500 s"). Use REPS >= 3 (a single repetition can give a negative minibwa map time).
- **SAM output is deterministic** (the same SAM for 2 and 4 threads and across runs: THREADS_2026-11-02.md "Fix"; I re-ran R3 (`hg38_low`), R4, R5 and the counts of R6 on the current head: identical to the notes). So the mapping, validation and proof numbers should reproduce exactly; only R1 and R2 timings have a spread.
- `speed.sh` uses the same subtraction for both tools (empty run). THREADS_2026-11-02.md instead subtracts minibwa's own "index loaded" log time and, for ours, the median of 12 empty runs; those numbers are not produced by `speed.sh`.

## R1 `speed.sh`
`bash Testing/repro/speed.sh novaseq_200k 6 4` (also `hg002_200k`, `hg38_mason`, `hg38_low`). Per tool: one warm-up empty run, then 6 x (empty run, full run); prints map wall, CPU (user+sys), end-to-end, the 6 individual values, and the line
`SET 4 threads: minibwa X s / ours Y s = Z.ZZx wall; CPU ...; end-to-end ...`. To compare a past head, `git checkout COMMIT && lake build lean-align` first (the claims name their commit).
Expected: see the claim table (RESULTS_2026-11-02.md section A). Time: about 2 x (1 + 2 x REPS) index loads and 2 x REPS full maps; NovaSeq 200k with REPS=3 took 3 min 59 s. Needs a few GB of free disk for the SAM it writes (a full disk makes `lean-align` die with "no space left on device" and the script then exits without output).

## R2 `ir.sh`
`bash Testing/repro/ir.sh .lake/build/bin/lean-align novaseq_200k 2000` prints callgrind's `Collected : N` (index load included, as in N32/N33). Deterministic; build both commits, copy each `lean-align`, run twice, compare.

## R3 `mapping.sh`, R6 `real_rescore.sh`
`mapping.sh` runs the shim (4 cores) and minibwa (`-t 4`) and prints sections (1)-(2) of `output_vs_minibwa.py`. `real_rescore.sh` additionally runs `Testing/fuzz/real_vs_minibwa.py` and `rescore_unique.py` and prints the
`[ALARMING]` count and `BUG? count`. Expected values are in the claim tables.

## R4 `Testing/unique/run.sh`
Generates the 4 Mb 15-mer-unique genome (seed 1), runs the proved checker (`kmer_check`, expect `PASS`), builds both indexes, maps two simulated sets and compares with minibwa, samtools and the BAM writer. Last line: `ALL UNIQUE-GENOME CHECKS PASSED`; per-set detail in `OUT/compare_sim.txt`, `compare_sim2.txt`.

## R5 `fuzz_audit.sh`
Testing/fuzz/README.md's four commands per seed and mode (`sim_pairs.py hg38.1l.fa ... 10000 MODE SEED`, shim, minibwa, `compare_sam.py`), then `audit_vs_minibwa.py`: rules A-D must print `0`, `info C` is the number of scorable pairs. The one-line genome `hg38.1l.fa` is made once (about 50 s).

## R7 SAM/BAM output checks
`sh Testing/scripts/fuzz_ci.sh`: 2,917 pairs on a generated 2 Mb genome; `VIOLATIONS: none`; two `--xfail` rules print `XFAIL` while the placeholder and short-mate problems exist. `FUZZ=1 sh Testing/scripts/CI_check.sh` runs it inside the CI check. The hg38 version is `output_fuzz.sh` (needs samtools).

## R8, R9 proofs
`proofs.sh` runs `CI_check.sh` and prints `ok N theorems, standard axioms only`, the axioms of `Spec.alignPairs_correct` and `Spec.alignPairs_end_to_end`, and the `AuditAlignPairs` summary. `statements.sh A B` diffs the theorem texts and says whether `Spec/Alignment.lean`, `Mapping.lean`, `Aligner.lean` changed:
the theorem text can stay the same while a definition it uses changes (it did: `PairAnswer.Correct` gained the `junkScore` clause), so read both parts of its output.
