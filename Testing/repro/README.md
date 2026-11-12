# Recreating the numbers of `Testing/notes/RESULTS_2026-11-02.md`

Index of recipes (R-ids are used in the results page). Each script prints the number it is about; "measured here" is the wall time of the author's run
(4 vCPU, 15 GB, current head `ab3aacd` + notes) and is stated only where it was actually timed.

| id | what | command (from the repo root, after the setup below) | measured here |
|---|---|---|---|
| R1 | speed vs minibwa (CPU, wall, end-to-end) | `sh Testing/scripts/headline.sh OUT 'k:$S/lean-align mbdef:$MINIBWA' 'novaseq:novaseq_200k'` then `python3 -I Testing/scripts/ab_med.py OUT/LOG` (see R1 below) | not re-timed here (REPEAT=3 x 2 tools, 6+ min) |
| R2 | instruction counts (callgrind) | `bash Testing/repro/ir.sh BINARY SET [PAIRS=2000]` | not timed (200 pairs ran to completion) |
| R3 | mapped / unique / agreement with minibwa | `bash Testing/repro/mapping.sh OUT hg38_mason hg38_low hg002_200k novaseq_200k` | `hg38_low`: 1 min 45 s |
| R4 | unique-genome exact match | `bash Testing/unique/run.sh OUT` | 5 min 9 s |
| R5 | hg38 fuzz audits (rules A-D print `HARD ...: 0`; rule E is the `info H` lines), 3 seeds x 3 modes | `bash Testing/repro/fuzz_audit.sh OUT` | 4 min 25 s (+ about 50 s once for the one-line genome) |
| R6 | real-data comparison and rescoring | `bash Testing/repro/real_rescore.sh OUT` | not timed (several minutes) |
| R7 | SAM/BAM output checks | `sh Testing/scripts/fuzz_ci.sh` (tiny genome) and `bash Testing/scripts/output_fuzz.sh OUT SET...` (hg38) | `fuzz_ci.sh`: 10-16 s |
| R8 | proofs: CI line, axioms, audit | `bash Testing/repro/proofs.sh` | 1 min 39 s (cached build) |
| R9 | theorem statements at two commits | `bash Testing/repro/statements.sh REV_A REV_B` | seconds |

## Setup from a fresh checkout (once)
**Disk: have about 40 GB free.** The release is 17 GB; `fetch_release.sh` joins the parts before deleting them (peak about 2x), `hg38.1l.fa` (R5, R6) is another 3 GB, the SAMs of R1/R3 add a few GB. On a 252 GB volume with 39 GB free the check ran out of disk three times (`No space left on device` truncates a part silently). Download assets one at a time and delete each part after appending it, or check `df` first.
**Check every asset's size and SHA-256.** `gh api ... releases/assets/ID > file` was cut short twice (`mb.mbw.partab` 1.57 of 1.99 GB, `genome.fa.partab`) with exit 0; `fetch_release.sh` catches it through `shasum -c`, a hand download does not, so compare sizes with `gh api repos/rowancallahan/lean-align/releases/tags/bench-release --jq '.assets[]|"\(.name) \(.size)"'`.

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
  empty FASTQ varied 1.6-44 s between runs on the author's box (THREADS_2026-11-02.md "Final proven head"; N32_KERNELS §4; my own runs 5-44 s). The N32 §5 timings subtract an empty-FASTQ run made right before
  each full run; `headline.sh` (R1) instead measures the load inside the run. Wall differences under about 10 s are noise; **user+sys CPU is the steadier column** (run-to-run spread about +-10-20%, N32_KERNELS §4-5).
- **One tool at a time, nothing else running, `taskset -c 0-3`.** Interleaving the tools made it worse (N32 §4: "empty runs up to 500 s"). Use REPS >= 3 (a single repetition can give a negative minibwa map time).
- **SAM output is deterministic** (the same SAM for 2 and 4 threads and across runs: THREADS_2026-11-02.md "Fix"; I re-ran R3 (`hg38_low`), R4, R5 and the counts of R6 on the current head: identical to the notes). So the mapping, validation and proof numbers should reproduce exactly; only R1 and R2 timings have a spread.
- Methods differ between notes: N32 §5/N33 §5 subtract an empty-FASTQ run (6 reps, median); THREADS_2026-11-02 subtracts minibwa's own "index loaded" log time; N32_REPEATS §7 (`headline.sh`) measures the shim's index load **inside the run** (`timed_load.py`, /proc rchar until the index-file size is read) and minibwa's from its log. Only the last is what R1 runs; A1-A6 of the results page are the older empty-run method.

## R1 `headline.sh` (kept instead of my earlier `speed.sh`, which implemented the N32 §5 empty-run subtraction)
Exact invocations and numbers: `Testing/notes/N32_REPEATS.md` §7 (round on e384063: `sh Testing/scripts/headline.sh OUT 'k:$S/v.k mbdef:$S/minibwa' 'novaseq:novaseq_200k'`, likewise `hg002_200k`, `hg38_mason`, `hg38_low`; envs REPEAT=3, THREADS=4, INDEX, INDEX_MB, READS; then `python3 -I Testing/scripts/ab_med.py LOG`). It drops page caches, `cat`s the index before each run, pins `taskset -c 0-3`, and reports load-subtracted median wall/CPU and end-to-end.
Caveat: the `ab_med.py` docstring still says "empty-FASTQ run" for ours; the code uses the in-run load from `timed_load.py`. To compare a past head, `git checkout COMMIT && lake build lean-align` first. Needs free disk for the SAMs (a full disk makes `lean-align` die with "no space left on device").

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
