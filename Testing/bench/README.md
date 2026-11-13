# Testing: everything a person has to read is in this folder

| file | what it does |
|---|---|
| `bench.sh` | the benchmark, top to bottom: tools, data, indexes, timing, agreement with minibwa, results, power off |
| `verify.sh` | is this checkout proved and does it give the right output; `PARANOID=1` for the slow, thorough checks |
| `time_one.py` | times one run of one tool (called by both scripts) |
| `compare.py` | counts read pairs on which our SAM and minibwa's agree |
| `tiny_data.py` | makes a small genome and read pairs with a known answer |
| `mirror_check.py` | the copies of the Spec in `Proofs/` say the same as `Spec/`; no forbidden words |
| `fuzz_hg38.py` | simulated hg38 pairs through both tools; none of our claims may be false |
| `sam_check.py` | every record of our SAM is well formed and its letters come from the input reads |
| `comparator/` | `lake comparator` settings: each `Proofs/` file states the same theorems as its `Spec/` file (untested) |

The scripts call each other, `lake`, the two aligners and standard tools. Nothing else in the repository.

## Laptop (minutes after the first build)

    bash Testing/bench/verify.sh ~/la-verify

Last line `VERIFY PASSED`: frozen Spec hashes, full `lake build`, the seven main theorems on the three standard
axioms, the small genome mapped identically to minibwa in columns 1-11, and every record of that SAM well formed.

## Server (Ubuntu 24.04, 150 GB disk, shutdown behaviour Stop)

    git clone https://github.com/rowancallahan/lean-align && cd lean-align
    VERIFY=1 nohup bash Testing/bench/bench.sh full ~/bench > ~/bench.out 2>&1 &
    tail -f ~/bench/all.log

It times both tools at half and at all the cores, three runs each, on the first 40M pairs of the minibwa paper's
NovaSeq reads; compares them on 1M pairs; with `VERIFY=1` runs `PARANOID=1 verify.sh` (clean rebuild, index rebuilt
and compared, same output at 1 and all threads, mirror check, SAM check of the 1M pairs, hg38 fuzz, the kernel
certificates, `lake check --paranoid`); packs
`~/bench/results.tgz`; powers the machine off, also when a step fails, and after 12 hours at the latest.
Next day: start the instance, copy `results.tgz` off, terminate it.

## Not covered here

These were in the old scripts and are dropped:
- a generated genome with repeats and runs of N (all simulated reads here are from N-free stretches);
- about 800 edge-case read pairs (1-101 or 400-1000 letters, all-N, bad qualities, adapters, mates trimmed away, odd mate placements);
- FASTQ format cases (CRLF, no final newline, reads over 1000 letters); the FASTQ parser is covered by the proved `parse_correct`.

The previous test scripts (`Testing/ec2/`, `Testing/verify.sh`, `CI_check.sh`, ...) are on branch `archive/testing-old`.
