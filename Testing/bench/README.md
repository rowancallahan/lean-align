# Testing: everything a person has to read is in this folder

| file | what it does |
|---|---|
| `bench.sh` | the benchmark, top to bottom: tools, data, indexes, timing, agreement with minibwa, results, power off |
| `verify.sh` | is this checkout proved and does it give the right output; `PARANOID=1` for the slow, thorough checks |
| `time_one.py` | times one run of one tool (called by both scripts) |
| `compare.py` | counts read pairs on which our SAM and minibwa's agree, and checks every record of our SAM for basic sanity |
| `tiny_data.py` | makes a small genome and read pairs with a known answer, and checks that our SAM puts every mate there |

`extra/` holds three longer checks kept for completeness (`mirror_check.py`, `sam_check.py`, `fuzz_hg38.py`); you do not
need to read them to trust the benchmark. `comparator/` holds the `lake comparator` settings (one file per Spec file).

The scripts call each other, `lake`, the two aligners and standard tools. Nothing else in the repository.

## Laptop (minutes after the first build)

    bash Testing/bench/verify.sh ~/la-verify

Last line `VERIFY PASSED`: frozen Spec hashes, full `lake build`, the seven main theorems on the three standard
axioms, the trimmer contract hash, and the small genome mapped at the true positions and identically to minibwa in columns 1-11
with every record of our SAM sane.

## Server (Ubuntu 24.04, 150 GB disk, shutdown behaviour Stop)

    git clone https://github.com/rowancallahan/lean-align && cd lean-align
    VERIFY=1 nohup bash Testing/bench/bench.sh full ~/bench > ~/bench.out 2>&1 &
    tail -f ~/bench/all.log

It times both tools at a quarter, at half and at all the cores, three runs each, on the first 40M pairs of the minibwa paper's
NovaSeq reads; compares them on 1M pairs; with `VERIFY=1` runs `PARANOID=1 verify.sh` (clean rebuild, index rebuilt
and compared, same output at 1 and all threads, mirror check, hg38 fuzz, `lake check --paranoid`); packs
`~/bench/results.tgz`; powers the machine off, also when a step fails, and after 12 hours at the latest.
Next day: start the instance, copy `results.tgz` off, terminate it.

The previous test scripts (`Testing/ec2/`, `Testing/verify.sh`, `CI_check.sh`, ...) are on branch `archive/testing-old`.
