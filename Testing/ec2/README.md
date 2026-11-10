# 16- and 32-core test against minibwa

Four files to read, 180 lines in total:

| file | what it does |
|---|---|
| `setup.sh` | builds lean-align and minibwa (c07de5c), fetches data, builds both indexes |
| `bench.py` | times ONE run of ONE tool; the docstring says exactly what is measured |
| `compare.py` | reads our SAM and minibwa's with pysam and counts pairs that match |
| `run.sh` | calls `bench.py` for each tool and thread count, then `compare.py` |
| `drop_adapter_pairs.py` | tiny mode only: leaves out simulated pairs our adapter rule would cut |

## Laptop (about 1 minute after the build)

    bash Testing/ec2/setup.sh tiny ~/la-tiny
    bash Testing/ec2/run.sh tiny ~/la-tiny

A generated 4 Mb genome in which every 15-letter word is unique, 200k simulated pairs. Passes when the last
line is `IDENTICAL: columns 1-11 of every record`. Needs git, make, a C compiler, python3, curl.
Not tested on macOS: there is no core pinning there, so tiny timings on a Mac only show the script runs.

## AWS

1. Launch `c7a.8xlarge`, Ubuntu 24.04, 150 GB gp3 disk. 32 vCPU = 32 real cores (no hyper-threads), 64 GB.
   Bare metal with the same core type is `c7a.metal-48xl` (192 cores); the scripts pin to cores 0-31 either way.
2. On the machine:

       git clone https://github.com/rowancallahan/lean-align && cd lean-align
       git checkout claude/festive-fermi-mf9mo6
       bash Testing/ec2/setup.sh full ~/bench        # hg38, 40M NovaSeq pairs, both indexes
       bash Testing/ec2/run.sh full ~/bench          # 16 and 32 threads, 3 runs each, both tools

3. Copy back `~/bench/timing.tsv` and `~/bench/compare.txt`, then terminate the instance.

Knobs: `PAIRS=100000000 bash ... setup.sh` for more reads (the whole 30x file is about 360M pairs; use a
300 GB disk). `THREADS="8 16 32" REPS=1 bash ... run.sh`.

## What the numbers mean

- Reads: the minibwa paper's WGS set (HG002 NovaSeq 30x, 2x151), its first PAIRS pairs, re-gzipped.
- Both tools get the reads from `gzip -dc` through a pipe, and their output is thrown away.
- Everything (aligner and gzips) is pinned to cores 0..THREADS-1. minibwa gets `-t THREADS`.
- wall includes index load, with the index already in the page cache.
- The paper's Fig. 3 number to compare with is Gbp/hr at 32 threads: minibwa 135.82, strobealign 149.96,
  on two Xeon Gold 6130 (32 cores, 64 hyper-threads, not pinned), whole 30x file.

## Differences from the paper's setup
- Different CPU, and pinned to 32 cores instead of 32 threads on a 64-thread machine.
- 40M pairs by default, not the whole file, so index load is a larger share of the wall time.
- strobealign is not run by these scripts.
