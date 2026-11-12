# 16- and 32-core test against minibwa

Five files to read, about 200 lines in total:

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

## Unattended run that powers the machine off
    nohup bash Testing/ec2/all.sh full ~/bench > ~/all.out 2>&1 &
Runs setup, timing and agreement, packs `~/bench/results.tgz` (all.log, timing.tsv, compare.txt) and then runs
`sudo shutdown -h now`, also when a step fails. `VERIFY=1` adds `Testing/verify.sh`. `NO_SHUTDOWN=1` keeps it on.
- In the EC2 launch settings choose shutdown behaviour **Stop** (not Terminate): the disk and results.tgz are kept.
  A stopped instance costs only its disk. Start it again later, `scp` results.tgz off, then terminate it.
- `nohup ... &` keeps it running after you log out. Watch progress with `tail -f ~/bench/all.log`.

## What the numbers mean

- Reads: the minibwa paper's WGS set (HG002 NovaSeq 30x, 2x151), its first PAIRS pairs, re-gzipped.
- Both tools get the reads from `gzip -dc` through a pipe, and their output is thrown away.
- Everything (aligner and gzips) is pinned to cores 0..THREADS-1. minibwa gets `-t THREADS`.
- wall includes index load, with the index already in the page cache.
- The paper's Fig. 3 number to compare with is Gbp/hr at 32 threads: minibwa 135.82, strobealign 149.96,
  on two Xeon Gold 6130 (32 cores, 64 hyper-threads, not pinned), whole 30x file.

## What to expect and what to try at 16-32 threads
- Leave transparent huge pages at the system default (`madvise` or `always`). With `never`, runs are 12-17% slower.
- Index build needs about 14 GB of memory (measured peak 13.84 GB); the suggested instances have plenty.
- Estimated ceilings from 4-core measurements: gunzip of the two files near 400 Gbp/hr; the single reader loop near
  365-450 Gbp/hr. If wall time at 32 threads falls well short of CPU time / 32, try in this order: `rapidgzip` in
  `bench.py`, then branch `fix/cut-tasks-2` (proved, same SAM; no gain at 4 cores, slightly slower on HiSeq there).
- Bigger pipes were tested (branch `fix/ec2-pipes`, `PIPE_BYTES`) and gave no gain.

## Differences from the paper's setup
- Different CPU, and pinned to 32 cores instead of 32 threads on a 64-thread machine.
- 40M pairs by default, not the whole file, so index load is a larger share of the wall time.
- strobealign is not run by these scripts.

## Verify

`Testing/verify.sh` (proofs, index freshness, hg38 fuzz vs minibwa, unique genome == minibwa, speed) on the
machine after `setup.sh full WORKDIR`:

    W=~/bench
    sudo apt-get install -y samtools                       # step 4 only
    mkdir -p $W/sets && for r in 1 2; do gzip -dc $W/cmp_R$r.fq.gz | head -n 800000 > $W/sets/nova200k_R$r.fq; done
    P=$W/sets SETS=nova200k INDEX=$W/ours.idx MBINDEX=$W/mb MINIBWA=$W/minibwa/minibwa SAMTOOLS=samtools \
      GENOME=$W/genome.fa THREADS=32 bash Testing/verify.sh $W/verify

- step 2 maps the first 2,000 pairs of the first set in SETS; step 5 times every set in SETS.
- step 3 writes a one-line copy of GENOME (about 3.2 GB) into $W/verify/fuzz.
- step 4 builds `kmer_check` and `bam_write`, its own 4 Mb genome and both indexes, and leaves out the simulated
  pairs our adapter cut trims (about 170 of 199,880 and 370 of 470,298; minibwa does not cut).
