# How minibwa's own speed benchmark is set up (2026-11-03)

Source: the paper's LaTeX source in the minibwa clone (`tex/minibwa.tex`, `tex/perf.tsv`, `tex/plot-perf.gp`; github.com/lh3/minibwa
at c07de5c, arXiv 2606.15357). arxiv.org itself is blocked from this box (proxy 403), so the arXiv text was not read; the
`tex/` source is the paper. The quotes below are verbatim from `tex/minibwa.tex`.

## Setup, quoted

- Hardware: "All tools were run on a Linux server equipped with two Xeon Gold 6130 CPUs at 2.10GHz." (2 × 16 cores, 32
  cores / 64 hardware threads; RAM not stated)
- Threads: "32 CPU threads are specified for all mappers except for Winnowmap2 which automatically uses all available CPUs."
  (Fig. `fig:perf` caption)
- Output: "Alignment output is redirected to `/dev/null` except for Bismark which has to generate BAM files." (same caption)
- Settings: "We used the recommended setting of each tool."
- Reference: "Reads are aligned to GRCh38."
- Data: "We obtained multiple whole-genome real datasets (see Data Availability)". The WGS short reads are "HG002 NovaSeq
  short reads: https://bit.ly/hg002-baid-sr-30x" (the Baid et al. 30x set; read count and length not stated in the
  text. Other sets: HiFi, ONT R10, Hi-C, SBX (N50 243 bp), BS-seq SRR4235788.)
- Metric: speed in "Gbp/hr over 32 threads" (`plot-perf.gp` y-label) and "Peak memory (GB)". `perf.tsv` gives, per dataset
  and tool, speed (Gbp/hr) and peak memory (GB). WGS row: `minibwa 135.82 8.28`, `bwa-mem2 50.79 26.02`,
  `bwa-mem 30.37 9.77`, `strobealign 149.96 63.53`.
- Text: "Minibwa is about four times as fast as BWA-MEM and more than twice as fast as BWA-MEM2."
  "Across all six datasets, minibwa uses <20 GB memory at the peak".

## What is NOT stated

- Whether the index load is inside the timing. A whole 30x genome run (~90-100 Gbp at 135.8 Gbp/hr ≈ 40-45 min) makes
  a ~10-20 s load negligible either way.
- Wall vs CPU time: "Gbp/hr over 32 threads" is throughput per wall hour with 32 threads (wall time). CPU time is not
  reported.
- RAM size of the server; read count; whether FASTQ was gzipped (not stated).

## Compared with our method (`Testing/scripts/headline.sh`)

| | minibwa paper | ours |
|---|---|---|
| threads | 32 (2 × Xeon Gold 6130) | 4 (taskset 0-3, this box) |
| data | whole HG002 NovaSeq 30x (~90-100 Gbp) | 200k pairs of HG002 NovaSeq (2 × 151 bp, ~60 Mbp) and HiSeq 2 × 250 |
| output | SAM to `/dev/null` | SAM written to a file (both tools) |
| index load | not stated; negligible at 30x | subtracted (ours: measured in-run; minibwa: its "index loaded" log line) |
| metric | Gbp/hr (wall) | wall seconds, median of 3, plus user CPU |

Implication: at 200k pairs, the fixed costs (index load, thread start-up, first chunk) weigh far more than in the
paper's 30x runs. Load is subtracted for both tools, but per-chunk overheads are not. A longer run (≥ 1M pairs) is
closer to the paper's regime.
