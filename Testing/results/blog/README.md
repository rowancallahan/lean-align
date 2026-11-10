# Results for the README and blog: how every number and figure was made

Everything here was made on one 4-core box unless a row says otherwise. Data are in `data/`, figures in `figs/`
(`.svg` and `.png`), tables in `RESULTS.md`. Rerun with `python3 make_figs.py` and `python3 make_tables.py`
(matplotlib only). The scripts read `data/*.tsv` and skip NA rows; nothing is hard-coded.

## Files

| file | content |
|---|---|
| `data/runs.tsv` | every timing run: 5M gz runs, streamed runs, whole lanes |
| `data/slow_jobs.tsv` | jobs longer than 5 s and idle cores, before and after |
| `data/slow_pairs.tsv` | the slowest single pairs, mapped alone on 1 core |
| `data/slow_pairs_stream.tsv` | the 36 slowest pairs of the HiSeq lane, before and after, same pair indexes |
| `data/accuracy.tsv`, `data/roc.tsv` | accuracy and uniqueness against minibwa (copied from `Testing/notes/UNIQUE_VS_MINIBWA.md` and `figures_draft/roc.tsv`) |
| `data/paper_perf.tsv` | the minibwa paper's Fig. 3 numbers, as published |
| `scripts/` | `util/` stream harness and trace analysis, `ec2/` 16/32-core scripts, `sim_pairs.py`, `roc_from_sams.py` |

## Box and common method

- Box: 4 cores (Intel Xeon @ 2.10 GHz, 1 thread per core), 15 GB RAM, Linux. Everything runs on those 4 cores:
  the aligner, the decompressors and the output sink (`os.sched_setaffinity` / `taskset -c 0-3`). hg38, one index per tool.
- lean-align index: `lean-align build hg38.upper.fa ic.idx` (5,338,015,764 bytes, built once with the code under test; the
  format has not changed between the builds compared). minibwa c07de5c with its own index.
- Commits: `64ae73f` = before (jobs of 16000 pairs, 8 in flight); `351301d` = first slow-pair fix; `f465a57` = merged build
  (4000-pair jobs, 32 in flight, slow-pair fixes). `e96862d` = older build used in the 5M gz rows.
- Output: the new `Main` writes `OUT.tmp` and renames it, so `/dev/null` cannot be the output. The sink is a FIFO at `OUT.tmp`
  drained by `cat > /dev/null` (md5 sink where marked).
- Time: `wall_s` = start to exit. `map_s` = wall minus the index load, measured inside the run (the load ends when the
  process has read as many bytes as the index file). `cpu_s` = user + system CPU of lean-align from the kernel (`wait4`),
  with the CPU used during the index load subtracted in the lane rows. Peak memory = `ru_maxrss` of lean-align (`wait4`).
- Rates: Gbp/hr = letters in both read files / map_s * 3600. Gbp/core-hr = the same letters / cpu_s * 3600 (aligner CPU only).
  Exact letter counts: NovaSeq 40M pairs = 12.08 Gbp (all reads 151); HiSeq lane = 16.835 Gbp (33,916,091 pairs, counted
  with `awk` on the stream).
- Repetitions: stated per row in `runs.tsv` (`reps`). The lane runs are single runs. Run-to-run spread on this box is about 2 percent.

## Per figure and table

### (a) Speed at 4 threads, 5M pairs (`figs/a_speed_4threads`, table "Speed at 4 threads")
- Rows `gz5m` in `runs.tsv`. Reads: the first 5M pairs of each file, from the NovaSeq and HiSeq URLs below, recompressed to gz.
  Both reads files are fed through `zcat` FIFOs to the aligner; the output is discarded; medians of 3 runs.
- Method and scripts: `Testing/notes/BENCH_SETUP.md` section 5 (branch `notes/bench-setup`: `taskset -c 0-3`, index load
  measured inside the run, `bench/compare.sh`, `bench/headline.sh`).
- Commits: `e96862d` (before) and `f465a57`. minibwa c07de5c rows are from an earlier session and have only wall time
  (`TO RE-MEASURE`); the figure shows an empty slot for them.
- These rows come from the timing box; I did not run them and did not re-check them against logs.

### (b) Peak memory (`figs/b_memory`)
- `peak_GB` of the streamed and lane rows. Lane rows: `ru_maxrss` of lean-align from my runs. The streamed rows come from the
  streaming box (not rechecked). lean-align uses 5.6 to 5.9 GB: the index is 5.3 GB. minibwa 8.8 GB is from the 20M streamed row.
- `peak_GB` of the 5M gz rows is `NA` (not recorded), so (b) uses the streamed and lane rows.

### (c) Throughput vs run size (`figs/c_throughput_vs_size`)
- Rows `stream` in `runs.tsv`: NovaSeq HG002, the first 10M, 20M and 40M pairs streamed from the network
  (`curl | gunzip`, no file on disk), output to a `cat` or md5 sink. These come from the streaming box; I did not re-check them.
- minibwa has one point (20M; resuming downloader, output to /dev/null). The 40M minibwa run is pending.
- "before" = 64ae73f-era build (trace commit f973b77). The 10M and 20M "before" runs and all "after" runs were single runs.

### (d) Slow jobs (`figs/d_slow_jobs`, table "Slow jobs"), (e2) slow pairs inside the lane (`figs/e2_slow_pairs_in_lane`)
- My runs, trace box (this 4-core box). One run each per cell.
- Data (streamed, nothing on disk). HiSeq: GIAB HG002 2x250, lane D1_S1_L001, the whole lane (33,916,091 pairs):

      A=https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads/D1_S1_L001
      ${A}_R1_001.fastq.gz  ${A}_R2_001.fastq.gz

  NovaSeq: the first 40M pairs of the HG002 30x PCR-free set used by the minibwa paper:

      G=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
      $G.R1.fastq.gz  $G.R2.fastq.gz

- Command (script `scripts/util/gzstream.py`, also on branch `exp/util-scripts`):

      NLINES=160000000 python3 gzstream.py LABEL BINARY URL_R1 URL_R2 new fifo      # NLINES = 4 x pairs; the lane ends by itself

  It starts `curl | gunzip -c | head -n NLINES > FIFO` per mate, the aligner, and a `cat` sink, all on cores 0-3.
- "Before" = `64ae73f` plus the trace commits `f973b77` (job and collect timestamps) and `d94d683` (every pair slower than 20 ms)
  from branch `exp/hol-trace`. "After" = `f465a57` with the same trace commits cherry-picked, as a local build (not pushed).
  The untraced `f465a57` NovaSeq run (771.7 s) is within 2 percent of the traced one (756.8 s), so the trace costs nothing measurable.
- Analysis: `scripts/util/slow.py TRACE 5` (jobs over 5 s, time with fewer than 4 jobs running), `scripts/util/pairs.py TRACE 1000`
  (pairs over 1 s; `PJ=4000` for the 4000-pair runs). "Ideal wall" = (aligner CPU + gunzip/curl CPU + sink CPU) / 4.
  `core_use_pipeline` = that same CPU / (map time * 4).
- Pair numbers are the same in both builds (job index * pairs per job + position in the job). Pair 2,538,239 of the lane is the
  `slow1` pair on branch `bench/slow-pairs`.
- The pair classes in `slow_pairs_stream.tsv` come from the trimmed mates: one letter repeated 20 or more times, or at most
  24 different 4-letter words, or a period of 8 or less matching in 90 percent of positions. Three pairs of the 36 matched none
  (35/35, 43/38 and 40/40 letters after trimming).
- Two untraced NovaSeq attempts failed because the network reset one mate's download (`curl: (56)`); the third is the one in
  the table. When one mate's stream stops early, lean-align keeps buffering the other mate (peak 9 to 14 GB, OOM kill once).

### (e) Slow pairs alone on one core (`figs/e_slow_pairs`)
- `slow_pairs.tsv`: single pairs (and 10 NovaSeq pairs together) mapped alone with the index loaded, 1 core, map seconds.
  Pairs: `bench/slow-pairs` branch (`Testing/notes/slow_pairs/`). Builds 64ae73f, 351301d, f465a57. From the timing box; not rechecked.
  The SAM output of the pairs is identical in the three builds (as reported when the rows were made).

### (f) Accuracy and uniqueness against minibwa (`figs/f_accuracy`, two tables)
- Source: `Testing/notes/UNIQUE_VS_MINIBWA.md`; numbers copied into `data/accuracy.tsv`.
- lean-align 027ef1e against minibwa c07de5c `map -t 4`, SAM written to files. Real reads: the first 200k pairs of the bench
  release's `novaseq_200k` and `hg002_200k` (HiSeq 2x250). Simulated reads: `scripts/sim_pairs.py mason|low|high`, seed 1,
  100k pairs each, from hg38.
- Scoring: a pair is proper if flag 0x2 is set on both mates. minibwa "unique" = MAPQ 60 on both mates. A simulated pair is
  correct if both mates start within 10 bp of the true start. Classes (unique / unknown / not proper) are our own tags (XU).
- This was measured before the slow-pair fixes. The fixes do not change the output (byte-identical SAM on the sets checked when
  the fixes were made, as reported by the person who made them), so these numbers are not re-measured on f465a57.
  1M-pair runs of this comparison were not done.

### (g) ROC on simulated reads (`figs/g_roc`)
- `data/roc.tsv` (from `Testing/notes/figures_draft/`, made by `scripts/roc_from_sams.py` from the SAMs of (f)). Per read, not per pair.
  Correct = same chromosome and the mapped and true intervals overlap by at least 10 percent (the paper's rule).
  x = reads mapped / all reads; y = correct / mapped. minibwa: one point per MAPQ threshold (60, 59, ... 0).
  lean-align: two points (MAPQ 60 = unique, and all mapped reads).
- Simulator vs the paper: the paper used mason v2.0.9 with `--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5`
  on GRCh38. Mason is not installed here. `sim_pairs.py` `mason` mode approximates those options (no variants; mismatch rate
  0.2/0.4/1.2 percent times 2.5 at start / 66 percent / end of the read; 1 bp indels at 0.005 percent per base; fragment
  N(300, 30)). `low` and `high` add haplotype variants (1 SNP per 1000 bp and 1 per 100 bp). They are our own models, not the paper's data.
- Measured on 027ef1e (see the note under (f)).

### (h) The paper's Fig. 3, WGS bars (`figs/h_paper_fig3_wgs`)
- `data/paper_perf.tsv`: `perf.tsv` of lh3/minibwa at c07de5c, WGS (HG002 NovaSeq 30x), 32 threads, two Xeon Gold 6130, as published.
- lean-align at 32 threads is not measured. The dashed slot is empty on purpose. A 16/32-core test is prepared in `scripts/ec2/`
  (`setup.sh`, `run.sh`; AWS c7a.8xlarge; its README explains the method and the differences from the paper).
- The 4-thread numbers in (a) to (c) are not comparable to the paper's 32-thread bars.

## What I changed in the transcribed rows

- Lane rows of `runs.tsv` (my runs): the values given as `wall_s` were the map seconds. `wall_s` is now the whole-run wall and
  `map_s` the map seconds; `cpu_s` is the map-phase CPU of lean-align; the HiSeq lane has 33,916,091 pairs (was 33,900,000);
  `Gbp_hr` and `Gbp_core_hr` were added. The traced `before` rows are build 64ae73f plus the trace commits.
- `slow_jobs.tsv`: all 20 numbers match my logs; unchanged.
- Rows I did not run (`gz5m`, `stream`, `slow_pairs.tsv`) are unchanged and not re-checked.

## Not measured, or older than f465a57

- minibwa on the whole HiSeq lane and at 40M NovaSeq (pending); minibwa 5M gz Gbp/hr and CPU (to re-measure).
- lean-align at 16 and 32 threads; any run with more than 4 cores.
- The 5M gz rows use `e96862d` and `f465a57`; the streamed "before" rows use a `64ae73f`-era build.
- Accuracy data (f, g) are from 027ef1e (before the slow-pair fixes). Real-read accuracy was only checked on 200k pairs.
- Peak memory for minibwa on the lanes.
