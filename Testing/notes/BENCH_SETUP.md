# Bench setup: reproducing the timing and fuzz runs on a fresh box

This is the setup behind the numbers in MINIBWA_BENCH.md and in the S-D messages of 2026-11-03 to 2026-11-10
(headline, core scaling, spec/fastq-bytes, 027ef1e, and the a2f75c8 SAM fuzz).
The scripts are in `Testing/notes/bench/`. Throughout, `S` is a scratch directory and `REPO` is the festive checkout.

## 0. Box and disk

- The runs used a 4-core cloud box with 16 GB RAM, Linux, and a 252 GB volume with only ~40 GB usable.
  Disk is the binding limit, so check `df` before every download.
- Peak usage: ic.idx 5.3 GB + minibwa index (mb.l2b + mb.mbw) 7 GB + genome.fa 3.2 GB.
  On top of that: 5M sets 2.4 GB gz, 1M plain sets 1.8 GB, and hg38.1l.fa 3.1 GB (fuzz_audit, regenerated as needed).
  Each lake build tree is ~0.6 GB.
- Lean: elan with toolchain `leanprover/lean4:v4.35.0`. A worktree may need `elan override set lean435`,
  and `export PATH=$HOME/.elan/bin:$PATH`.

## 1. Data

**Bench release** (genome, minibwa index, 200k sets).
Use `sh Testing/data/fetch_release.sh bench-release`; see Testing/repro/README.md for the disk and SHA-256 caveats.
On a tight disk, fetch asset by asset: append each part in place, skip hg002, then run `sha256sum -c`. The loop:

    gh api repos/rowancallahan/lean-align/releases/tags/bench-release --jq '.assets[] | "\(.id) \(.name)"' |
      grep -v hg002 | sort -k2 | while read id name; do
        case $name in *.part??) out=$dst/${name%.part??};; *) out=$dst/$name; : > $out;; esac
        gh api -H "Accept: application/octet-stream" repos/rowancallahan/lean-align/releases/assets/$id >> $out; done

What this gives you:
- `genome.fa`: hg38.upper.fa, 3.16 GB.
- `mb.l2b` and `mb.mbw`: the minibwa c07de5c index of the same genome, so no `minibwa index` run is needed.
- `shim.idx.chromosomes`.
- The 200k sets.

Do NOT use the release's `shim.idx`: its format predates 54196c2, and an old index silently maps nothing (verify step 2).

**Real reads.** These are the first 5M pairs of each file, streamed and cut with `head`, and recompressed.
- bit.ly, ftp-trace.ncbi and ebi.ac.uk were refused by the network policy.
- These two hosts worked.

      G=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
      A=https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads/D1_S1_L001
      mkdir -p $S/big; cd $S/big
      for m in 1 2; do (curl -sS $G.R$m.fastq.gz | gunzip -c 2>/dev/null | head -n 20000000 | gzip > nova5m_R$m.fq.gz) & done
      for m in 1 2; do (curl -sS ${A}_R${m}_001.fastq.gz | gunzip -c 2>/dev/null | head -n 20000000 | gzip > hiseq5m_R$m.fq.gz) & done
      wait

- NovaSeq is 2×151 (1.510 Gbp per 5M pairs). HiSeq is 2×250 with variable lengths (2.482 Gbp per 5M).
- The read names of R1 and R2 are in step. Check this with `paste <(zcat R1|awk 'NR%4==1') <(zcat R2|awk 'NR%4==1') | head`.
- Plain 1M sets (the first 1M pairs):

      mkdir -p $S/p1m
      for m in 1 2; do zcat $S/big/nova5m_R$m.fq.gz  | head -n 4000000 > $S/p1m/n1m_R$m.fq; done   # 369 MB each
      for m in 1 2; do zcat $S/big/hiseq5m_R$m.fq.gz | head -n 4000000 > $S/p1m/h1m_R$m.fq; done   # 553 MB each

## 2. minibwa (c07de5c, lh3)

    git clone https://github.com/lh3/minibwa $S/minibwa && cd $S/minibwa && git checkout c07de5c && make -j2
    mkdir -p $S/bin; cp minibwa $S/bin/minibwa

- Index: the release's `Testing/data/prebuilt/mb` (`mb.l2b` + `mb.mbw`), so `MBINDEX=$REPO/Testing/data/prebuilt/mb`.
- Use an absolute path. A worktree without `Testing/data/prebuilt` makes minibwa abort with "failed to load the index".
- Its load time is printed on stderr: `[M::...::LOAD_WALL*CPU_RATIO] index loaded`.

## 3. Our hg38 index (ic.idx)

Build it with the code you will time. The index format is part of the code, so rebuild after any index-format change.

    cd $REPO && lake build lean-align
    .lake/build/bin/lean-align build Testing/data/prebuilt/genome.fa $S/idx/ic.idx    # ~30 min, ~14 GB RAM; 5,338,015,764 B

- The current ic.idx was built from 54196c2's format. Every build since then up to festive be317e9 reads it unchanged.
- Check it with verify step 2 (2,000 NovaSeq pairs must be ≥85% mapped), or `INDEX=$S/idx/ic.idx STEPS=2 bash Testing/verify.sh OUT`.

## 4. Builds under test

- `lake build lean-align`, then copy `.lake/build/bin/lean-align` to `$S/bin/<label>`. Keep the binaries; worktrees get reused.
- To build a patch locally: `git apply Testing/notes/<x>.patch`, then `lake build lean-align`.
  The full `lake build` may fail on proofs the patch has not adapted yet.
- bpB is byte_pipeline.patch on festive fb986a6. It ran with `PIPE_B=1`, and festive 027ef1e and later have variant B built in.
- Check SAM equality by md5. Write the SAM to a FIFO read by `md5sum`, so no SAM file lands on disk:

      mkfifo $S/fifo/o; md5sum < $S/fifo/o > $S/md5.txt & $BIN map $I R1 R2 $S/fifo/o 100 1000; wait

- Reference md5s (columns-identical across festive 1ea07b3 … 027ef1e and bpB):

  | Set | md5 |
  |---|---|
  | n1m | 24329625d6347ac345048a4c9e3cc877 |
  | h1m | f680742c4f26ef89f7956b3fc2dad989 |
  | nova5m | 38b566e50a2623fae08645fe8d30719c |
  | hiseq5m | 6c5e7ae194f2926a4b19b562b24a84f5 |

## 5. Timing method (the standard since 2026-11-03)

- **Cores.** 4 threads, `taskset -c 0-3` on every run. Ours uses all cores by itself; minibwa gets `-t 4`.
- **Output.** SAM goes to `/dev/null` for both tools. Arguments for ours: `map INDEX R1 R2 /dev/null 100 1000`.
- **Page cache, other tool.** Before a tool's group of runs, drop the other tool's index from the page cache:

      python3 -c "import os,sys
      for f in sys.argv[1:]:
          fd=os.open(f,os.O_RDONLY); os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED); os.close(fd)" FILES

- **Page cache, own files.** Before each run, warm the tool's own index and the plain inputs with `cat FILES > /dev/null`.
- **Index load is measured inside the run.** A separate empty run sees a different page-cache state and gave negative map times.
  - Ours: `Testing/scripts/timed_load.py LABEL BIN map INDEX ...`. Load is the time until `/proc/PID/io` rchar reaches
    the index size, since Main reads the whole index before any FASTQ. It prints wall, cpu (user+sys), load and loadcpu.
  - minibwa: `Testing/notes/bench/phases.py LABEL 99999999999 /dev/null 0 -- sh -c "minibwa map -t 4 MB R1 R2 > /dev/null 2> mb.err"`.
    It gives total wall and user/sys. Take load = LOAD_WALL and loadcpu = LOAD_WALL × CPU_RATIO from the `index loaded` line in mb.err.
- **Reported quantities.**

  | Quantity | Definition |
  |---|---|
  | map | wall − load |
  | CPU | user + sys − loadcpu |
  | util | CPU / (map × 4) |
  | Gbp/hr | bases / map × 3600 |
  | Gbp per core-hour | bases / whole-run (user + sys) × 3600 |

  Whole-run wall is also reported when asked.
- **Repeats.** Three per build. The build order is rotated per rep (rep 2 reversed), and the median per quantity is reported.
  Always send the per-rep lines: a cold first load and the occasional slow rep (e.g. hiseq5m 184 vs 131 s) show up there.
- **Inputs.**
  - Plain files (`$S/p1m/*.fq`) are the headline.
  - 5M via zcat FIFO: `mkfifo a b; zcat X_R1.fq.gz > a & zcat X_R2.fq.gz > b &`, then map `a b`.
  - zcat costs about 4 s CPU per 1M pairs, which lowers util on 4 cores (~0.87–0.91 vs 0.95–0.97 for plain files).
- **Scripts.**
  - `bench/compare.sh` runs builds against each other, ours only. Set `BINS="label:bin ..."`; the label bpB gets `PIPE_B=1`.
    It prints a TIME line per run and an MD5 line per build and set.
  - `bench/headline.sh` runs ours (`OURS=bin`) against minibwa on n1m/h1m plain and the 5M FIFO sets.
  - Compute the medians from the TIME / PHASES / MBLOAD lines with a short regex script; MBLOAD gives minibwa's load and ratio.
- **Core scaling.** The same method at `taskset -c 0-(c-1)` for c = 1, 2, 4, with minibwa `-t c`. Report speedup vs c=1 and util per c.

## 6. Fuzz and SAM checks

- **hg38 fuzz audit:**

      cd $REPO && STEPS=3 INDEX=$S/idx/ic.idx MBINDEX=$REPO/Testing/data/prebuilt/mb MINIBWA=$S/bin/minibwa bash Testing/verify.sh $S/vfy

  It writes `$S/vfy/fuzz/hg38.1l.fa` (3.1 GB) if missing. HARD A–D must be 0 in all 9 cells (3 seeds × mason/low/high).
- **Tiny-genome fuzz:** `sh Testing/scripts/fuzz_ci.sh`; it must print `VIOLATIONS: none`.
  To compare two builds, run the same steps with a persistent directory and `cmp` the SAMs.
- **samtools** via pysam (no samtools binary needed). PyPI must go through the proxy:

      NO_PROXY=localhost,127.0.0.1 no_proxy=localhost,127.0.0.1 pip install --break-system-packages pysam
      SAMTOOLS="python3 Testing/scripts/samtools_pysam.py"

  The wrapper raises SamtoolsError when its reader closes the pipe early (e.g. `cmp` at the first difference).
  Write `view` output to a file, or read it to the end.
- **Unique genome (verify step 4 / `Testing/unique/run.sh`).**
  - The `bam_write` lines fail to build since the FASTQ spec change: BamWrite.lean uses the old record fields and `samName`.
    Skip them.
  - `bench/uniq_text.sh` runs the rest and compares columns 1–11 on the SAM text.
  - Columns 1–11 are NOT identical to minibwa, and this is expected:
    - The TruSeq cut hits 5 adapter-like loci in the random genome plus chance 6–12 letter tail matches (~3.3e-4 per mate).
    - A pair with a mate trimmed away is reported unmapped.
    - Pairs with one short mate are not proved unique (MAPQ 0).
  - `bench/writetrim.py DIR SET` writes our trimmed reads, using a Python model of trimBytes that matches every kept length.
    With those reads given to minibwa, columns 1–11 match except MAPQ on the not-proved pairs, plus one 30-letter mate that minibwa leaves unmapped.
  - `bench/fieldcmp.py OURS MB LABEL` compares field by field on pairs where both tools give the same proper pair.
