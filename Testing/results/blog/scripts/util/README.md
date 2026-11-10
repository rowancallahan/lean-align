# Utilization / slow-job scripts (exp/util-scripts)

Streams (no disk): the first N lines of each gz file, through `curl | gunzip -c | head -n N > FIFO`.

    A=https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads/D1_S1_L001
    HISEQ R1: ${A}_R1_001.fastq.gz   R2: ${A}_R2_001.fastq.gz     (6.39 GB / 6.86 GB gz; the lane ends at 33.9M pairs = 135.6M lines)
    G=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
    NOVA   R1: $G.R1.fastq.gz        R2: $G.R2.fastq.gz           (25.7 GB / 26.6 GB gz; used the first 40M pairs)
    N lines = 4 * pairs; 160000000 = 40M pairs (HiSeq: head stops at the end of the lane)

## gzstream.py  (whole-pipeline harness)
    NLINES=160000000 python3 gzstream.py LABEL BIN URL_R1 URL_R2 new fifo
- LABEL: results `res/LABEL.trace` (the binary's stderr), the one-line summary on stdout. Paths are hard-coded to /home/user/S (edit S).
- `new` = the binary writes OUT.tmp then renames; the sink is a FIFO at OUT.tmp drained by `cat > /dev/null`.
- Everything on 4 cores: `os.sched_setaffinity({0,1,2,3})` is inherited by lean-align, both `curl|gunzip|head` pipelines and the sink.
- Index `idx/ic.idx` (built with `lean-align build genome.fa ic.idx`); load time = until /proc/PID/io rchar reaches the index size.
- Summary line: map (wall - load), lean_cpu (user+sys minus load CPU), zcat_cpu (= curl+gunzip+head pipelines, via wait4), sink_cpu, peakRSS_lean_MB, util_lean = lean_cpu/(map*4), util_all = (lean+zcat+sink)/(map*4).
- (gzrun.py is the same for local .gz files; gzan.py summarizes its per-thread samples.)
- To run another tool (e.g. minibwa) on the same stream, replace the `lean` Popen by your command reading FIFOs `a` and `b`.

## slow.py TRACE [thresh_s]   (hol-trace J lines)
Lists jobs longer than thresh (default 5 s): index = spawn order, pairs = idx*PAIRS_PER_JOB..., and the time with < 4 jobs running.
It hard-codes 16000 pairs per job in the printed range (change for 4000-pair jobs).

## pairs.py TRACE [min_ms] [n]   (hol-trace P lines, exp/hol-trace d94d683 or later)
Slow pairs with job idx, pair index (idx*16000+inJob, 16000 hard-coded), mates' trimmed lengths, longest run, distinct 4-mers, best period; writes TRACE.pairs.json.

Reference run (festive 64ae73f + f973b77 trace, 4 cores, 16000-pair jobs, inFlight 8): HiSeq 34M: map 1317 s, lean CPU 3110 s, util 0.59 (0.66 incl. gunzip), 25 jobs > 5 s, 658 s with < 4 jobs running.
