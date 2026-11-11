# Streamed NovaSeq runs (HG002 NovaSeq 30x, 2x151), ours vs minibwa, 4 threads

Method: R1 and R2 are fetched from the public GCS URL (scripts/wgrun2.py), `gunzip -c | head -n 4N | tee FIFO | awk` (awk counts exact pairs and bases),
into two FIFOs; the aligner runs under `taskset -c 0-3` (ours: `lean-align map ic.idx f1 f2 out.sam 100 1000`, output FIFO out.sam.tmp drained by `cat > /dev/null`,
or `md5sum` when MD5=1; minibwa: `map -t 4`, output /dev/null). result.json = rusage of the aligner (wait4) plus all children (producers, awk, sink).
threads.csv = aligner per-thread CPU ticks (t_s, tid, utime+stime, 100 ticks/s) every 10 s (runs from n10000000_ours_4ced on).
minibwa 20M/40M (dirs *_rf1) used scripts/retrycat.py (resuming Range downloader) because plain curl dropped the stream under backpressure: the plain-curl attempts
n20000000_minibwa (14.26M pairs) and an earlier one (17.24M, not kept) are INVALID short runs, kept only as evidence. n10000000_minibwa is plain curl, 10M complete.
Builds: f973b77 / 4ced426 (trace, NEVER MERGE), 6164113 (fix/fast), f465a57 (fix/fast); minibwa c07de5c. Index: ic.idx built by 027ef1e. Traces and SAMs are not included (large).
Dirs: *_ours = f973b77; *_ours_4ced = 4ced426 10M; n10000000_ours_fast = 6164113; *_ours_f465 = f465a57; *_minibwa_rf1 = minibwa with resuming downloader.
