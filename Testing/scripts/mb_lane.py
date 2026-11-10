#!/usr/bin/env python3
"""python3 -I mb_lane.py MINIBWA INDEX_PREFIX OUTDIR   Stream the whole GIAB HG002 HiSeq 2x250 lane D1_S1_L001 (17 files per mate) through
curl | gunzip into two FIFOs, run `minibwa map -t 4` on them, SAM to `md5sum` on a pipe (nothing on disk). All processes pinned to cores 0-3.
Counts the lines each mate stream delivers (wc -l on a tee), per-process rusage via wait4, wall, peak RSS. Prints one summary."""
import os, subprocess, sys, threading, time
mb, idx, out = sys.argv[1:4]
os.sched_setaffinity(0, {0, 1, 2, 3}); os.makedirs(out, exist_ok=True)
G = 'https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads'
a, b = f'{out}/a', f'{out}/b'
for f in (a, b):
    if os.path.exists(f): os.remove(f)
    os.mkfifo(f)
def feeder(r, fifo):   # pipefail: any failed curl / gunzip makes the stage exit non-zero
    urls = ' '.join(f'{G}/D1_S1_L001_R{r}_{i:03d}.fastq.gz' for i in range(1, 18))
    return ['bash', '-c', f'set -o pipefail; for u in {urls}; do curl -sSf "$u" | gunzip -c || exit 1; done | tee >(wc -l > {out}/lines{r}) > {fifo}']
P = {}
P['feed1'] = subprocess.Popen(feeder(1, a)); P['feed2'] = subprocess.Popen(feeder(2, b))
sink = subprocess.Popen(['bash', '-c', f'md5sum > {out}/sam.md5'], stdin=subprocess.PIPE)
t0 = time.time()
m = subprocess.Popen([mb, 'map', '-t', '4', idx, a, b], stdout=sink.stdin, stderr=open(f'{out}/mb.log', 'w'))
sink.stdin.close(); P['mb'] = m; P['sink'] = sink
res = {}
def w(n, p):
    _, st, ru = os.wait4(p.pid, 0); res[n] = (st, time.time() - t0, ru)
th = [threading.Thread(target=w, args=(n, p)) for n, p in P.items()]
[t.start() for t in th]; [t.join() for t in th]
for n, (st, t, ru) in res.items():
    print(f'{n}: exit {st}, ended at {t:.1f} s, user {ru.ru_utime:.1f} s, sys {ru.ru_stime:.1f} s, maxrss {ru.ru_maxrss / 1e6:.2f} GB')
wall = res['mb'][1]; ru = res['mb'][2]; cpu = ru.ru_utime + ru.ru_stime
print(f'minibwa wall {wall:.1f} s, cpu {cpu:.1f} s, cores {cpu / wall:.2f}')
print('lines R1', open(f'{out}/lines1').read().strip(), 'R2', open(f'{out}/lines2').read().strip(), 'md5', open(f'{out}/sam.md5').read().strip())
print('SUMMARY_DONE')
