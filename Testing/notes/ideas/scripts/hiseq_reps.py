#!/usr/bin/env python3
"""python3 -I hiseq_reps.py KIND BIN INDEX OUTDIR [NLINES=40000000]    KIND = lean | mb
One streamed run on the first NLINES/4 pairs of GIAB HG002 HiSeq 2x250 D1_S1_L001_R{1,2}_001 (rangecat | gunzip | head -> FIFO), 4 threads, everything pinned to cores 0-3.
Index files are cat'ed into the page cache first (not timed). lean: SAM goes to a FIFO at OUT.tmp drained by `cat > /dev/null`; mb: stdout -> pipe -> `cat > /dev/null`.
Prints one TSV row: kind wall load aligner_cpu pipeline_cpu peak_rss lines1 lines2 (wall = launch to aligner exit; load = index read time)."""
import os, subprocess, sys, threading, time
kind, bin_, idx, out = sys.argv[1:5]; N = int(sys.argv[5]) if len(sys.argv) > 5 else 40000000
os.sched_setaffinity(0, {0, 1, 2, 3}); os.makedirs(out, exist_ok=True)
files = [idx] if kind == 'lean' else [idx + '.mbw', idx + '.l2b']
for f in files: subprocess.run(['cat', f], stdout=subprocess.DEVNULL, check=True)
isz = sum(os.path.getsize(f) for f in files)
G = 'https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads'
RC = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rangecat.py')
a, b = f'{out}/a', f'{out}/b'
for f in (a, b, f'{out}/o.tmp', f'{out}/o'):
    if os.path.exists(f): os.remove(f)
os.mkfifo(a); os.mkfifo(b)
def feeder(r, fifo):
    return ['bash', '-c', f'python3 -I {RC} {G}/D1_S1_L001_R{r}_001.fastq.gz | gunzip -c | head -n {N} | tee >(wc -l > {out}/lines{r}) > {fifo}']
P = {'feed1': subprocess.Popen(feeder(1, a), stderr=open(f'{out}/dl1.log', 'w')), 'feed2': subprocess.Popen(feeder(2, b), stderr=open(f'{out}/dl2.log', 'w'))}
if kind == 'lean':
    os.mkfifo(f'{out}/o.tmp'); P['sink'] = subprocess.Popen(['bash', '-c', f'cat < {out}/o.tmp > /dev/null'])
    t0 = time.time(); m = subprocess.Popen([bin_, 'map', idx, a, b, f'{out}/o', '100', '1000'], stderr=open(f'{out}/aligner.log', 'w'))
else:
    P['sink'] = subprocess.Popen(['bash', '-c', 'cat > /dev/null'], stdin=subprocess.PIPE)
    t0 = time.time(); m = subprocess.Popen([bin_, 'map', '-t', '4', idx, a, b], stdout=P['sink'].stdin, stderr=open(f'{out}/aligner.log', 'w'))
    P['sink'].stdin.close()
P['aligner'] = m
load = [None]
def sampler():   # lean: index load = until the process has read the whole index (rchar)
    while load[0] is None and m.poll() is None:
        try:
            r = int([l for l in open(f'/proc/{m.pid}/io') if l.startswith('rchar')][0].split()[1])
            if r >= isz: load[0] = time.time() - t0
        except FileNotFoundError: pass
        time.sleep(0.05)
if kind == 'lean': threading.Thread(target=sampler).start()
res = {}
def w(n, p): _, st, ru = os.wait4(p.pid, 0); res[n] = (st, time.time() - t0, ru)
th = [threading.Thread(target=w, args=(n, p)) for n, p in P.items()]
[t.start() for t in th]; [t.join() for t in th]
assert all(v[0] == 0 for v in res.values()), res
if kind == 'mb':
    load[0] = float([l for l in open(f'{out}/aligner.log') if 'index loaded' in l][0].split('::')[2].split('*')[0])
cpu = lambda ru: ru.ru_utime + ru.ru_stime
pipe = sum(cpu(res[n][2]) for n in res if n != 'aligner')
print('\t'.join(str(x) for x in [kind, f'{res["aligner"][1]:.1f}', f'{load[0]:.1f}', f'{cpu(res["aligner"][2]):.1f}', f'{pipe:.1f}',
      f'{res["aligner"][2].ru_maxrss / 1e6:.2f}', open(f'{out}/lines1').read().strip(), open(f'{out}/lines2').read().strip()]))
