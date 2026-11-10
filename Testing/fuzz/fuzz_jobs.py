#!/usr/bin/env python3
"""Many-jobs stress (jobPairs 16000): python3 -I fuzz_jobs.py WORK(g/all.fa, idx_new) REF_BIN BIN [BIN ...]
Input: >= 200k valid pairs (5 fuzz_reads sets of ~40k pairs, names prefixed per set). REF_BIN maps it once; each BIN maps it
5 times: exit 0, output byte-identical to REF_BIN's and to its own earlier runs, no OUT.tmp, no leftover process or zombie."""
import hashlib, os, subprocess, sys, time
work = os.path.abspath(sys.argv[1]); ref = os.path.abspath(sys.argv[2]); bins = [os.path.abspath(x) for x in sys.argv[3:]]
idx = f'{work}/idx_new'; f1, f2 = f'{work}/jobs1.fq', f'{work}/jobs2.fq'
if not os.path.exists(f2):
    with open(f1, 'wb') as o1, open(f2, 'wb') as o2:
        for s in range(5):
            subprocess.run(['python3', '-I', 'Testing/scripts/fuzz_reads.py', f'{work}/g/all.fa', f'{work}/jb', '2000', str(300 + s)], check=True, capture_output=True)
            for o, r in [(o1, 1), (o2, 2)]:
                L = open(f'{work}/jb_R{r}.fq', 'rb').read().split(b'\n')[:-1]
                for i in range(0, len(L), 4): L[i] = b'@j%d_' % s + L[i][1:]
                o.write(b'\n'.join(L) + b'\n')
pairs = sum(1 for _ in open(f1, 'rb')) // 4; assert pairs >= 200000, pairs
print(f'{pairs} pairs, {os.path.getsize(f1) / 1e6:.0f} MB per file', flush=True)
def leftovers(name):   # processes named like the binary, or any zombie
    ps = subprocess.run(['ps', '-eo', 'pid,stat,comm,args'], capture_output=True, text=True).stdout.splitlines()[1:]
    return [l for l in ps if (' Z' in l[:14] or os.path.basename(name)[:15] in l.split(None, 3)[2]) and 'ps -eo' not in l]
def mapit(b, out):
    if os.path.exists(out): os.remove(out)
    t = time.time(); r = subprocess.run([b, 'map', idx, f1, f2, out, '100', '1000'], capture_output=True)
    return r.returncode, hashlib.sha256(open(out, 'rb').read()).hexdigest() if os.path.exists(out) else None, os.path.exists(out + '.tmp'), time.time() - t, r.stderr
rc, want, _, t, _ = mapit(ref, f'{work}/jobs_ref.sam'); assert rc == 0; print(f'ref: {t:.0f}s', flush=True)
bad = 0
for b in bins:
    for k in range(5):
        rc, h, tmp, t, err = mapit(b, f'{work}/jobs_o.sam'); left = leftovers(b)
        ok = rc == 0 and h == want and not tmp and not left; bad += not ok
        print(('ok   ' if ok else 'FAIL ') + f'jobs: {os.path.basename(os.path.dirname(b))} run {k + 1}: exit {rc}, == ref {h == want}, tmp {tmp}, leftover {left}, {t:.0f}s {err[:100]}', flush=True)
sys.exit(1 if bad else 0)
