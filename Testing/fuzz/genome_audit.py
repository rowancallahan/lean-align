#!/usr/bin/env python3
"""python3 -I genome_audit.py BIN WORK GENOME.fa [NPAIRS=20000] [modes=mason,low]
build time/size, then per mode: simulate pairs (Testing/benches/sim_pairs.py), map, report % proper (flag 2 on both),
% XU unique, % repetitiveUnknown, % both mates within 20 of the true start, seconds per 1000 pairs, peak RSS."""
import os, re, resource, subprocess, sys, time
bin_, work, fa = [os.path.abspath(x) for x in sys.argv[1:4]]; n = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
modes = (sys.argv[5] if len(sys.argv) > 5 else 'mason,low').split(','); os.makedirs(work, exist_ok=True)
name = os.path.basename(fa)[:-3]; idx = f'{work}/{name}.idx'
def timed(cmd):
    t = time.time(); pr = subprocess.Popen(cmd, stderr=subprocess.PIPE, text=True)
    err = pr.stderr.read(); _, st, ru = os.wait4(pr.pid, 0); pr.returncode = 0   # reaped here
    return os.waitstatus_to_exitcode(st), time.time() - t, ru.ru_maxrss / 1024, err
rc, t, mb, err = timed([bin_, 'build', fa, idx])
bases = sum(len(l) for l in open(fa) if l[0] != '>') - 0
print(f'{name}: {bases / 1e6:.1f} Mb  build rc={rc} {t:.1f}s peak {mb:.0f} MB  index {os.path.getsize(idx) / 1e6:.1f} MB = {os.path.getsize(idx) / bases:.2f} B/base' + ('' if rc == 0 else '\n' + err), flush=True)
if rc: sys.exit(1)
truth = lambda q: (lambda m: m and [(m[1], int(m[2]) + 1, m[3] == '-'), (m[1], int(m[4]) + 1, m[5] == '-')])(re.match(r's\d+:([^:]+):(\d+)-\d+([+-]):(\d+)-\d+([+-])', q))
for mode in modes:
    pre = f'{work}/{name}_{mode}'
    subprocess.run(['python3', '-I', 'Testing/benches/sim_pairs.py', os.environ.get('READS_FA', fa), pre, str(n), mode, '3'], check=True, capture_output=True)
    rc, t, mb, err = timed([bin_, 'map', idx, pre + '_R1.fq', pre + '_R2.fq', pre + '.sam', '100', '1000'])
    if rc: print(f'  {mode}: map rc={rc}\n{err}'); continue
    tot = prop = uniq = rep = at = degen = 0; cur = []
    for l in open(pre + '.sam'):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); f = int(r[1])
        if f & 0x900: continue
        cur.append((r, f))
        if len(cur) < 2: continue
        p = cur if cur[0][1] & 64 else cur[::-1]; cur = []; tot += 1
        if all(f & 2 for _, f in p): prop += 1
        tags = p[0][0][11:]
        uniq += 'XU:Z:unique' in tags; rep += 'XU:Z:repetitiveUnknown' in tags
        t_ = truth(p[0][0][0])
        if t_ and all(not f & 4 and r[2] == t_[i][0] and abs(int(r[3]) - t_[i][1]) <= 20 and bool(f & 16) == t_[i][2] for i, (r, f) in enumerate(p)): at += 1
    pc = lambda x: f'{100 * x / tot:5.1f}%'
    print(f'  {mode:6} pairs {tot}  proper {pc(prop)}  unique {pc(uniq)}  repetitiveUnknown {pc(rep)}  at truth {pc(at)}  map {t:.1f}s ({t * 1e6 / tot:.0f} ms per 1000 pairs, load incl.)  peak {mb:.0f} MB', flush=True)
