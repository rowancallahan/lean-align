#!/usr/bin/env python3
# samp.py NAME OUT : wait for a process whose comm starts with NAME; until it exits, sample per thread its CPU (user, sys),
# run-queue wait (schedstat) and context switches, the same for every zcat/cat/md5sum process, and the box's idle CPU.
import os, sys, time
name, out = sys.argv[1], sys.argv[2]; tck = os.sysconf("SC_CLK_TCK")
def comm(p):
    try: return open(f'/proc/{p}/comm').read().strip()
    except OSError: return ''
def idle():
    f = open('/proc/stat').readline().split()[1:]; return int(f[3]) + int(f[4]), sum(map(int, f[:8]))
pid = None
while pid is None:
    pid = next((int(p) for p in os.listdir('/proc') if p.isdigit() and comm(p).startswith(name)), None); time.sleep(0.01)
t0 = time.monotonic(); i0 = idle(); thr = {}; helpers = {}
def sample(p, tid):
    st = open(f'/proc/{p}/task/{tid}/stat').read().rsplit(')', 1)[1].split()
    ss = open(f'/proc/{p}/task/{tid}/schedstat').read().split()
    sw = [l.split()[1] for l in open(f'/proc/{p}/task/{tid}/status') if 'ctxt_switches' in l]
    return (int(st[11]) / tck, int(st[12]) / tck, int(ss[1]) / 1e9, int(sw[0]), int(sw[1]))
while os.path.exists(f'/proc/{pid}/task'):
    try:
        for tid in os.listdir(f'/proc/{pid}/task'): thr[int(tid)] = sample(pid, tid)
    except OSError: pass
    for p in os.listdir('/proc'):
        if p.isdigit() and comm(p) in ('zcat', 'gzip', 'cat', 'md5sum'):
            try: helpers[(comm(p), int(p))] = sample(p, p)
            except OSError: pass
    time.sleep(0.1)
w = time.monotonic() - t0; i1 = idle()
idle_frac = (i1[0] - i0[0]) / max(1, i1[1] - i0[1])
f = lambda k, v: f"{k}:{v[0]+v[1]:.1f}cpu/{v[1]:.1f}sys/{v[2]:.1f}rq/{v[3]}v/{v[4]}nv"
top = sorted(thr.items(), key=lambda x: -(x[1][0] + x[1][1]))[:6]
open(out, 'w').write(f"wall {w:.1f} box-idle {idle_frac:.2f}\n  threads " + " ".join(f(f'+{t-pid}', v) for t, v in top) +
                     "\n  helpers " + " ".join(f(c, v) for (c, p), v in sorted(helpers.items())) + "\n")
