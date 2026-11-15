#!/usr/bin/env python3
"""python3 -I cache_run.py CORES LABEL OUT.sam CMD ARGS...   (env is inherited)
Runs CMD pinned to CORES (e.g. 0 or 0-3), polls /proc/PID/smaps_rollup every 0.5 s, prints one TSV row:
LABEL  wall  user  sys  maxrss_GB  max_AnonHugePages_MB  md5(OUT.sam). Deletes OUT.sam afterwards."""
import hashlib, os, subprocess, sys, threading, time
cores, label, out = sys.argv[1:4]; cmd = sys.argv[4:]
lo, _, hi = cores.partition('-'); os.sched_setaffinity(0, set(range(int(lo), int(hi or lo) + 1)))
t0 = time.time(); p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); peak = [0]
def poll():
    while p.poll() is None:
        try: peak[0] = max(peak[0], max(int(l.split()[1]) for l in open(f'/proc/{p.pid}/smaps_rollup') if l.startswith('AnonHugePages')))
        except (FileNotFoundError, ProcessLookupError): pass
        time.sleep(0.5)
th = threading.Thread(target=poll); th.start()
_, st, ru = os.wait4(p.pid, 0); th.join(); wall = time.time() - t0
assert st == 0, st
print('\t'.join([label, f'{wall:.2f}', f'{ru.ru_utime:.2f}', f'{ru.ru_stime:.2f}', f'{ru.ru_maxrss / 1e6:.2f}', f'{peak[0] / 1024:.0f}',
                 hashlib.md5(open(out, 'rb').read()).hexdigest()]), flush=True)
os.remove(out)
