"""Per-phase wall times of one mapper run.
usage: python3 phases.py LABEL INDEX_BYTES OUT_FILE HEADER_BYTES -- CMD...
load: until the process has read INDEX_BYTES (/proc/PID/io rchar); first: until OUT_FILE is larger than HEADER_BYTES
(the first chunk's SAM written); total: process exit. Prints user/sys CPU of the run too."""
import os, resource, subprocess, sys, time
lab, ib, out, hb = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
cmd = sys.argv[sys.argv.index('--') + 1:]
t0 = time.time()
p = subprocess.Popen(cmd)
load = first = None
while p.poll() is None:
    now = time.time() - t0
    if load is None:
        try:
            for l in open(f'/proc/{p.pid}/io'):
                if l.startswith('rchar') and int(l.split()[1]) >= ib: load = now
        except OSError:
            pass
    if first is None:
        try:
            if os.path.getsize(out) > hb: first = now
        except OSError:
            pass
    time.sleep(0.02)
tot = time.time() - t0
r = resource.getrusage(resource.RUSAGE_CHILDREN)
f = lambda x: 'n/a' if x is None else f'{x:.2f}'
print(f'PHASES {lab}: load {f(load)} s, first chunk out {f(first)} s, total {tot:.2f} s, map (total-load) '
      f'{f(None if load is None else tot - load)} s, user {r.ru_utime:.1f} s, sys {r.ru_stime:.1f} s, rc {p.returncode}', flush=True)
