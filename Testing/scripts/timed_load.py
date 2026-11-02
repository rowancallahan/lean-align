#!/usr/bin/env python3
"""Run `lean-align map INDEX ...`; print wall, CPU (user / sys) and the index load measured inside the run: the time
until the process has read as many bytes as the index file holds (Main.lean reads the whole index before any FASTQ),
and the CPU used by then.   python3 timed_load.py LABEL CMD map INDEX ARGS..."""
import os, resource, subprocess, sys, time
t0 = time.monotonic()
size = os.path.getsize(sys.argv[4])
p = subprocess.Popen(sys.argv[2:])
load = lcpu = None
tck = os.sysconf('SC_CLK_TCK')
while p.poll() is None:
    try:
        with open(f'/proc/{p.pid}/io') as f: rchar = int(f.readline().split()[1])
        with open(f'/proc/{p.pid}/stat') as f: st = f.read().rsplit(')', 1)[1].split()
        if load is None and rchar >= size:
            load = time.monotonic() - t0; lcpu = (int(st[11]) + int(st[12])) / tck
    except (FileNotFoundError, ProcessLookupError, IndexError): pass
    time.sleep(0.005)
wall = time.monotonic() - t0
r = resource.getrusage(resource.RUSAGE_CHILDREN)
assert load is not None, 'never read the whole index'
print(f"TIME {sys.argv[1]}: wall {wall:.1f} s, cpu {r.ru_utime + r.ru_stime:.1f} s, user {r.ru_utime:.1f} s, sys {r.ru_stime:.1f} s, "
      f"load {load:.2f} s, loadcpu {lcpu:.2f} s, peak {r.ru_maxrss / 1e6:.2f} GB, exit {p.returncode}", flush=True)
sys.exit(p.returncode)
